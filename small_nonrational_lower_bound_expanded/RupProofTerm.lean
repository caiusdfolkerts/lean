module

public meta import Lean.Elab.Term
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.Tactic.AuxLemma
public meta import Std.Data.HashMap
public meta import Std.Data.HashSet

/-!
# Direct proof terms for RUP certificates

This elaborator is an untrusted proof producer.  Each reverse-unit-propagation
step becomes a small ordinary Lean theorem over a fresh abstract valuation
and only the clause hypotheses used by that step.  The final assembly is also
checked over an abstract valuation before it is applied to the user's model.

The elaborator neither asserts a checker result nor introduces an axiom.  It
does not use native decision procedures.  Every generated auxiliary theorem
passes through the ordinary kernel with synchronous checking enabled.

The accepted input is DIMACS CNF and the RUP-only fragment of text LRAT.
Deletion commands are ignored because previously proved clauses remain true.
RAT hints are rejected.  Clauses are represented by curried falsities: for
example `[i, -j]` means `(p i → False) → p j → False`.
-/

public meta section

namespace Papers.RationalityTen.RupProofTerm

open Lean Meta Elab Term

initialize registerTraceClass `RupProofTerm

private structure Timings where
  expressions : Nat := 0
  stepKernel : Nat := 0
  planning : Nat := 0
  finalClosure : Nat := 0
  finalKernel : Nat := 0
  deriving Inhabited

abbrev Clause := Array Int

structure Step where
  id : Nat
  clause : Clause
  hints : Array Nat
  deriving Inhabited

structure Unit where
  literal : Int
  hint : Nat
  deriving Inhabited

inductive Conflict where
  | clause (hint : Nat)
  | tautology (atomIndex : Nat)
  deriving Inhabited

structure Plan where
  used : Array Nat
  units : Array Unit
  conflict : Conflict
  deriving Inhabited

private def arrow (domain codomain : Expr) : Expr :=
  .forallE .anonymous domain codomain .default

private inductive Token where
  | number (value : Int)
  | word (value : String)
  | eof
  deriving Inhabited

/-- A one-pass ASCII scanner avoids allocating several strings for every
literal and hint in a large LRAT certificate. -/
private def nextToken (bytes : ByteArray) (start : Nat) : Except String (Token × Nat) := do
  let mut index := start
  while index < bytes.size && bytes[index]!.toNat ≤ 32 do
    index := index + 1
  if index == bytes.size then return (.eof, index)
  let first := bytes[index]!.toNat
  if first == 45 || (48 ≤ first && first ≤ 57) then
    let negative := first == 45
    if negative then index := index + 1
    let beginDigits := index
    let mut value := 0
    while index < bytes.size && 48 ≤ bytes[index]!.toNat && bytes[index]!.toNat ≤ 57 do
      value := 10 * value + (bytes[index]!.toNat - 48)
      index := index + 1
    if index == beginDigits || (index < bytes.size && bytes[index]!.toNat > 32) then
      throw s!"invalid integer at byte {start}"
    return (.number (if negative then -(Int.ofNat value) else Int.ofNat value), index)
  else
    let beginWord := index
    while index < bytes.size && bytes[index]!.toNat > 32 do
      index := index + 1
    return (.word (String.fromUTF8! (bytes.extract beginWord index)), index)

private def skipLine (bytes : ByteArray) (start : Nat) : Nat := Id.run do
  let mut index := start
  while index < bytes.size && bytes[index]! != 10 do
    index := index + 1
  return index

private def nextNumber (bytes : ByteArray) (start : Nat) : Except String (Int × Nat) := do
  let (token, next) ← nextToken bytes start
  match token with
  | .number value => return (value, next)
  | _ => throw s!"expected integer at byte {start}"

private def parseCnf (text : String) : Except String (Array Clause) := do
  let bytes := text.toUTF8
  let mut position := 0
  let mut clauses : Array Clause := #[]
  let mut pending : Clause := #[]
  let mut header : Option (Nat × Nat) := none
  while position < bytes.size do
    let (token, next) ← nextToken bytes position
    position := next
    match token with
    | .eof => break
    | .word "c" => position := skipLine bytes position
    | .word "p" =>
      let (.word "cnf", next) ← nextToken bytes position |
        throw "expected DIMACS 'cnf' header marker"
      let (variables, next) ← nextNumber bytes next
      let (count, next) ← nextNumber bytes next
      if variables < 0 || count < 0 || header.isSome then
        throw "expected one DIMACS 'p cnf variables clauses' header"
      header := some (variables.toNat, count.toNat)
      position := next
    | .word _ => throw "unexpected word in DIMACS clauses"
    | .number literal =>
      if literal == 0 then
        clauses := clauses.push pending
        pending := #[]
      else
        pending := pending.push literal
  let some (variables, count) := header | throw "missing DIMACS header"
  if !pending.isEmpty || clauses.size != count then
    throw "DIMACS clause count or terminating zero does not match the header"
  for clause in clauses do
    for literal in clause do
      if literal.natAbs > variables then throw "DIMACS literal exceeds the declared variable count"
  return clauses

private def parseLrat (text : String) : Except String (Array Step) := do
  let bytes := text.toUTF8
  let mut position := 0
  let mut steps := #[]
  while position < bytes.size do
    let (token, next) ← nextToken bytes position
    position := next
    if let .eof := token then break
    if let .word "c" := token then
      position := skipLine bytes position
      continue
    let .number rawId := token | throw "expected LRAT clause identifier"
    if rawId ≤ 0 then throw "LRAT clause identifiers must be positive"
    let id := rawId.toNat
    let (token, next) ← nextToken bytes position
    position := next
    if let .word "d" := token then
      position := skipLine bytes position
      continue
    let .number first := token | throw s!"LRAT step {id}: expected clause literal"
    let mut clause : Clause := #[]
    let mut hints : Array Nat := #[]
    let mut literal := first
    while literal != 0 do
      clause := clause.push literal
      let (nextLiteral, next) ← nextNumber bytes position
      literal := nextLiteral
      position := next
    let mut finished := false
    while !finished do
      let (value, next) ← nextNumber bytes position
      position := next
      if value == 0 then finished := true
      else if value < 0 then throw s!"LRAT step {id}: RAT hints are not supported"
      else hints := hints.push value.toNat
    steps := steps.push ⟨id, clause, hints⟩
  return steps

private def planStep (clauses : Std.HashMap Nat Clause) (step : Step) : Except String Plan := do
  if clauses.contains step.id then throw s!"LRAT step {step.id}: duplicate clause identifier"
  let mut known : Std.HashSet Int := {}
  for literal in step.clause do
    if known.contains literal then return ⟨#[], #[], .tautology literal.natAbs⟩
    known := known.insert (-literal)
  let mut used := #[]
  let mut units := #[]
  for hint in step.hints do
    let some clause := clauses[hint]? |
      throw s!"LRAT step {step.id}: unknown hint {hint}"
    if !used.contains hint then used := used.push hint
    let mut unknown : Option Int := none
    for literal in clause do
      if known.contains literal then
        throw s!"LRAT step {step.id}: hint {hint} is already satisfied"
      if !known.contains (-literal) then
        if let some other := unknown then
          if other != literal then
            throw s!"LRAT step {step.id}: hint {hint} has more than one unknown literal"
        unknown := some literal
    match unknown with
    | none => return ⟨used, units, .clause hint⟩
    | some literal =>
        units := units.push ⟨literal, hint⟩
        known := known.insert literal
  throw s!"LRAT step {step.id}: propagation does not end in a conflict"

private def atom (valuation : Expr) (atomIndex : Nat) : Expr :=
  mkApp valuation (mkNatLit atomIndex)

private def literalType (valuation : Expr) (literal : Int) : Expr :=
  let proposition := atom valuation literal.natAbs
  if literal > 0 then proposition else arrow proposition (mkConst ``False)

private def clauseType (valuation : Expr) (clause : Clause) : Expr :=
  clause.foldr (fun literal rest => arrow (literalType valuation (-literal)) rest)
    (mkConst ``False)

private def lookupProof (known : Std.HashMap Int Expr) (literal : Int) : MetaM Expr :=
  match known[literal]? with
  | some proof => pure proof
  | none => throwError "RUP proof construction lost literal {literal}"

private def hintProof (hypotheses : Std.HashMap Nat Expr) (hint : Nat) : MetaM Expr :=
  match hypotheses[hint]? with
  | some proof => pure proof
  | none => throwError "RUP proof construction lost clause {hint}"

private partial def buildUnits (valuation : Expr) (clauses : Std.HashMap Nat Clause)
    (hypotheses : Std.HashMap Nat Expr) (plan : Plan) (index : Nat)
    (known : Std.HashMap Int Expr) (lets : Array Expr) : MetaM Expr := do
  if index < plan.units.size then
    let unit := plan.units[index]!
    let clause := clauses[unit.hint]!
    let hypothesis ← hintProof hypotheses unit.hint
    let proof ← withLocalDeclD `hu (literalType valuation (-unit.literal)) fun hu => do
      let arguments ← clause.mapM fun literal =>
        if literal == unit.literal then pure hu else lookupProof known (-literal)
      let contradiction := mkAppN hypothesis arguments
      let implication ← mkLambdaFVars #[hu] contradiction
      if unit.literal > 0 then
        return mkApp2 (mkConst ``Classical.byContradiction)
          (atom valuation unit.literal.natAbs) implication
      else
        return implication
    withLetDecl (Name.mkSimple s!"u{index}") (literalType valuation unit.literal) proof fun fvar =>
      buildUnits valuation clauses hypotheses plan (index + 1)
        (known.insert unit.literal fvar) (lets.push fvar)
  else
    let contradiction ← match plan.conflict with
      | .tautology atomIndex => do
          let negative ← lookupProof known (-(Int.ofNat atomIndex))
          let positive ← lookupProof known (Int.ofNat atomIndex)
          pure (mkApp negative positive)
      | .clause hint => do
          let arguments ← clauses[hint]!.mapM fun literal => lookupProof known (-literal)
          let hypothesis ← hintProof hypotheses hint
          pure (mkAppN hypothesis arguments)
    mkLetFVars lets contradiction

/-- Build each propagation step in a fresh context, independently of the
actual geometric interpretation and of unrelated initial clauses. -/
private def buildStepLemma (clauses : Std.HashMap Nat Clause) (step : Step)
    (plan : Plan) (timings : IO.Ref Timings) (inlineSteps : Bool) : MetaM Expr := do
  let started ← IO.monoMsNow
  withLCtx {} #[] do
    withLocalDeclD `p (arrow (mkConst ``Nat) (mkSort .zero)) fun valuation => do
      let declarations := plan.used.map fun hint =>
        (Name.mkSimple s!"h{hint}", clauseType valuation clauses[hint]!)
      withLocalDeclsDND declarations fun assumptions => do
        let hypotheses := (plan.used.zip assumptions).foldl
          (fun table pair => table.insert pair.1 pair.2) ({} : Std.HashMap Nat Expr)
        let declarations := step.clause.mapIdx fun index literal =>
          (Name.mkSimple s!"a{index}", literalType valuation (-literal))
        let proof ← withLocalDeclsDND declarations fun falsities => do
          let known := (step.clause.zip falsities).foldl
            (fun table pair => table.insert (-pair.1) pair.2) ({} : Std.HashMap Int Expr)
          let body ← buildUnits valuation clauses hypotheses plan 0 known #[]
          mkLambdaFVars falsities body
        let binders := #[valuation] ++ assumptions
        let type ← mkForallFVars binders (clauseType valuation step.clause)
        let value ← mkLambdaFVars binders proof
        let checking ← IO.monoMsNow
        timings.modify fun state => { state with expressions := state.expressions + checking - started }
        if inlineSteps then return value
        let name ← withOptions (fun options => (Elab.async.set options false).setBool `debug.skipKernelTC false) do
          mkAuxLemma [] type value (kind? := some `_rup)
        let finished ← IO.monoMsNow
        timings.modify fun state => { state with stepKernel := state.stepKernel + finished - checking }
        return mkConst name

private partial def assemble (valuation : Expr) (steps : Array Step) (index : Nat)
    (clauses : Std.HashMap Nat Clause) (proofs : Std.HashMap Nat Expr)
    (lets : Array Expr) (last : Option Nat) (timings : IO.Ref Timings)
    (inlineSteps : Bool) : MetaM Expr := do
  if index < steps.size then
    let step := steps[index]!
    let started ← IO.monoMsNow
    let plan ← match planStep clauses step with
      | .ok plan => pure plan
      | .error message => throwError message
    let planned ← IO.monoMsNow
    timings.modify fun state => { state with planning := state.planning + planned - started }
    let lemma ← buildStepLemma clauses step plan timings inlineSteps
    let arguments ← plan.used.mapM fun hint => hintProof proofs hint
    let proof := mkAppN lemma (#[valuation] ++ arguments)
    withLetDecl (Name.mkSimple s!"r{step.id}") (clauseType valuation step.clause) proof fun fvar =>
      assemble valuation steps (index + 1) (clauses.insert step.id step.clause)
        (proofs.insert step.id fvar) (lets.push fvar) (some step.id) timings inlineSteps
  else
    let some last := last | throwError "RUP input contains no learned clause"
    if !clauses[last]!.isEmpty then throwError "RUP input does not end with the empty clause"
    let closing ← IO.monoMsNow
    let proof ← mkLetFVars lets (← hintProof proofs last)
    let finished ← IO.monoMsNow
    timings.modify fun state => { state with finalClosure := state.finalClosure + finished - closing }
    return proof

private def buildRefutation (initial : Array Clause) (steps : Array Step)
    (timings : IO.Ref Timings) (inlineSteps : Bool := false) : MetaM Expr :=
  withLCtx {} #[] do
    withLocalDeclD `p (arrow (mkConst ``Nat) (mkSort .zero)) fun valuation => do
      let declarations := initial.mapIdx fun index clause =>
        (Name.mkSimple s!"h{index + 1}", clauseType valuation clause)
      withLocalDeclsDND declarations fun assumptions => do
        let mut clauses : Std.HashMap Nat Clause := {}
        let mut proofs : Std.HashMap Nat Expr := {}
        for index in [:initial.size] do
          clauses := clauses.insert (index + 1) initial[index]!
          proofs := proofs.insert (index + 1) assumptions[index]!
        let body ← assemble valuation steps 0 clauses proofs #[] none timings inlineSteps
        let closing ← IO.monoMsNow
        let binders := #[valuation] ++ assumptions
        let type ← mkForallFVars binders (mkConst ``False)
        let value ← mkLambdaFVars binders body
        let checking ← IO.monoMsNow
        timings.modify fun state => { state with finalClosure := state.finalClosure + checking - closing }
        let name ← withOptions (fun options => (Elab.async.set options false).setBool `debug.skipKernelTC false) do
          mkAuxLemma [] type value (kind? := some `_rup_refutation)
        let finished ← IO.monoMsNow
        timings.modify fun state => { state with finalKernel := finished - checking }
        return mkConst name

/-- Build one ordinary abstract refutation theorem from untrusted RUP text.
When `inlineSteps` is true, propagation subproofs are let-bound inside that
single theorem rather than exported as one declaration per learned clause.
The entire resulting theorem is still checked by Lean's ordinary kernel. -/
def mkRefutationFromClauses (initial : Array Clause) (lrat : String)
    (inlineSteps : Bool := true) : MetaM Expr := do
  let started ← IO.monoMsNow
  let steps ← match parseLrat lrat with
    | .ok steps => pure steps
    | .error message => throwError message
  let parsed ← IO.monoMsNow
  let timings ← IO.mkRef ({} : Timings)
  let refutation ← buildRefutation initial steps timings inlineSteps
  let finished ← IO.monoMsNow
  let profile ← timings.get
  trace[RupProofTerm] "RUP milliseconds: parsing={parsed-started}, planning={profile.planning}, expressions={profile.expressions}, step kernel={profile.stepKernel}, final closure={profile.finalClosure}, final kernel={profile.finalKernel}, total={finished-started}; inline={inlineSteps}"
  return refutation

def mkRefutation (cnf lrat : String) (inlineSteps : Bool := true) : MetaM Expr := do
  let initial ← match parseCnf cnf with
    | .ok clauses => pure clauses
    | .error message => throwError message
  mkRefutationFromClauses initial lrat inlineSteps

syntax (name := rupProof) "rup_proof% " term:max " #[" term,* "] " str str : term

@[term_elab rupProof] def elaborateRupProof : TermElab := fun stx _ => do
  let started ← IO.monoMsNow
  let `(rup_proof% $valuation #[$hypotheses,*] $cnf:str $lrat:str) := stx |
    throwErrorAt stx "malformed rup_proof% term"
  let initial ← match parseCnf cnf.getString with
    | .ok clauses => pure clauses
    | .error message => throwErrorAt cnf message
  let steps ← match parseLrat lrat.getString with
    | .ok steps => pure steps
    | .error message => throwErrorAt lrat message
  let proofSyntax := hypotheses.getElems
  if proofSyntax.size != initial.size then
    throwErrorAt stx "expected {initial.size} initial clause proofs, got {proofSyntax.size}"
  let parsed ← IO.monoMsNow
  let valuation ← elabTermEnsuringType valuation (arrow (mkConst ``Nat) (mkSort .zero))
  let mut initialProofs := #[]
  for index in [:initial.size] do
    initialProofs := initialProofs.push
      (← elabTermEnsuringType proofSyntax[index]! (clauseType valuation initial[index]!))
  let elaborated ← IO.monoMsNow
  let timings ← IO.mkRef ({} : Timings)
  let refutation ← buildRefutation initial steps timings
  let finished ← IO.monoMsNow
  let profile ← timings.get
  trace[RupProofTerm] "RUP milliseconds: parsing={parsed - started}, initial proofs={elaborated - parsed}, planning={profile.planning}, expressions={profile.expressions}, step kernel={profile.stepKernel}, final closure={profile.finalClosure}, final kernel={profile.finalKernel}, total={finished - started}"
  return mkAppN refutation (#[valuation] ++ initialProofs)

end Papers.RationalityTen.RupProofTerm
