module

public meta import Lean.Elab.Command
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.Tactic.AuxLemma
public meta import RupProofTerm

/-!
# Direct proof terms for geometric SAT input clauses

The JSON input to this command is an untrusted description of which proved
geometric and counting rules to apply.  It is not a trusted certificate.
The command builds ordinary proof expressions and submits every resulting
theorem to Lean's kernel with synchronous checking enabled.  Incorrect input
therefore fails to produce the stated theorem.

Building expressions directly avoids repeatedly elaborating the large closed
semantic table at each initial-clause argument.  The public theorem statements
still use that table, and the kernel checks every conversion to its meaning.
-/

public meta section

namespace Papers.RationalityTen.FacetSatInitials

open Lean Meta Elab Command

initialize registerTraceClass `FacetSatInitials

private def arrow (a b : Expr) : Expr := .forallE .anonymous a b .default
private def falseExpr : Expr := mkConst ``False
private def natExpr : Expr := mkConst ``Nat
private def natFn : Expr := arrow natExpr natExpr

private def fromExcept (value : Except String α) : MetaM α :=
  match value with
  | .ok a => pure a
  | .error message => throwError "facet_initials%: {message}"

private def field (json : Json) (key : String) : MetaM Json :=
  fromExcept (json.getObjVal? key)
private def natField (json : Json) (key : String) : MetaM Nat := do
  fromExcept ((← field json key).getNat?)
private def strField (json : Json) (key : String) : MetaM String := do
  fromExcept ((← field json key).getStr?)
private def arrayField (json : Json) (key : String) : MetaM (Array Json) := do
  fromExcept ((← field json key).getArr?)
private def boolFieldD (json : Json) (key : String) (fallback : Bool) : Bool :=
  ((json.getObjVal? key).toOption.bind (fun value => value.getBool?.toOption)).getD fallback
private def natArray (json : Json) : MetaM (Array Nat) := do
  (← fromExcept json.getArr?).mapM (fun value => fromExcept value.getNat?)
private def intArray (json : Json) : MetaM (Array Int) := do
  (← fromExcept json.getArr?).mapM (fun value => fromExcept value.getInt?)

private def parseName (text : String) : Name :=
  (text.splitOn ".").foldl Name.str .anonymous

private def padded (width value : Nat) : String :=
  let digits := toString value
  String.ofList (List.replicate (width - digits.length) '0') ++ digits

private structure Globals where
  ns : Name
  data : Expr
  n : Expr
  α : Expr
  listType : Expr
  selectedTemplate : Expr
  decidableTemplate : Expr
  equalityTemplate : Expr
  inlineFacts : Bool
  factCache : IO.Ref (PHashMap Expr Expr)
  kind : Expr
  relation : Expr
  ridges : Expr
  rows : Expr
  requirements : Expr
  manifest : Json
  atoms : Array Json
  atomEquations : Array (Option (Expr × Expr))
  groupTemplates : Std.HashMap Nat (Expr × Expr)
  lower : Bool
  coverage : Bool
  edgeCoverEnabled : Bool

private def Globals.named (g : Globals) (name : String) : Expr :=
  mkConst (Name.str g.ns name)

private def Globals.facet (g : Globals) (index : Nat) : Expr :=
  mkApp (g.named "facetIndex") (mkNatLit index)

private def Globals.ridge (g : Globals) (index : Nat) : Expr :=
  mkApp (g.named "ridgeIndex") (mkNatLit index)

private def Globals.facetList (g : Globals) (values : Array Nat) : Expr :=
  values.foldr (fun value tail => mkApp3 (mkConst ``List.cons [.zero]) g.α (g.facet value) tail)
    (mkApp (mkConst ``List.nil [.zero]) g.α)

private def Globals.model (g : Globals) (selected : Expr) (index : Nat) : Expr :=
  mkApp2 (g.named "model") selected (mkNatLit index)

private def Globals.falsity (g : Globals) (selected : Expr) (literal : Int) : Expr :=
  let atom := g.model selected literal.natAbs
  if literal > 0 then arrow atom falseExpr else atom

private def eqExpr (α a b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [.succ .zero]) α a b

private def natLt (a b : Expr) : Expr :=
  mkAppN (mkConst ``LT.lt [.zero]) #[natExpr, mkConst ``instLTNat, a, b]
private def natLe (a b : Expr) : Expr := mkApp2 (mkConst ``Nat.le) a b

/-- The equality proof is checked by the kernel; this producer never evaluates
the proposition in native code or treats a Boolean result as evidence. -/
private def closedDecide (g : Globals) (target : Expr) : MetaM Expr := do
  if g.inlineFacts then
    if let some proof := (← g.factCache.get).find? target then return proof
  let env ← getEnv
  let key : AuxLemmaKey := {type := target, isPrivate := !env.isExporting, defeq := false}
  if !g.inlineFacts then
    if let some (name, []) := (auxLemmasExt.getState env).lemmas.find? key then
      return mkConst name
  let inst ← if target.isForall && target.bindingBody! == falseExpr &&
      target.bindingDomain!.isAppOfArity ``Eq 3 then do
    let equality := target.bindingDomain!
    let arguments := equality.getAppArgs
    let equalityInst := mkApp2 g.equalityTemplate arguments[1]! arguments[2]!
    pure (mkApp2 (mkConst ``instDecidableNot) equality equalityInst)
  else if target.isAppOfArity ``Eq 3 && target.getAppArgs[0]! == mkConst ``Bool then
    pure (mkApp2 (mkConst ``Bool.decEq) target.getAppArgs[1]! target.getAppArgs[2]!)
  else if target.isAppOfArity ``LT.lt 4 && target.getAppArgs[0]! == natExpr then
    pure (mkApp2 (mkConst ``Nat.decLt) target.getAppArgs[2]! target.getAppArgs[3]!)
  else if target.isAppOfArity ``Membership.mem 5 then
    pure (mkApp (g.decidableTemplate.instantiate1 target.getAppArgs[3]!) target.getAppArgs[4]!)
  else synthInstance (mkApp (mkConst ``Decidable) target)
  let refl := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Bool) (mkConst ``Bool.true)
  let value := mkApp3 (mkConst ``of_decide_eq_true) target inst refl
  if g.inlineFacts then
    g.factCache.modify fun cache => cache.insert target value
    return value
  let name ← mkAuxLemma [] target value (kind? := some `_facet_fact)
  return mkConst name

private structure Context where
  g : Globals
  selectedList : Expr
  quota : Expr
  boundary : Expr
  budget : Option Expr
  noSame : Option Expr
  edgeCover : Option Expr
  selected : Expr
  selectedDecidable : Expr
  counterType : Expr
  groupKey : Option Nat := none
  clause : Array Int
  hypotheses : Array Expr

private def Context.boundaryArgs (c : Context) : Array Expr :=
  #[c.g.n, mkNatLit 1024, c.g.kind, c.g.relation, c.g.ridges, c.quota,
    c.selectedList, c.boundary]

private def Context.counterArgs (c : Context) : Array Expr :=
  #[c.counterType, c.selected, c.selectedDecidable]

private def Context.groupCounter (c : Context) (key : Nat) : MetaM Context := do
  let some (selected, decidable) := c.g.groupTemplates[key]? |
    throwError "facet_initials%: missing grouping for kind {key}"
  return {c with
    selected := selected.instantiate1 c.selectedList,
    selectedDecidable := decidable.instantiate1 c.selectedList,
    counterType := natExpr, groupKey := some key}

private def Context.hyp (c : Context) (literal : Int) : MetaM Expr := do
  for index in [:c.clause.size] do
    if c.clause[index]! == literal then return c.hypotheses[index]!
  throwError "facet_initials%: rule refers to missing literal {literal}"

private def Context.counter (c : Context) (name : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst name) (c.counterArgs ++ args)

private def Context.boundaryRule (c : Context) (name : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst name) (c.boundaryArgs ++ args)

private def reached (c : Context) (vertices : Expr) (threshold : Nat) : Expr :=
  c.counter `Papers.RationalityTen.SequentialCounter.reached #[vertices, mkNatLit threshold]

private def listLength (c : Context) (vertices : Expr) : Expr :=
  mkApp2 (mkConst ``List.length [.zero]) c.counterType vertices

private def emptyNotReached (c : Context) (threshold : Nat) : MetaM Expr := do
  let hpositive ← closedDecide c.g (natLt (mkNatLit 0) (mkNatLit threshold))
  return c.counter `Papers.RationalityTen.SequentialCounter.not_reached_empty #[mkNatLit threshold, hpositive]

private def reachedArgument (c : Context) (vertices : Array Nat) (listExpr : Expr)
    (threshold : Nat) (literal : Json) (negative : Bool) : MetaM Expr := do
  if let .bool value := literal then
    if value then throwError "facet_initials%: tautological merge clause"
    if negative then
      let hlarge ← closedDecide c.g (natLt (listLength c listExpr) (mkNatLit threshold))
      return c.counter `Papers.RationalityTen.SequentialCounter.not_reached_above_length
        #[listExpr, mkNatLit threshold, hlarge]
    if threshold != 0 then throwError "facet_initials%: invalid zero-threshold constant"
    return c.counter `Papers.RationalityTen.SequentialCounter.reached_zero #[listExpr]
  let lit ← fromExcept literal.getInt?
  let hypothesis ← c.hyp lit
  if lit == 0 || lit.natAbs > c.g.atoms.size then
    throwError "facet_initials%: atom index out of bounds"
  let atom := c.g.atoms[lit.natAbs - 1]!
  let tag ← strField atom "tag"
  let isLeaf := if c.groupKey.isSome then tag == "group" else tag == "facet"
  if !isLeaf then return hypothesis
  let index ← natField atom "index"
  if vertices != #[index] || threshold != 1 then
    throwError "facet_initials%: totalizer leaf does not match its facet atom"
  if let some key := c.groupKey then
    if (← natField atom "kind") != key then
      throwError "facet_initials%: grouped totalizer leaf has the wrong kind"
  let vertex := if c.groupKey.isSome then mkNatLit index else c.g.facet index
  if !negative then
    return c.counter `Papers.RationalityTen.SequentialCounter.leaf_lower #[vertex, hypothesis]
  withLocalDeclD `hx (reached c listExpr 1) fun hx => do
    mkLambdaFVars #[hx] (mkApp hypothesis (c.counter `Papers.RationalityTen.SequentialCounter.leaf_upper #[vertex, hx]))

private def allMemberships (c : Context) (vertices : Array Nat)
    (hypotheses : Array Expr) (negative : Bool) : MetaM Expr := do
  if vertices.size != hypotheses.size then
    throwError "facet_initials%: membership clause has the wrong length"
  let nilName := if negative then `Papers.RationalityTen.FacetSat.not_mem_nil else `Papers.RationalityTen.FacetSat.all_mem_nil
  let consName := if negative then `Papers.RationalityTen.FacetSat.not_mem_cons else `Papers.RationalityTen.FacetSat.all_mem_cons
  let mut value := mkApp2 (mkConst nilName) c.g.n c.selected
  let mut tail := c.g.facetList #[]
  for offset in [:vertices.size] do
    let index := vertices.size - 1 - offset
    let vertex := c.g.facet vertices[index]!
    value := mkAppN (mkConst consName) #[c.g.n, c.selected, vertex, tail,
      hypotheses[index]!, value]
    tail := mkApp3 (mkConst ``List.cons [.zero]) c.g.α vertex tail
  return value

/-- Opaque atom equations stop subsequent clause proofs from reopening the
semantic lookup table.  Their proofs are ordinary kernel-checked equalities. -/
private def semanticHypothesis (g : Globals) (selectedList : Expr)
    (literal : Int) (hypothesis : Expr) : MetaM Expr := do
  let some (theoremExpr, body) := g.atomEquations[literal.natAbs - 1]! |
    return hypothesis
  let equalityType := body.instantiate1 selectedList
  if !equalityType.isAppOfArity ``Eq 3 then
    throwError "facet_initials%: atom equation does not state an equality"
  let arguments := equalityType.getAppArgs
  let left := arguments[1]!
  let right := arguments[2]!
  let equality := mkApp theoremExpr selectedList
  if literal < 0 then
    return mkAppN (mkConst ``Eq.mp [.zero]) #[left, right, equality, hypothesis]
  withLocalDeclD `semantic right fun value => do
    let converted := mkAppN (mkConst ``Eq.mpr [.zero]) #[left, right, equality, value]
    mkLambdaFVars #[value] (mkApp hypothesis converted)

private def buildRule (c : Context) (rule : Json) : MetaM Expr := do
  let tag ← strField rule "tag"
  match tag with
  | "incompatible" =>
    let a := c.g.facet (← natField rule "a")
    let b := c.g.facet (← natField rule "b")
    let hne ← closedDecide c.g (arrow (eqExpr c.g.α a b) falseExpr)
    let hbad ← closedDecide c.g (eqExpr (mkConst ``Bool)
      (mkApp2 c.g.relation a b) (mkConst ``Bool.false))
    return c.boundaryRule `Papers.RationalityTen.FacetSat.Boundary.incompatible (#[a, b, hne, hbad] ++ c.hypotheses)
  | "three" =>
    let vertices ← natArray (← field rule "vertices")
    if vertices.size != 3 then throwError "facet_initials%: three-facet clause needs three vertices"
    let q ← natField rule "ridge"
    let a := c.g.facet vertices[0]!
    let b := c.g.facet vertices[1]!
    let d := c.g.facet vertices[2]!
    let hab ← closedDecide c.g (arrow (eqExpr c.g.α a b) falseExpr)
    let had ← closedDecide c.g (arrow (eqExpr c.g.α a d) falseExpr)
    let hbd ← closedDecide c.g (arrow (eqExpr c.g.α b d) falseExpr)
    let facts := vertices.map (fun v => c.g.named s!"ridge_{v}_{q}")
    return c.boundaryRule `Papers.RationalityTen.FacetSat.Boundary.three
      (#[c.g.ridge q, a, b, d, hab, had, hbd] ++ facts ++ c.hypotheses)
  | "mate" =>
    let a ← natField rule "a"
    let q ← natField rule "ridge"
    let owners ← natArray (← field rule "owners")
    if c.hypotheses.size != owners.size + 1 then
      throwError "facet_initials%: mate clause has the wrong length"
    let allFalse ← allMemberships c owners (c.hypotheses.extract 1 c.hypotheses.size) true
    let rowsExact := mkApp2 (mkConst `Papers.RationalityTen.FacetSat.Data.ridgeRows_exact)
      c.g.data (c.g.named "ridge_matrix_checked")
    return c.boundaryRule `Papers.RationalityTen.FacetSat.Boundary.packed_mate
      #[c.g.rows, rowsExact, c.g.ridge q, c.g.facet a,
        c.g.named s!"owners_{a}_{q}", c.g.named s!"dropped_{a}_{q}",
        c.g.named s!"ridge_{a}_{q}", c.g.named s!"owners_{a}_{q}_checked",
        c.hypotheses[0]!, allFalse]
  | "group_take" =>
    let key ← natField rule "kind"
    let index ← natField rule "index"
    let member ← natField rule "member"
    let grouping := c.g.named s!"grouping{key}"
    let members := mkAppN (mkConst `Papers.RationalityTen.FacetSat.Grouping.members)
      #[c.g.n, grouping, mkNatLit index]
    let vertex := c.g.facet member
    let membership := mkApp (mkConst ``List.instMembership [.zero]) c.g.α
    let hmember ← closedDecide c.g (mkAppN (mkConst ``Membership.mem [.zero, .zero])
      #[c.g.α, c.g.listType, membership, members, vertex])
    return mkAppN (mkConst `Papers.RationalityTen.FacetSat.Grouping.group_take)
      (#[c.g.n, grouping, c.selectedList, mkNatLit index, vertex, hmember] ++ c.hypotheses)
  | "group_or" =>
    let key ← natField rule "kind"
    let index ← natField rule "index"
    let members ← natArray (← field rule "members")
    if c.hypotheses.size != members.size + 1 then
      throwError "facet_initials%: group disjunction has the wrong number of literals"
    let allFalse ← allMemberships c members (c.hypotheses.extract 1 c.hypotheses.size) true
    return mkAppN (mkConst `Papers.RationalityTen.FacetSat.Grouping.group_or)
      #[c.g.n, c.g.named s!"grouping{key}", c.selectedList, mkNatLit index,
        c.hypotheses[0]!, allFalse]
  | "edge" =>
    let some edgeCover := c.edgeCover |
      throwError "facet_initials%: edge clause is missing its graph-cover assumption"
    let edge ← natField rule "edge"
    let owners ← natArray (← field rule "owners")
    let allFalse ← allMemberships c owners c.hypotheses true
    return mkAppN (mkConst `Papers.RationalityTen.FacetSat.EdgeCover.clause)
      #[c.g.n, c.g.named "edgeCount", c.g.named "requiredEdges", c.g.named "edgeRows",
        c.selectedList, edgeCover, mkApp (c.g.named "edgeIndex") (mkNatLit edge),
        c.g.named s!"edgeOwners_{edge}", c.g.named s!"edge_{edge}_required",
        c.g.named s!"edge_{edge}_owners_checked", allFalse]
  | "counter" =>
    let key ← natField rule "kind"
    let c ← if boolFieldD rule "grouped" false then c.groupCounter key else pure c
    let position ← natField rule "position"
    let threshold ← natField rule "threshold"
    let gate ← strField rule "gate"
    let theoremName ← match gate with
      | "carry" => pure `Papers.RationalityTen.SequentialCounter.prefix_carry
      | "take" => pure `Papers.RationalityTen.SequentialCounter.prefix_take
      | "previous_or_selected" => pure `Papers.RationalityTen.SequentialCounter.prefix_previous_or_selected
      | "previous_or_lower" => pure `Papers.RationalityTen.SequentialCounter.prefix_previous_or_lower
      | _ => throwError "facet_initials%: unknown sequential-counter gate"
    let vertices := c.g.named (if c.groupKey.isSome then s!"groupKind{key}" else s!"kind{key}")
    let prefixList := mkApp3 (mkConst ``List.take [.zero]) c.counterType (mkNatLit position) vertices
    let hindex ← closedDecide c.g (natLt (mkNatLit position) (listLength c vertices))
    let hpositive ← closedDecide c.g (natLt (mkNatLit 0) (mkNatLit threshold))
    let literals ← arrayField rule "full_literals"
    let mut arguments := #[]
    for index in [:literals.size] do
      let literal := literals[index]!
      if let .bool value := literal then
        if value then throwError "facet_initials%: tautological counter clause"
        if gate == "take" && index == 1 && threshold == 1 then
          arguments := arguments.push (c.counter `Papers.RationalityTen.SequentialCounter.reached_zero #[prefixList])
        else if (gate == "previous_or_selected" || gate == "previous_or_lower") &&
            position == 0 && (index == 1 || index == 2) then
          let bound := if index == 1 then threshold else threshold - 1
          arguments := arguments.push (← emptyNotReached c bound)
        else throwError "facet_initials%: unsupported reduced counter literal"
      else arguments := arguments.push (← c.hyp (← fromExcept literal.getInt?))
    return c.counter theoremName
      (#[vertices, mkNatLit position, mkNatLit threshold, hindex, hpositive] ++ arguments)
  | "merge" =>
    let c ← if boolFieldD rule "grouped" false then
      c.groupCounter (← natField rule "kind") else pure c
    let left ← natArray (← field rule "left")
    let right ← natArray (← field rule "right")
    let a ← natField rule "a"
    let b ← natField rule "b"
    let leftExpr := c.g.named (← strField rule "left_name")
    let rightExpr := c.g.named (← strField rule "right_name")
    let joinedExpr := c.g.named (← strField rule "joined_name")
    let literals ← arrayField rule "full_literals"
    if literals.size != 3 then throwError "facet_initials%: merge clause needs three literals"
    let direction ← strField rule "direction"
    let (theoremName, arguments) ← if direction == "forward" then do
      let x ← reachedArgument c left leftExpr a literals[0]! false
      let y ← reachedArgument c right rightExpr b literals[1]! false
      let z ← reachedArgument c (left ++ right) joinedExpr (a+b) literals[2]! true
      pure (`Papers.RationalityTen.SequentialCounter.merge_forward, #[x, y, z])
    else if direction == "backward" then do
      let x ← reachedArgument c (left ++ right) joinedExpr (a+b+1) literals[0]! false
      let y ← reachedArgument c left leftExpr (a+1) literals[1]! true
      let z ← reachedArgument c right rightExpr (b+1) literals[2]! true
      pure (`Papers.RationalityTen.SequentialCounter.merge_backward, #[x, y, z])
    else throwError "facet_initials%: unknown merge direction"
    return c.counter theoremName (#[leftExpr, rightExpr, mkNatLit a, mkNatLit b] ++ arguments)
  | "quota_lower" | "quota_upper" =>
    let key ← natField rule "kind"
    let c ← if boolFieldD rule "grouped" false then c.groupCounter key else pure c
    let quota ← natField rule "quota"
    let vertices := c.g.named (if c.groupKey.isSome then s!"groupKind{key}" else s!"kind{key}")
    let count := if c.groupKey.isSome then
      c.boundaryRule `Papers.RationalityTen.FacetSat.Boundary.group_count
        #[c.g.named s!"grouping{key}", mkNatLit key, c.g.named s!"grouping{key}_checked"]
    else c.boundaryRule `Papers.RationalityTen.FacetSat.Boundary.quota_count
      #[mkNatLit key, vertices, c.g.named s!"kind{key}_checked"]
    let (theoremName, bound) ← if c.g.lower then do
      if tag != "quota_lower" then throwError "facet_initials%: upper quota in lower-only certificate"
      let some budget := c.budget | throwError "facet_initials%: missing lower-quota context"
      let actual := mkApp c.quota (mkNatLit key)
      let required := mkApp c.g.requirements (mkNatLit key)
      let selectedCount := c.counter `Papers.RationalityTen.SequentialCounter.selectedCount #[vertices]
      let equality := mkAppN (mkConst ``Eq.symm [.succ .zero]) #[natExpr, selectedCount, actual, count]
      let upper := mkAppN (mkConst ``Nat.le_of_eq) #[actual, selectedCount, equality]
      let bound := mkAppN (mkConst ``Nat.le_trans)
        #[required, actual, selectedCount, mkApp budget (mkNatLit key), upper]
      pure (`Papers.RationalityTen.SequentialCounter.quota_lower_of_le, bound)
    else pure ((if tag == "quota_lower" then `Papers.RationalityTen.SequentialCounter.quota_lower else `Papers.RationalityTen.SequentialCounter.quota_upper), count)
    let fn := c.counter theoremName #[vertices, mkNatLit quota, bound]
    if c.hypotheses.size == 1 then
      let literal := c.clause[0]!
      let atom := c.g.atoms[literal.natAbs - 1]!
      let atomTag ← strField atom "tag"
      let indices ← if atomTag == "facet" || atomTag == "group" then
        pure #[← natField atom "index"] else pure #[]
      let threshold := if tag == "quota_lower" then quota else quota+1
      let argument ← reachedArgument c indices vertices threshold (toJson literal)
        (tag == "quota_lower")
      return mkApp fn argument
    if !c.hypotheses.isEmpty || tag != "quota_lower" then
      throwError "facet_initials%: quota clause has the wrong length"
    let hlarge ← closedDecide c.g (natLt (listLength c vertices) (mkNatLit quota))
    return mkApp fn (c.counter `Papers.RationalityTen.SequentialCounter.not_reached_above_length
      #[vertices, mkNatLit quota, hlarge])
  | "block" =>
    if c.g.lower then throwError "facet_initials%: leaf blocking requires exact quotas"
    let some noSame := c.noSame | throwError "facet_initials%: missing leaf-coverage context"
    let index ← natField rule "leaf"
    let vertices ← natArray (← field rule "vertices")
    let allSelected ← allMemberships c vertices c.hypotheses false
    let leafCount := c.g.named "leafCount"
    let hindex ← closedDecide c.g (natLt (mkNatLit index) leafCount)
    let leafIndex := mkApp3 (mkConst ``Fin.mk) leafCount (mkNatLit index) hindex
    let name := "leaf" ++ padded 4 index
    return c.boundaryRule `Papers.RationalityTen.FacetSat.Boundary.block_leaf_checked
      #[c.g.named name, c.g.named (name ++ "_checked"), mkApp noSame leafIndex, allSelected]
  | _ => throwError "facet_initials%: unknown initial-clause rule {tag}"

private def boundaryType (g : Globals) (quota selected : Expr) : Expr :=
  mkAppN (mkConst `Papers.RationalityTen.FacetSat.Boundary)
    #[g.n, mkNatLit 1024, g.kind, g.relation, g.ridges, quota, selected]

private def noSameType (g : Globals) (selected : Expr) : MetaM Expr := do
  let leafCount := g.named "leafCount"
  withLocalDeclD `j (mkApp (mkConst ``Fin) leafCount) fun j => do
    let leaf := mkApp (g.named "leaves") j
    let familyLeaf := mkApp2 (mkConst `Papers.RationalityTen.SparseGrowthDAG.family) g.n leaf
    let familySelected := mkApp2 (mkConst `Papers.RationalityTen.SparseGrowthDAG.family) g.n selected
    let same := mkApp3 (mkConst `Papers.RationalityTen.GrowthDAG.Same) g.n familyLeaf familySelected
    mkForallFVars #[j] (arrow same falseExpr)

private def edgeCoverType (g : Globals) (selected : Expr) : Expr :=
  mkAppN (mkConst `Papers.RationalityTen.FacetSat.EdgeCover)
    #[g.n, g.named "edgeCount", g.named "requiredEdges", g.named "edgeRows", selected]

private def withBoundaryContext (g : Globals)
    (action : Context → Array Expr → MetaM β) : MetaM β :=
  withLCtx {} #[] do
    withLocalDeclD `S g.listType fun selectedList => do
      let withQuota (quota : Expr) (context : Array Expr) := do
        withLocalDeclD `H (boundaryType g quota selectedList) fun boundary => do
          let withBudget (budget : Option Expr) (context : Array Expr) := do
            let withEdgeCover (edgeCover : Option Expr) (context : Array Expr) := do
              let withNoSame (noSame : Option Expr) (context : Array Expr) := do
                let selected := g.selectedTemplate.instantiate1 selectedList
                let selectedDecidable := g.decidableTemplate.instantiate1 selectedList
                let c : Context := {
                  g, selectedList, quota, boundary, budget, noSame, edgeCover,
                  selected, selectedDecidable, counterType := g.α,
                  clause := #[], hypotheses := #[] }
                action c context
              if g.coverage then
                withLocalDeclD `noSame (← noSameType g selectedList) fun noSame =>
                  withNoSame (some noSame) (context.push noSame)
              else withNoSame none context
            if g.edgeCoverEnabled then
              withLocalDeclD `edgeCover (edgeCoverType g selectedList) fun edgeCover =>
                withEdgeCover (some edgeCover) (context.push edgeCover)
            else withEdgeCover none context
          if g.lower then
            let budgetType ← withLocalDeclD `j natExpr fun j =>
              mkForallFVars #[j] (natLe (mkApp g.requirements j) (mkApp quota j))
            withLocalDeclD `hbudget budgetType fun budget =>
              withBudget (some budget) (context.push boundary |>.push budget)
          else withBudget none (context.push boundary)
      if g.lower then
        withLocalDeclD `actualQuota natFn fun quota =>
          withQuota quota #[selectedList, quota]
      else withQuota g.requirements #[selectedList]

private def buildClause (base : Context) (clause : Array Int) (rule : Json) : MetaM Expr := do
  let bindings := clause.mapIdx fun index literal =>
    (Name.str .anonymous s!"h{index}", base.g.falsity base.selectedList literal)
  withLocalDeclsDND bindings fun hypotheses => do
    let semanticHypotheses ← hypotheses.mapIdxM fun index hypothesis =>
      semanticHypothesis base.g base.selectedList clause[index]! hypothesis
    let proof ← buildRule {base with clause, hypotheses := semanticHypotheses} rule
    mkLambdaFVars hypotheses proof

private def buildInitial (g : Globals) (number : Nat) (clause : Array Int)
    (rule : Json) : MetaM (Nat × Nat) := do
  let start ← IO.monoMsNow
  withBoundaryContext g fun base context => do
    let proof ← buildClause base clause rule
    let value ← mkLambdaFVars context proof
    let clauseType := clause.foldr
      (fun literal rest => arrow (g.falsity base.selectedList literal) rest) falseExpr
    let type ← mkForallFVars context clauseType
    let name := Name.str g.ns ("initial" ++ padded 5 number)
    let beforeKernel ← IO.monoMsNow
    addDecl (.thmDecl {name, levelParams := [], type, value})
    let afterKernel ← IO.monoMsNow
    return (beforeKernel-start, afterKernel-beforeKernel)

private def prepare (namespaceText manifestText : String) (inlineFacts : Bool := false) :
    MetaM (Globals × Array (Array Int) × Array Json) := do
  let manifest ← fromExcept (Json.parse manifestText)
  let ns := parseName namespaceText
  if namespaceText != (← strField manifest "namespace") then
    throwError "facet_initials%: namespace does not match the manifest"
  let data := mkConst (Name.str ns "data")
  let parent := mkApp (mkConst `Papers.RationalityTen.FacetSat.Data.toData) data
  let n := mkApp (mkConst `Papers.RationalityTen.GraphFacetClique.Data.count) parent
  let α := mkApp (mkConst ``Fin) n
  let listType := mkApp (mkConst ``List [.zero]) α
  let (selectedTemplate, decidableTemplate) ← withLCtx {} #[] do
    withLocalDeclD `S listType fun selectedList => do
      let selected ← withLocalDeclD `c α fun vertex => do
        let membership := mkApp (mkConst ``List.instMembership [.zero]) α
        mkLambdaFVars #[vertex] (mkAppN (mkConst ``Membership.mem [.zero, .zero])
          #[α, listType, membership, selectedList, vertex])
      let selectedDecidable ← withLocalDeclD `c α fun vertex => do
        let instanceExpr ← synthInstance (mkApp (mkConst ``Decidable) (mkApp selected vertex))
        mkLambdaFVars #[vertex] instanceExpr
      let selectedTemplate ← mkLambdaFVars #[selectedList] selected
      let decidableTemplate ← mkLambdaFVars #[selectedList] selectedDecidable
      return (selectedTemplate.bindingBody!, decidableTemplate.bindingBody!)
  let equalityTemplate ← withLCtx {} #[] do
    withLocalDeclD `a α fun a =>
      withLocalDeclD `b α fun b => do
        let instanceExpr ← synthInstance (mkApp (mkConst ``Decidable) (eqExpr α a b))
        mkLambdaFVars #[a, b] instanceExpr
  let atoms ← arrayField manifest "atoms"
  let rules ← arrayField manifest "rules"
  let mut groupedKinds := #[]
  for rule in rules do
    let tag ← strField rule "tag"
    if tag == "group_take" || tag == "group_or" || boolFieldD rule "grouped" false then
      let key ← natField rule "kind"
      if !groupedKinds.contains key then groupedKinds := groupedKinds.push key
  let mut groupTemplates : Std.HashMap Nat (Expr × Expr) := {}
  for key in groupedKinds do
    let grouping := mkConst (Name.str ns s!"grouping{key}")
    let templates ← withLCtx {} #[] do
      withLocalDeclD `S listType fun selectedList => do
        let selected := mkAppN (mkConst `Papers.RationalityTen.FacetSat.Grouping.selected)
          #[n, grouping, selectedList]
        let selectedDecidable ← withLocalDeclD `group natExpr fun index => do
          let instanceExpr ← synthInstance (mkApp (mkConst ``Decidable) (mkApp selected index))
          mkLambdaFVars #[index] instanceExpr
        let selectedTemplate ← mkLambdaFVars #[selectedList] selected
        let decidableTemplate ← mkLambdaFVars #[selectedList] selectedDecidable
        return (selectedTemplate.bindingBody!, decidableTemplate.bindingBody!)
    groupTemplates := groupTemplates.insert key templates
  let env ← getEnv
  let atomEquations := atoms.mapIdx fun index _ =>
    let name := Name.str ns ("atom" ++ padded 5 (index+1) ++ "_eq")
    match env.find? name with
    | some info =>
      match info.type with
      | .forallE _ _ body _ => some (mkConst name, body)
      | _ => none
    | none => none
  let g : Globals := {
    ns, data, n, α, listType, selectedTemplate, decidableTemplate, equalityTemplate,
    inlineFacts, factCache := ← IO.mkRef {},
    kind := mkApp (mkConst `Papers.RationalityTen.GraphFacetClique.Data.kind) parent,
    relation := mkApp (mkConst `Papers.RationalityTen.GraphFacetClique.Data.relation) parent,
    ridges := mkApp (mkConst `Papers.RationalityTen.FacetSat.Data.ridges) data,
    rows := mkApp (mkConst `Papers.RationalityTen.FacetSat.Data.ridgeRows) data,
    requirements := mkConst (Name.str ns "requirements"), manifest,
    atoms, atomEquations, groupTemplates,
    lower := boolFieldD manifest "lower_only" false,
    coverage := boolFieldD manifest "coverage" false,
    edgeCoverEnabled := boolFieldD manifest "edge_cover" false }
  let clauses ← arrayField manifest "clauses"
  if clauses.size != rules.size then throwError "facet_initials%: rule and clause counts differ"
  let clauses ← clauses.mapM fun json => do
    let clause ← intArray json
    for literal in clause do
      if literal == 0 || literal.natAbs > g.atoms.size then
        throwError "facet_initials%: atom index out of bounds"
    if clause.toList.eraseDups.length != clause.size then
      throwError "facet_initials%: duplicate clause literal"
    return clause
  return (g, clauses, rules)

private def checkedOptions (options : Options) : Options :=
  (options.setBool `Elab.async false).setBool `debug.skipKernelTC false

private def runInitials (namespaceText manifestText : String) : MetaM Unit := do
  let start ← IO.monoMsNow
  let (g, clauses, rules) ← prepare namespaceText manifestText
  let parsed ← IO.monoMsNow
  let (expressionMs, kernelMs) ← withOptions checkedOptions do
    let mut expressionMs := 0
    let mut kernelMs := 0
    for index in [:clauses.size] do
      try
        let (expression, kernel) ← buildInitial g (index + 1) clauses[index]! rules[index]!
        expressionMs := expressionMs + expression
        kernelMs := kernelMs + kernel
      catch exception => throwError "initial{padded 5 (index+1)}: {exception.toMessageData}"
    return (expressionMs, kernelMs)
  let finished ← IO.monoMsNow
  trace[FacetSatInitials] "{clauses.size} clauses; parsing {parsed-start} ms; expressions {expressionMs} ms; kernel {kernelMs} ms; total {finished-start} ms"

/-- Produce only the final boundary theorem, passing its initial clause
proofs directly to the abstract RUP refutation.  Initial clauses need not
become thousands of exported declarations or be elaborated a second time. -/
private def runRefutation (namespaceText manifestText cnf lrat : String) : MetaM Unit :=
  withOptions checkedOptions do
    let start ← IO.monoMsNow
    let (g, clauses, rules) ← prepare namespaceText manifestText true
    let prepared ← IO.monoMsNow
    let refutation ← RupProofTerm.mkRefutation cnf lrat
    let generic ← IO.monoMsNow
    let (expressionMs, kernelMs) ← withBoundaryContext g fun base context => do
      let mut hypotheses := #[]
      for index in [:clauses.size] do
        try
          hypotheses := hypotheses.push (← buildClause base clauses[index]! rules[index]!)
        catch exception => throwError "initial{padded 5 (index+1)}: {exception.toMessageData}"
      let valuation := mkApp (g.named "model") base.selectedList
      let proof := mkAppN refutation (#[valuation] ++ hypotheses)
      let value ← mkLambdaFVars context proof
      let type ← mkForallFVars context falseExpr
      let beforeKernel ← IO.monoMsNow
      let name := Name.str g.ns "boundary_unsat"
      addDecl (.thmDecl {name, levelParams := [], type, value})
      let afterKernel ← IO.monoMsNow
      return (beforeKernel-generic, afterKernel-beforeKernel)
    let finished ← IO.monoMsNow
    trace[FacetSatInitials] "fused {clauses.size} clauses; preparation {prepared-start} ms; generic RUP {generic-prepared} ms; initial expressions {expressionMs} ms; semantic kernel {kernelMs} ms; total {finished-start} ms"

syntax (name := facetInitials) "facet_initials% " str str : command

@[command_elab facetInitials] def elabFacetInitials : CommandElab := fun stx => do
  let some namespaceText := stx[1].isStrLit? | throwUnsupportedSyntax
  let some manifestText := stx[2].isStrLit? | throwUnsupportedSyntax
  liftTermElabM (runInitials namespaceText manifestText)

syntax (name := facetRefutation) "facet_refute% " str str str str : command

@[command_elab facetRefutation] def elabFacetRefutation : CommandElab := fun stx => do
  let some namespaceText := stx[1].isStrLit? | throwUnsupportedSyntax
  let some manifestText := stx[2].isStrLit? | throwUnsupportedSyntax
  let some cnf := stx[3].isStrLit? | throwUnsupportedSyntax
  let some lrat := stx[4].isStrLit? | throwUnsupportedSyntax
  liftTermElabM (runRefutation namespaceText manifestText cnf lrat)

end Papers.RationalityTen.FacetSatInitials
