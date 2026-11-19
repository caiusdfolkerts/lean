module

public meta import Lean.Elab.Command
public meta import Lean.Meta.AppBuilder

/-!
# Kernel-checked closed facts for facet SAT certificates

This command is an untrusted proof producer.  It constructs only equality
proofs and applications of the previously proved ridge-matrix lemma.  Every
declaration is checked synchronously by the ordinary kernel; a false Boolean
test cannot be turned into a theorem by the command.

Constructing the small proof expressions directly avoids running a separate
elaboration tactic for every closed ridge and owner-list fact.
-/

public meta section

namespace Papers.RationalityTen.FacetSatFacts

open Lean Meta Elab Command

initialize registerTraceClass `FacetSatFacts

private def fromExcept (value : Except String α) : MetaM α :=
  match value with
  | .ok value => pure value
  | .error message => throwError "facet_facts%: {message}"

private def parseName (text : String) : Name :=
  (text.splitOn ".").foldl Name.str .anonymous

private def pairs (json : Json) (key : String) : MetaM (Array (Nat × Nat)) := do
  let entries ← fromExcept ((← fromExcept (json.getObjVal? key)).getArr?)
  entries.mapM fun entry => do
    let values ← fromExcept entry.getArr?
    if values.size != 2 then throwError "facet_facts%: expected an index pair"
    return (← fromExcept values[0]!.getNat?, ← fromExcept values[1]!.getNat?)

private def indices (json : Json) : MetaM (Array Nat) := do
  (← fromExcept json.getArr?).mapM fun entry => fromExcept entry.getNat?

private def eqBool (left right : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Bool) left right

private def checked (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl (.thmDecl {name, levelParams := [], type, value})

private def runFacts (namespaceText manifestText : String) : MetaM Unit := do
  let start ← IO.monoMsNow
  let manifest ← fromExcept (Json.parse manifestText)
  let ns := parseName namespaceText
  let named (name : String) := mkConst (Name.str ns name)
  let data := named "data"
  let parent := mkApp (mkConst `Papers.RationalityTen.FacetSat.Data.toData) data
  let n := mkApp (mkConst `Papers.RationalityTen.GraphFacetClique.Data.count) parent
  let relation := mkApp (mkConst `Papers.RationalityTen.GraphFacetClique.Data.relation) parent
  let kind := mkApp (mkConst `Papers.RationalityTen.GraphFacetClique.Data.kind) parent
  let facet (index : Nat) := mkApp (named "facetIndex") (mkNatLit index)
  let ridge (index : Nat) := mkApp (named "ridgeIndex") (mkNatLit index)
  let trueExpr := mkConst ``Bool.true
  let boolExpr := mkConst ``Bool
  let reflTrue := mkApp2 (mkConst ``Eq.refl [.succ .zero]) boolExpr trueExpr
  let ridgePairs ← pairs manifest "ridges"
  let ownerEntries ← fromExcept ((← fromExcept (manifest.getObjVal? "owners")).getArr?)
  let α := mkApp (mkConst ``Fin) n
  let listType := mkApp (mkConst ``List [.zero]) α
  let facetList (values : Array Nat) :=
    values.foldr (fun value tail => mkApp3 (mkConst ``List.cons [.zero]) α (facet value) tail)
      (mkApp (mkConst ``List.nil [.zero]) α)
  withOptions (fun options => options.setBool `Elab.async false |>.setBool `debug.skipKernelTC false) do
    if let .ok groupingsJson := manifest.getObjVal? "groupings" then
      for key in (← indices groupingsJson) do
        let test := mkAppN (mkConst `Papers.RationalityTen.FacetSat.Grouping.check)
          #[n, named s!"grouping{key}", kind, relation, mkNatLit key]
        checked (Name.str ns s!"grouping{key}_checked") (eqBool test trueExpr) reflTrue
    if let .ok edgesJson := manifest.getObjVal? "edges" then
      for entry in (← fromExcept edgesJson.getArr?) do
        let values ← fromExcept entry.getArr?
        if values.size != 2 then throwError "facet_facts%: expected an edge and owner list"
        let index ← fromExcept values[0]!.getNat?
        let ownerName := Name.str ns s!"edgeOwners_{index}"
        let ownerValue := facetList (← indices values[1]!)
        addDecl (.defnDecl { name := ownerName, levelParams := [], type := listType, value := ownerValue, hints := .regular 0, safety := .safe }) (forceExpose := true)
        let edge := mkApp (named "edgeIndex") (mkNatLit index)
        let edgeVal := mkApp2 (mkConst ``Fin.val) (named "edgeCount") edge
        let required := mkApp2 (mkConst ``Nat.testBit) (named "requiredEdges") edgeVal
        checked (Name.str ns s!"edge_{index}_required") (eqBool required trueExpr) reflTrue
        let test := mkApp3 (mkConst `Papers.RationalityTen.FacetSat.EdgeCover.ownersCheck)
          n (mkApp (named "edgeRows") edge) (mkConst ownerName)
        checked (Name.str ns s!"edge_{index}_owners_checked") (eqBool test trueExpr) reflTrue
    for (a, q) in ridgePairs do
      let av := facet a
      let qv := ridge q
      let row := mkApp2 (mkConst `Papers.RationalityTen.FacetSat.Data.ridgeRows) data qv
      let bit := mkApp2 (mkConst ``Nat.testBit) row (mkApp2 (mkConst ``Fin.val) n av)
      let incident := mkApp3 (mkConst `Papers.RationalityTen.FacetSat.Data.ridges) data av qv
      let exactRow := mkApp4 (mkConst `Papers.RationalityTen.FacetSat.Data.ridgeRows_exact)
        data (named "ridge_matrix_checked") qv av
      let reverse := mkApp4 (mkConst ``Eq.symm [.succ .zero]) boolExpr bit incident exactRow
      let proof := mkApp6 (mkConst ``Eq.trans [.succ .zero])
        boolExpr incident bit trueExpr reverse reflTrue
      checked (Name.str ns s!"ridge_{a}_{q}") (eqBool incident trueExpr) proof
    for entry in ownerEntries do
      let values ← fromExcept entry.getArr?
      if values.size != 2 && values.size != 4 then
        throwError "facet_facts%: expected an owner pair, optionally with two index lists"
      let a ← fromExcept values[0]!.getNat?
      let q ← fromExcept values[1]!.getNat?
      if values.size == 4 then
        for (suffix, position) in #[("owners", 2), ("dropped", 3)] do
          let name := Name.str ns s!"{suffix}_{a}_{q}"
          let value := facetList (← indices values[position]!)
          addDecl (.defnDecl { name := name, levelParams := [], type := listType, value := value, hints := .regular 0, safety := .safe }) (forceExpose := true)
      let row := mkApp2 (mkConst `Papers.RationalityTen.FacetSat.Data.ridgeRows) data (ridge q)
      let test := mkAppN (mkConst `Papers.RationalityTen.FacetSat.Boundary.packedOwnersCheck)
        #[n, relation, row, facet a, named s!"owners_{a}_{q}", named s!"dropped_{a}_{q}"]
      checked (Name.str ns s!"owners_{a}_{q}_checked") (eqBool test trueExpr) reflTrue
  let finished ← IO.monoMsNow
  trace[FacetSatFacts] "{ridgePairs.size} ridge facts, {ownerEntries.size} owner facts; proof construction and kernel {finished-start} ms"

syntax (name := facetFacts) "facet_facts% " str str : command

@[command_elab facetFacts] def elabFacetFacts : CommandElab := fun stx => do
  let some namespaceText := stx[1].isStrLit? | throwUnsupportedSyntax
  let some manifestText := stx[2].isStrLit? | throwUnsupportedSyntax
  liftTermElabM (runFacts namespaceText manifestText)

private partial def lookupLeaf (tree : Expr) (index : Nat) : MetaM Expr := do
  let args := tree.getAppArgs
  if tree.isAppOfArity `Papers.RationalityTen.ConcreteGrowth.Table.leaf 2 then
    return args[1]!
  if tree.isAppOfArity `Papers.RationalityTen.ConcreteGrowth.Table.branch 4 then
    let some cut ← getNatValue? args[1]! |
      throwError "facet_atoms%: table cut is not a closed natural number"
    return ← lookupLeaf (if index < cut then args[2]! else args[3]!) index
  let reduced ← whnf tree
  if reduced == tree then throwError "facet_atoms%: expected a transparent balanced table"
  lookupLeaf reduced index

private def runAtoms (namespaceText : String) (count : Nat) : MetaM Unit := do
  let start ← IO.monoMsNow
  let ns := parseName namespaceText
  let named (name : String) := mkConst (Name.str ns name)
  let data := named "data"
  let parent := mkApp (mkConst `Papers.RationalityTen.FacetSat.Data.toData) data
  let n := mkApp (mkConst `Papers.RationalityTen.GraphFacetClique.Data.count) parent
  let listType := mkApp (mkConst ``List [.zero]) (mkApp (mkConst ``Fin) n)
  let some table := (← getConstInfo (Name.str ns "modelTable")).value? |
    throwError "facet_atoms%: missing transparent model table"
  withOptions (fun options => options.setBool `Elab.async false |>.setBool `debug.skipKernelTC false) do
    for index in [1:count+1] do
      let meaning ← lookupLeaf table index
      withLocalDeclD `S listType fun selected => do
        let left := mkApp2 (named "model") selected (mkNatLit index)
        let right := mkApp meaning selected
        let prop := mkSort .zero
        let target := mkApp3 (mkConst ``Eq [.succ .zero]) prop left right
        let proof := mkApp2 (mkConst ``Eq.refl [.succ .zero]) prop right
        let type ← mkForallFVars #[selected] target
        let value ← mkLambdaFVars #[selected] proof
        let digits := toString index
        let padded := String.ofList (List.replicate (5 - digits.length) '0') ++ digits
        checked (Name.str ns s!"atom{padded}_eq") type value
  let finished ← IO.monoMsNow
  trace[FacetSatFacts] "{count} atom equalities; proof construction and kernel {finished-start} ms"

private partial def balancedTable (α : Expr) (values : Array Expr) (lo hi : Nat) : Expr :=
  if hi - lo ≤ 1 then
    mkApp2 (mkConst `Papers.RationalityTen.ConcreteGrowth.Table.leaf) α values[lo]!
  else
    let middle := lo + (hi - lo) / 2
    mkApp4 (mkConst `Papers.RationalityTen.ConcreteGrowth.Table.branch) α (mkNatLit middle)
      (balancedTable α values lo middle) (balancedTable α values middle hi)

private def runModel (namespaceText manifestText : String) : MetaM Unit := do
  let start ← IO.monoMsNow
  let manifest ← fromExcept (Json.parse manifestText)
  let atoms ← fromExcept ((← fromExcept (manifest.getObjVal? "atoms")).getArr?)
  let ns := parseName namespaceText
  let named (name : String) := mkConst (Name.str ns name)
  let data := named "data"
  let parent := mkApp (mkConst `Papers.RationalityTen.FacetSat.Data.toData) data
  let n := mkApp (mkConst `Papers.RationalityTen.GraphFacetClique.Data.count) parent
  let α := mkApp (mkConst ``Fin) n
  let listType := mkApp (mkConst ``List [.zero]) α
  let prop := mkSort .zero
  let atomType := Expr.forallE .anonymous listType prop .default
  let membership ← synthInstance (mkApp2 (mkConst ``Membership [.zero, .zero]) α listType)
  let meanings ← withLocalDeclD `S listType fun selectedList => do
    let selected ← withLocalDeclD `c α fun vertex =>
      mkLambdaFVars #[vertex] (mkAppN (mkConst ``Membership.mem [.zero, .zero])
        #[α, listType, membership, selectedList, vertex])
    let selectedDecidable ← withLocalDeclD `c α fun vertex => do
      let instanceExpr ← synthInstance (mkApp (mkConst ``Decidable) (mkApp selected vertex))
      mkLambdaFVars #[vertex] instanceExpr
    let mut groupedPredicates : Array (Nat × Expr × Expr) := #[]
    let mut meanings := #[← mkLambdaFVars #[selectedList] (mkConst ``False)]
    for atom in atoms do
      let tag ← fromExcept ((← fromExcept (atom.getObjVal? "tag")).getStr?)
      let grouped := tag == "group" || tag == "group_totalizer"
      let (atomα, atomSelected, atomDecidable) ← if grouped then do
        let kind ← fromExcept ((← fromExcept (atom.getObjVal? "kind")).getNat?)
        let (predicate, decision) ← match groupedPredicates.find? (fun entry => entry.1 == kind) with
          | some (_, predicate, decision) => pure (predicate, decision)
          | none => do
            let predicate := mkApp3 (mkConst `Papers.RationalityTen.FacetSat.Grouping.selected)
              n (named s!"grouping{kind}") selectedList
            let decision ← synthInstance
              (mkApp2 (mkConst ``DecidablePred [.zero]) (mkConst ``Nat) predicate)
            groupedPredicates := groupedPredicates.push (kind, predicate, decision)
            pure (predicate, decision)
        pure (mkConst ``Nat, predicate, decision)
      else pure (α, selected, selectedDecidable)
      let meaning ← if tag == "facet" then do
        let index ← fromExcept ((← fromExcept (atom.getObjVal? "index")).getNat?)
        pure (mkApp selected (mkApp (named "facetIndex") (mkNatLit index)))
      else if tag == "group" then do
        let index ← fromExcept ((← fromExcept (atom.getObjVal? "index")).getNat?)
        pure (mkApp atomSelected (mkNatLit index))
      else do
        let threshold ← fromExcept ((← fromExcept (atom.getObjVal? "threshold")).getNat?)
        let vertices ← if tag == "counter" then do
          let kind ← fromExcept ((← fromExcept (atom.getObjVal? "kind")).getNat?)
          let position ← fromExcept ((← fromExcept (atom.getObjVal? "prefix")).getNat?)
          pure (mkApp3 (mkConst ``List.take [.zero]) α (mkNatLit position) (named s!"kind{kind}"))
        else if tag == "totalizer" || tag == "group_totalizer" then do
          let listName ← fromExcept ((← fromExcept (atom.getObjVal? "list_name")).getStr?)
          pure (named listName)
        else throwError "facet_model%: unsupported atom tag {tag}"
        pure (mkAppN (mkConst `Papers.RationalityTen.SequentialCounter.reached)
          #[atomα, atomSelected, atomDecidable, vertices, mkNatLit threshold])
      meanings := meanings.push (← mkLambdaFVars #[selectedList] meaning)
    return meanings
  let tableType := mkApp (mkConst `Papers.RationalityTen.ConcreteGrowth.Table) atomType
  let tableValue := balancedTable atomType meanings 0 meanings.size
  withOptions (fun options => options.setBool `Elab.async false |>.setBool `debug.skipKernelTC false) do
    addDecl (.defnDecl { name := Name.str ns "modelTable", levelParams := [], type := tableType, value := tableValue, hints := .regular 0, safety := .safe }) (forceExpose := true)
    withLocalDeclD `S listType fun selectedList =>
      withLocalDeclD `atomIndex (mkConst ``Nat) fun index => do
        let lookup := mkApp3 (mkConst `Papers.RationalityTen.ConcreteGrowth.Table.get)
          atomType (named "modelTable") index
        let value ← mkLambdaFVars #[selectedList, index] (mkApp lookup selectedList)
        let type ← mkForallFVars #[selectedList, index] prop
        addDecl (.defnDecl { name := Name.str ns "model", levelParams := [], type, value, hints := .regular 0, safety := .safe }) (forceExpose := true)
  let finished ← IO.monoMsNow
  trace[FacetSatFacts] "{atoms.size} model atoms; proof construction and kernel {finished-start} ms"

syntax (name := facetModel) "facet_model% " str str : command

@[command_elab facetModel] def elabFacetModel : CommandElab := fun stx => do
  let some namespaceText := stx[1].isStrLit? | throwUnsupportedSyntax
  let some manifestText := stx[2].isStrLit? | throwUnsupportedSyntax
  liftTermElabM (runModel namespaceText manifestText)

syntax (name := facetAtoms) "facet_atoms% " str num : command

@[command_elab facetAtoms] def elabFacetAtoms : CommandElab := fun stx => do
  let some namespaceText := stx[1].isStrLit? | throwUnsupportedSyntax
  let some count := stx[2].isNatLit? | throwUnsupportedSyntax
  liftTermElabM (runAtoms namespaceText count)

end Papers.RationalityTen.FacetSatFacts
