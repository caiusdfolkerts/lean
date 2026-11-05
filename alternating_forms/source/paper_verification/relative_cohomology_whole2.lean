module

public import paper_verification.oai_thom003_run1
import all paper_verification.oai_thom003_run1
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: PaperVerification.RelativeCohomologyWhole -/

/-!
# The actual relative cohomology of a space relative to itself

Restriction to the whole subspace is an isomorphism of singular cochain
complexes. Its kernel is therefore zero in every degree. This also handles
an empty geometric stratum when its open complement is the entire space.
-/

namespace PaperVerification.RelativeCohomologyWhole

noncomputable section

open CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular
open OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0})

/-- The literal whole-subspace inclusion is the hom of this topological
isomorphism; no replacement of the underlying space is made. -/
def wholeSubspaceIso : TopCat.of (Set.univ : Set X) ≅ X where
  hom := subspaceInclusion X Set.univ
  inv := TopCat.ofHom ⟨fun x => ⟨x, Set.mem_univ x⟩,
    continuous_id.subtype_mk _⟩
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

instance wholeSubspaceInclusion_isIso :
    IsIso (subspaceInclusion X Set.univ) :=
  inferInstanceAs (IsIso (wholeSubspaceIso X).hom)

instance wholeSubspaceRestriction_isIso :
    IsIso (RelativeSequence.subspaceCochainRestriction M X Set.univ) := by
  change IsIso ((Functor.singularCochainsFunctor M).map
    (subspaceInclusion X Set.univ).op)
  infer_instance

theorem relativeCochains_univ_isZero :
    IsZero (RelativeSequence.relativeSingularCochains M X Set.univ) :=
  isZero_kernel_of_mono (RelativeSequence.subspaceCochainRestriction M X Set.univ)

/-- All genuine relative singular groups of `(X,X)` vanish. -/
theorem relativeCohomology_univ_isZero (n : ℕ) :
    IsZero (RelativeSequence.relativeSingularCohomology M X Set.univ n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n).map_isZero (relativeCochains_univ_isZero M X)

end
end PaperVerification.RelativeCohomologyWhole
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.RelativeCohomologyWhole"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.RelativeCohomologyWhole.relativeCochains_univ_isZero, "theorem"),
    (`PaperVerification.RelativeCohomologyWhole.relativeCohomology_univ_isZero, "theorem"),
    (`PaperVerification.RelativeCohomologyWhole.wholeSubspaceIso, "definition")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "dd8efe72b2cf5f1362dfae378cd20bb1"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:dd8efe72b2cf5f1362dfae378cd20bb1"
