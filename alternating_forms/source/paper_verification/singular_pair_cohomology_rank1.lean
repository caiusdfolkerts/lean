module

public import paper_verification.exact_sequence_rank2
import all paper_verification.exact_sequence_rank2
public import paper_verification.oai_thom003_run1
import all paper_verification.oai_thom003_run1
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: PaperVerification.SingularPairCohomologyRank -/

/-!
# Rank and vanishing in the genuine singular-cohomology pair sequence

These statements use the original relative, absolute, and subspace groups,
with exactness proved from their actual singular cochain complexes.
-/

namespace PaperVerification.SingularCohomologyRank

noncomputable section

open CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular

section Pair

variable {K : Type} [Field K] (X : TopCat.{0}) (A : Set X) (n : ℕ)

/-- Finiteness propagates through the actual relative/absolute/subspace
cohomology sequence, without assuming that restriction is surjective. -/
theorem finite_of_pair
    [Module.Finite K (RelativeSequence.relativeSingularCohomology
      (ModuleCat.of K K) X A n)]
    [Module.Finite K (Basic.singularCohomology (ModuleCat.of K K) (TopCat.of A) n)] :
    Module.Finite K (Basic.singularCohomology (ModuleCat.of K K) X n) :=
  ExactSequenceRank.finite_middle
    (RelativeSequence.relativeCohomologyInclusion (ModuleCat.of K K) X A n).hom
    (RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of K K) X A n).hom
    (RelativeSequence.relativeCohomology_range_inclusion (ModuleCat.of K K) X A n)

/-- The rank estimate uses the original maps in the long exact sequence. -/
theorem finrank_le_relative_add_subspace
    [Module.Finite K (RelativeSequence.relativeSingularCohomology
      (ModuleCat.of K K) X A n)]
    [Module.Finite K (Basic.singularCohomology (ModuleCat.of K K) (TopCat.of A) n)] :
    Module.finrank K (Basic.singularCohomology (ModuleCat.of K K) X n) ≤
      Module.finrank K (RelativeSequence.relativeSingularCohomology
        (ModuleCat.of K K) X A n) +
      Module.finrank K (Basic.singularCohomology (ModuleCat.of K K) (TopCat.of A) n) :=
  ExactSequenceRank.finrank_middle_le
    (RelativeSequence.relativeCohomologyInclusion (ModuleCat.of K K) X A n).hom
    (RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of K K) X A n).hom
    (RelativeSequence.relativeCohomology_range_inclusion (ModuleCat.of K K) X A n)

/-- Vanishing propagates through the same sequence. -/
theorem isZero_of_pair
    (hrel : IsZero (RelativeSequence.relativeSingularCohomology
      (ModuleCat.of K K) X A n))
    (hopen : IsZero (Basic.singularCohomology (ModuleCat.of K K) (TopCat.of A) n)) :
    IsZero (Basic.singularCohomology (ModuleCat.of K K) X n) := by
  letI := ModuleCat.subsingleton_of_isZero hrel
  letI := ModuleCat.subsingleton_of_isZero hopen
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ExactSequenceRank.subsingleton_middle
    (RelativeSequence.relativeCohomologyInclusion (ModuleCat.of K K) X A n).hom
    (RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of K K) X A n).hom
    (RelativeSequence.relativeCohomology_range_inclusion (ModuleCat.of K K) X A n)

end Pair

end
end PaperVerification.SingularCohomologyRank
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SingularPairCohomologyRank"


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
    (`PaperVerification.SingularCohomologyRank.finite_of_pair, "theorem"),
    (`PaperVerification.SingularCohomologyRank.finrank_le_relative_add_subspace, "theorem"),
    (`PaperVerification.SingularCohomologyRank.isZero_of_pair, "theorem")
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
    ("nonce", toJson "83b3c7d094279b1adbe4bed934668d95"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:83b3c7d094279b1adbe4bed934668d95"
