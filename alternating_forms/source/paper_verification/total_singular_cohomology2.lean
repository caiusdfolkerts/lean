module

public import paper_verification.direct_sum_concentration2
import all paper_verification.direct_sum_concentration2
public import paper_verification.exact_sequence_rank2
import all paper_verification.exact_sequence_rank2
public import paper_verification.empty_singular_cohomology3
import all paper_verification.empty_singular_cohomology3
public import paper_verification.oai_thom003_run1
import all paper_verification.oai_thom003_run1
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: PaperVerification.TotalSingularCohomology -/

/-!
# Total singular cohomology and the actual pair sequence

The total group is the direct sum of the genuine singular groups over all
natural degrees. Degreewise exactness gives exactness of the direct-sum maps.
Thus a finite paving can be treated without a cohomological degree cutoff.
-/

namespace PaperVerification.TotalSingularCohomology

noncomputable section

open CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular
open scoped DirectSum

variable {K : Type} [Field K]

abbrev total (X : TopCat.{0}) :=
  ⨁ n : ℕ, Basic.singularCohomology (ModuleCat.of K K) X n

abbrev relativeTotal (X : TopCat.{0}) (A : Set X) :=
  ⨁ n : ℕ, RelativeSequence.relativeSingularCohomology (ModuleCat.of K K) X A n

def inclusion (X : TopCat.{0}) (A : Set X) :
    relativeTotal (K := K) X A →ₗ[K] total (K := K) X :=
  DirectSum.lmap fun n =>
    (RelativeSequence.relativeCohomologyInclusion (ModuleCat.of K K) X A n).hom

def restriction (X : TopCat.{0}) (A : Set X) :
    total (K := K) X →ₗ[K] total (K := K) (TopCat.of A) :=
  DirectSum.lmap fun n =>
    (RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of K K) X A n).hom

/-- The direct sum of the original pair-sequence maps is exact. -/
theorem range_inclusion_eq_ker_restriction (X : TopCat.{0}) (A : Set X) :
    LinearMap.range (inclusion (K := K) X A) = LinearMap.ker (restriction (K := K) X A) :=
  DirectSumConcentration.range_eq_ker _ _ fun n =>
    RelativeSequence.relativeCohomology_range_inclusion (ModuleCat.of K K) X A n

theorem finite_and_finrank_le (X : TopCat.{0}) (A : Set X)
    [Module.Finite K (relativeTotal (K := K) X A)]
    [Module.Finite K (total (K := K) (TopCat.of A))] :
    Module.Finite K (total (K := K) X) ∧
      Module.finrank K (total (K := K) X) ≤
        Module.finrank K (relativeTotal (K := K) X A) +
        Module.finrank K (total (K := K) (TopCat.of A)) :=
  ⟨ExactSequenceRank.finite_middle (inclusion X A) (restriction X A)
      (range_inclusion_eq_ker_restriction X A),
    ExactSequenceRank.finrank_middle_le (inclusion X A) (restriction X A)
      (range_inclusion_eq_ker_restriction X A)⟩

/-- The initial total group of an empty stage is literally zero. -/
theorem subsingleton_of_isEmpty (X : TopCat.{0}) [IsEmpty X] :
    Subsingleton (total (K := K) X) := by
  letI (n : ℕ) : Subsingleton (Basic.singularCohomology (ModuleCat.of K K) X n) :=
    ModuleCat.subsingleton_of_isZero
      (EmptySingularCohomology.cohomology_isZero (ModuleCat.of K K) X n)
  infer_instance

end
end PaperVerification.TotalSingularCohomology
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TotalSingularCohomology"


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
    (`PaperVerification.TotalSingularCohomology.range_inclusion_eq_ker_restriction, "theorem"),
    (`PaperVerification.TotalSingularCohomology.finite_and_finrank_le, "theorem"),
    (`PaperVerification.TotalSingularCohomology.subsingleton_of_isEmpty, "theorem"),
    (`PaperVerification.TotalSingularCohomology.total, "definition"),
    (`PaperVerification.TotalSingularCohomology.relativeTotal, "definition")
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
    ("nonce", toJson "22b44762f5b861376080a06d79757e99"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:22b44762f5b861376080a06d79757e99"
