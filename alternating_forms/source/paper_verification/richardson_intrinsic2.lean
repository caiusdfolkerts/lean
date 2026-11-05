module

public import paper_verification.global_comparisons4
import all paper_verification.global_comparisons4
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.RichardsonIntrinsicRankIdeal -/


/-!
# The full rank ideal of the actual tautological flag projections

The independent determinantal ideal on each ambient chart is generated
by minors of the actual tautological frame, viewed as genuine
structure-sheaf sections.  Its equality with the polynomial rank ideal
is proved before taking any quotient, radical, or geometric point.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite Matrix
open scoped Matrix

namespace PaperVerification.SchubertRankIdeals

variable {R S : Type*} [CommRing R] [CommRing S] {s n : ℕ}

/-- Base change of the full restricted-minor ideal, over arbitrary
commutative rings. -/
theorem restrictedMinorIdeal_map (f : R →+* S)
    (A : Matrix (Fin s) (Fin n) R) (q : ℕ) (C : Set (Fin n)) :
    (restrictedMinorIdeal A q C).map f = restrictedMinorIdeal (A.map f) q C := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro z ⟨rows, cols, hcols, rfl⟩
    change f ((A.submatrix rows cols).det) ∈ restrictedMinorIdeal (A.map f) q C
    rw [f.map_det, RingHom.mapMatrix_apply]
    exact Ideal.subset_span ⟨rows, cols, hcols, rfl⟩
  · apply Ideal.span_le.mpr
    rintro z ⟨rows, cols, hcols, rfl⟩
    change ((A.submatrix rows cols).map f).det ∈ (restrictedMinorIdeal A q C).map f
    rw [← RingHom.mapMatrix_apply, ← f.map_det]
    exact Ideal.mem_map_of_mem f (Ideal.subset_span ⟨rows, cols, hcols, rfl⟩)

end PaperVerification.SchubertRankIdeals

namespace PaperVerification.AlternatingForms

variable {R S : Type*} [CommRing R] [CommRing S] {s n : ℕ}

theorem richardsonChartRankIdeal_map (f : R →+* S)
    (A : Matrix (Fin s) (Fin n) R) (α β : Fin s → Fin n) :
    (richardsonChartRankIdeal A α β).map f =
      richardsonChartRankIdeal (A.map f) α β := by
  simp only [richardsonChartRankIdeal, Ideal.map_iSup, Ideal.map_sup,
    SchubertRankIdeals.restrictedMinorIdeal_map]

variable {K : Type} [Field K] {t : ℕ}

/-- The matrix of the genuine ambient-coordinate projections on the
actual local basis of the tautological subbundle. -/
def ambientTautologicalFrameMatrix (p : PluckerIndex (t + 2) n)
    (U : (ambientGrassmannian (K := K) t n).Opens)
    (hU : U ≤ tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n))) :
    Matrix (Fin (t + 2)) (Fin n) Γ(ambientGrassmannian (K := K) t n, U) :=
  fun i c ↦ tautologicalSectionCoordinates emptyAlternatingTuple U
    (tautologicalRowSection p emptyAlternatingTuple U hU i) c

theorem ambientTautologicalFrameMatrix_eq (p : PluckerIndex (t + 2) n)
    (U : (ambientGrassmannian (K := K) t n).Opens)
    (hU : U ≤ tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n))) :
    ambientTautologicalFrameMatrix p U hU =
      (pluckerChartMatrix p).map (tautologicalLocalPolynomialHom p emptyAlternatingTuple U hU) := by
  funext i c
  exact congrFun (tautologicalRowSection_coordinates p emptyAlternatingTuple U hU i) c

/-- Full opposite-flag determinantal ideal in the actual section ring. -/
def ambientRichardsonIntrinsicChartIdeal (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n)
    (U : (ambientGrassmannian (K := K) t n).Opens)
    (hU : U ≤ tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n))) :
    Ideal Γ(ambientGrassmannian (K := K) t n, U) :=
  richardsonChartRankIdeal (ambientTautologicalFrameMatrix p U hU) α β

/-- Exact equality of the actual tautological rank ideal and the
polynomial chart ideal, on every subopen of each chart. -/
theorem ambientRichardsonIntrinsicChartIdeal_eq_map (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n)
    (U : (ambientGrassmannian (K := K) t n).Opens)
    (hU : U ≤ tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n))) :
    ambientRichardsonIntrinsicChartIdeal p α β U hU =
      (richardsonChartIdeal (K := K) p α β).map
        (tautologicalLocalPolynomialHom p emptyAlternatingTuple U hU) := by
  rw [ambientRichardsonIntrinsicChartIdeal, ambientTautologicalFrameMatrix_eq]
  exact (richardsonChartRankIdeal_map _ _ α β).symm

end PaperVerification.AlternatingForms
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.RichardsonIntrinsicRankIdeal"


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
    (`PaperVerification.SchubertRankIdeals.restrictedMinorIdeal_map, "theorem"),
    (`PaperVerification.AlternatingForms.richardsonChartRankIdeal_map, "theorem"),
    (`PaperVerification.AlternatingForms.ambientTautologicalFrameMatrix, "definition"),
    (`PaperVerification.AlternatingForms.ambientTautologicalFrameMatrix_eq, "theorem"),
    (`PaperVerification.AlternatingForms.ambientRichardsonIntrinsicChartIdeal, "definition"),
    (`PaperVerification.AlternatingForms.ambientRichardsonIntrinsicChartIdeal_eq_map, "theorem")
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
    ("nonce", toJson "727a6b67149fab71c3e97127644fdbad"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:727a6b67149fab71c3e97127644fdbad"
