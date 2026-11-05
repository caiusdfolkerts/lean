module

public import paper_verification.schubert_rank3
import all paper_verification.schubert_rank3
public import paper_verification.literal001
import all paper_verification.literal001
public import Mathlib.Order.Interval.Finset.Fin
public import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.SchubertFlagIndices -/


/-!
# Flag-rank conditions and ordered Plücker indices

For an increasing index, failure of an upper or lower flag bound is exactly
existence of the expected number of distinct positions in the corresponding
coordinate projection.  These finite counting lemmas connect genuine
restricted minors to the printed Richardson interval.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

variable {s n : ℕ}

/-- An upper flag bound fails exactly when `s - j` selected columns lie
strictly beyond that flag step. -/
theorem upper_flag_failure_iff_selected_columns
    (I : PluckerIndex s n) (j : Fin s) (b : Fin n) :
    b < I.val j ↔ ∃ e : Fin (s - j.val) ↪ Fin s, ∀ i, b < I.val (e i) := by
  classical
  constructor
  · intro h
    let e : Fin (s - j.val) ↪ Fin s :=
      ⟨fun i ↦ ⟨j.val + i.val, by have := i.isLt; have := j.isLt; omega⟩,
        by intro i k h; apply Fin.ext; have := congrArg Fin.val h; simp only at this; omega⟩
    refine ⟨e, fun i ↦ lt_of_lt_of_le h (I.property.monotone ?_)⟩
    change j.val ≤ j.val + i.val
    omega
  · rintro ⟨e, he⟩
    by_contra h
    have hI : I.val j ≤ b := le_of_not_gt h
    have hsub : Finset.univ.image e ⊆ Finset.Ioi j := by
      intro i hi
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_Ioi.mpr (I.property.lt_iff_lt.mp (lt_of_le_of_lt hI (he a)))
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ e.injective, Finset.card_univ,
      Fintype.card_fin, Fin.card_Ioi] at hc
    have := j.isLt
    omega

/-- A lower flag bound fails exactly when `j + 1` selected columns lie
strictly before that flag step. -/
theorem lower_flag_failure_iff_selected_columns
    (I : PluckerIndex s n) (j : Fin s) (a : Fin n) :
    I.val j < a ↔ ∃ e : Fin (j.val + 1) ↪ Fin s, ∀ i, I.val (e i) < a := by
  classical
  constructor
  · intro h
    let e : Fin (j.val + 1) ↪ Fin s :=
      ⟨fun i ↦ ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩,
        by intro i k h; apply Fin.ext; exact congrArg (fun x : Fin s ↦ x.val) h⟩
    refine ⟨e, fun i ↦ lt_of_le_of_lt (I.property.monotone ?_) h⟩
    change i.val ≤ j.val
    have := i.isLt
    omega
  · rintro ⟨e, he⟩
    by_contra h
    have hI : a ≤ I.val j := le_of_not_gt h
    have hsub : Finset.univ.image e ⊆ Finset.Iio j := by
      intro i hi
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_Iio.mpr (I.property.lt_iff_lt.mp (lt_of_lt_of_le (he k) hI))
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ e.injective, Finset.card_univ,
      Fintype.card_fin, Fin.card_Iio] at hc
    omega

/-- Sorting a maximal-minor column map preserves all selected-column
conditions, with an explicitly transported injection of positions. -/
theorem sortedPluckerIndex_selected_columns
    (cols : Fin s → Fin n) (hc : Function.Injective cols)
    (q : ℕ) (C : Set (Fin n)) (e : Fin q ↪ Fin s)
    (he : ∀ i, cols (e i) ∈ C) :
    ∃ e' : Fin q ↪ Fin s, ∀ i, (sortedPluckerIndex cols hc).val (e' i) ∈ C := by
  refine ⟨⟨fun i ↦ (Tuple.sort cols).symm (e i),
    (Tuple.sort cols).symm.injective.comp e.injective⟩, ?_⟩
  intro i
  change cols ((Tuple.sort cols) ((Tuple.sort cols).symm (e i))) ∈ C
  simpa only [Equiv.apply_symm_apply] using he i

end PaperVerification.AlternatingForms
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SchubertFlagIndices"

section ComponentSource_1
/- Original module: PaperVerification.RichardsonChartIdeals -/


/-!
# The Richardson interval as actual opposite flag-rank equations

The rank conditions are independently defined by minors of coordinate
projections of a normalized matrix.  Their ideal is proved equal to the
image of the original interval Plücker ideal, over every field.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Matrix MvPolynomial
open scoped BigOperators
open PaperVerification.SchubertRankIdeals

namespace PaperVerification.AlternatingForms

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] {s n : ℕ}

/-- Coordinate generators whose indices contain enough selected positions
in a specified coordinate projection. -/
def selectedPluckerIdeal (q : ℕ) (C : Set (Fin n)) :
    Ideal (MvPolynomial (PluckerIndex s n) K) :=
  Ideal.span {z | ∃ I : PluckerIndex s n,
    (∃ e : Fin q ↪ Fin s, ∀ i, I.val (e i) ∈ C) ∧ z = X I}

/-- Evaluation identifies these coordinate equations with the corresponding
full minors, before any Grassmannian normalization is assumed. -/
theorem fullRestrictedMinorIdeal_eq_map_selectedPluckerIdeal
    (A : Matrix (Fin s) (Fin n) R) (q : ℕ) (C : Set (Fin n)) :
    fullRestrictedMinorIdeal A q C =
      (selectedPluckerIdeal (K := K) (s := s) q C).map
        (matrixMinorEvaluation A).toRingHom := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro z ⟨cols, e, hcols, rfl⟩
    change Matrix.det (Matrix.of fun i j : Fin s ↦ A i (cols j)) ∈ _
    rw [← matrixMinorEvaluation_orderedCoordinate (K := K) A cols]
    by_cases hc : Function.Injective cols
    · apply Ideal.mem_map_of_mem
      rw [orderedPluckerCoordinate, dif_pos hc]
      rw [Algebra.smul_def]
      apply Ideal.mul_mem_left
      apply Ideal.subset_span
      exact ⟨sortedPluckerIndex cols hc,
        sortedPluckerIndex_selected_columns cols hc q C e hcols, rfl⟩
    · simp only [orderedPluckerCoordinate, dif_neg hc, map_zero]
      exact Ideal.zero_mem _
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro z ⟨I, ⟨e, he⟩, rfl⟩
    change matrixMinorEvaluation (K := K) A (X I) ∈ fullRestrictedMinorIdeal A q C
    apply Ideal.subset_span
    exact ⟨I.val, e, he, by
      simp only [matrixMinorEvaluation, aeval_X, Matrix.submatrix, id_eq]⟩

/-- The sum of the two opposite flag-rank ideals, with the ordinary minor
sizes `s-j` and `j+1` at the zero-based position `j`. -/
def richardsonChartRankIdeal (A : Matrix (Fin s) (Fin n) R)
    (α β : Fin s → Fin n) : Ideal R :=
  ⨆ j : Fin s,
    restrictedMinorIdeal A (s - j.val) {c | β j < c} ⊔
      restrictedMinorIdeal A (j.val + 1) {c | c < α j}

/-- The printed interval inequalities are precisely the full Plücker
coordinates forced by the two opposite flags. -/
theorem intervalPluckerIdeal_eq_flag_coordinates (α β : Fin s → Fin n) :
    intervalPluckerIdeal (K := K) α β =
      matrixPluckerIdeal ⊔ ⨆ j : Fin s,
        selectedPluckerIdeal (K := K) (s := s) (s - j.val) {c | β j < c} ⊔
          selectedPluckerIdeal (K := K) (s := s) (j.val + 1) {c | c < α j} := by
  classical
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    rintro z ⟨I, hbad, rfl⟩
    obtain ⟨j, hj⟩ := not_forall.mp hbad
    apply Ideal.mem_sup_right
    apply Ideal.mem_iSup_of_mem j
    by_cases hlo : α j ≤ I.val j
    · apply Ideal.mem_sup_left
      apply Ideal.subset_span
      refine ⟨I, ?_, rfl⟩
      apply (upper_flag_failure_iff_selected_columns I j (β j)).mp
      exact lt_of_not_ge (fun hhi ↦ hj ⟨hlo, hhi⟩)
    · apply Ideal.mem_sup_right
      apply Ideal.subset_span
      exact ⟨I, (lower_flag_failure_iff_selected_columns I j (α j)).mp
        (lt_of_not_ge hlo), rfl⟩
  · apply sup_le le_sup_left
    apply iSup_le
    intro j
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro z ⟨I, he, rfl⟩
      apply Ideal.mem_sup_right
      apply Ideal.subset_span
      refine ⟨I, ?_, rfl⟩
      intro h
      exact (not_lt_of_ge (h j).2)
        ((upper_flag_failure_iff_selected_columns I j (β j)).mpr he)
    · apply Ideal.span_le.mpr
      rintro z ⟨I, he, rfl⟩
      apply Ideal.mem_sup_right
      apply Ideal.subset_span
      refine ⟨I, ?_, rfl⟩
      intro h
      exact (not_lt_of_ge (h j).1)
        ((lower_flag_failure_iff_selected_columns I j (α j)).mpr he)

/-- The genuine determinantal equations defining opposite Schubert rank
conditions agree with the original interval ideal on every normalized
Grassmannian chart.  This is equality of ideals, not just of zero sets. -/
theorem intervalPluckerIdeal_map_eq_richardsonChartRankIdeal
    (A : Matrix (Fin s) (Fin n) R) (p : Fin s → Fin n)
    (hp : A.submatrix id p = 1) (α β : Fin s → Fin n) :
    (intervalPluckerIdeal (K := K) α β).map (matrixMinorEvaluation A).toRingHom =
      richardsonChartRankIdeal A α β := by
  have hgrass : (matrixPluckerIdeal (K := K) (s := s) (n := n)).map
      (matrixMinorEvaluation A).toRingHom = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr (matrixPluckerIdeal_le_matrixMinorKernel A)
  rw [intervalPluckerIdeal_eq_flag_coordinates, Ideal.map_sup, hgrass,
    bot_sup_eq, Ideal.map_iSup]
  unfold richardsonChartRankIdeal
  congr 1
  funext j
  rw [Ideal.map_sup,
    ← fullRestrictedMinorIdeal_eq_map_selectedPluckerIdeal,
    ← fullRestrictedMinorIdeal_eq_map_selectedPluckerIdeal,
    ← restrictedMinorIdeal_eq_fullRestrictedMinorIdeal_of_le A p hp _ (Nat.sub_le _ _),
    ← restrictedMinorIdeal_eq_fullRestrictedMinorIdeal_of_le A p hp _
      (Nat.succ_le_of_lt j.isLt)]

end PaperVerification.AlternatingForms
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.RichardsonChartIdeals"


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
    (`PaperVerification.AlternatingForms.upper_flag_failure_iff_selected_columns, "theorem"),
    (`PaperVerification.AlternatingForms.lower_flag_failure_iff_selected_columns, "theorem"),
    (`PaperVerification.AlternatingForms.selectedPluckerIdeal, "definition"),
    (`PaperVerification.AlternatingForms.fullRestrictedMinorIdeal_eq_map_selectedPluckerIdeal, "theorem"),
    (`PaperVerification.AlternatingForms.richardsonChartRankIdeal, "definition"),
    (`PaperVerification.AlternatingForms.intervalPluckerIdeal_eq_flag_coordinates, "theorem"),
    (`PaperVerification.AlternatingForms.intervalPluckerIdeal_map_eq_richardsonChartRankIdeal, "theorem")
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
    ("nonce", toJson "deef32856dd957489e8ba7c452a137eb"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:deef32856dd957489e8ba7c452a137eb"
