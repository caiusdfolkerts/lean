module

public import PaperVerification.SchubertRankIdeals
public import PaperVerification.SchubertFlagIndices

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
