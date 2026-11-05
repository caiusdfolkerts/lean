module

public import PaperVerification.AlternatingFormsUniversalMinors
public import Mathlib.Order.Interval.Finset.Fin
public import Lean.Elab.Tactic.Omega

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
