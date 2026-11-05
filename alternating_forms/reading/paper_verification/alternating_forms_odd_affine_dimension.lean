module

public import PaperVerification.AlternatingFormsOddRationality

/-!
# The number of coordinates in the odd rational chart

The remaining columns are exactly those numbered at least `2*r+1` in the
zero-based path convention.  Their entries form a rectangular array with
`r+1` rows and `2*(k-r)` columns.  The resulting birationality witness has
precisely the paper's dimension `2*s*(k+1-s)`, where `s=r+1`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

private theorem oddAffine_free_column_ge (k r : ℕ) (h : r ≤ k)
    (j : Fin (2*k+1)) (hnp : j ∉ Set.range (oddAffinePivot k r h).val)
    (hnh : ¬oddAffineIsHead r j) : 2*r+1 ≤ j.val := by
  by_contra hj
  by_cases heven : j.val % 2 = 0
  · apply hnp
    refine ⟨⟨j.val/2, by omega⟩, ?_⟩
    apply Fin.ext
    change 2 * (j.val / 2) = j.val
    omega
  · apply hnh
    exact ⟨by omega, by omega⟩

/-- The free chart entries are literally a rectangular array. -/
def oddAffineFreeVariableEquiv (k r : ℕ) (h : r ≤ k) :
    OddAffineFreeVariable k r h ≃ Fin (r+1) × Fin (2*(k-r)) where
  toFun a := (a.val.1, ⟨a.val.2.val.val - (2*r+1), by
    have ht := oddAffine_free_column_ge k r h a.val.2.val a.val.2.property a.property
    have hj := a.val.2.val.isLt
    omega⟩)
  invFun a := ⟨(a.1, ⟨⟨2*r+1+a.2.val, by have := a.2.isLt; omega⟩, by
    rintro ⟨i, hi⟩
    have hi' := congrArg Fin.val hi
    change 2*i.val = 2*r+1+a.2.val at hi'
    have := i.isLt
    omega⟩), by
      intro hh
      have := hh.2
      change (2*r+1+a.2.val)/2 < r at this
      omega⟩
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Fin.ext
      have ht := oddAffine_free_column_ge k r h a.val.2.val a.val.2.property a.property
      dsimp only
      omega
  right_inv a := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      dsimp only
      omega

/-- The chart has the full expected number of independent polynomial variables. -/
theorem card_oddAffineFreeVariable (k r : ℕ) (h : r ≤ k) :
    Fintype.card (OddAffineFreeVariable k r h) = 2*(r+1)*(k-r) := by
  rw [Fintype.card_congr (oddAffineFreeVariableEquiv k r h),
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  ring

variable {K : Type} [Field K] [CharZero K]

/-- Rationality with a finite affine witness of exactly the paper's dimension.
The morphisms still commute with the original structure map to `Spec K`. -/
theorem paper_theorem_4_1_rationality_with_dimension_at_least_two
    (k t : ℕ) (h : t+1 ≤ k) :
    ∃ N : Type, Finite N ∧ Nat.card N = 2*(t+2)*(k-(t+1)) ∧ Scheme.BirationalOver
      (isotropicStructureMap (t := t) (oddPluckerForms (K := K) k))
      (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
  refine ⟨OddAffineFreeVariable k (t+1) h, inferInstance, ?_, ?_⟩
  · simpa only [Nat.card_eq_fintype_card, Nat.add_assoc] using
      card_oddAffineFreeVariable k (t+1) h
  · exact scheme_birationalOver_affine_of_dense_chart _ _
      (oddIsotropicBigCell_dense k t h) (OddAffineFreeVariable k (t+1) h)
      (oddIsotropicBigCellAffineIso k t h) (oddIsotropicBigCellAffineIso_over k t h)

end PaperVerification.AlternatingForms
