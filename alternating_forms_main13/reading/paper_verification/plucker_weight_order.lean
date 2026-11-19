module

public import PaperVerification.IsotropicAttractingNormalizedFiltration

/-!
# A finite order refining the genuine Plücker weights

This is only the combinatorial indexing of the closed filtration.  Every
Plücker coordinate occurs exactly once, and its predecessor set satisfies
the hypotheses already used to identify the actual affine stratum.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCharts

open PaperVerification.AlternatingForms

variable (s n : ℕ)

abbrev pivotCount := Fintype.card (PluckerIndex s n)

/-- Sort one enumeration by weight; no numerical tie-breaking assumption
is needed by the determinant proof. -/
def weightOrderedPivots : Fin (pivotCount s n) ≃ PluckerIndex s n :=
  (Tuple.sort (fun i : Fin (pivotCount s n) =>
    pluckerWeight ((Fintype.equivFin (PluckerIndex s n)).symm i))).trans
      (Fintype.equivFin (PluckerIndex s n)).symm

theorem weightOrderedPivots_monotone :
    Monotone (fun i => pluckerWeight (weightOrderedPivots s n i)) := by
  intro i j hij
  have h := (Tuple.monotone_sort (fun i : Fin (pivotCount s n) =>
    pluckerWeight ((Fintype.equivFin (PluckerIndex s n)).symm i))) hij
  exact h

/-- The literal original coordinates eliminated at the m-th stage. -/
def pivotPrefix (m : ℕ) : Set (PluckerIndex s n) :=
  {I | ((weightOrderedPivots s n).symm I).val < m}

@[simp] theorem pivotPrefix_zero : pivotPrefix s n 0 = ∅ := by
  ext I
  simp [pivotPrefix]

@[simp] theorem pivotPrefix_all : pivotPrefix s n (pivotCount s n) = Set.univ := by
  ext I
  simp only [pivotPrefix, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact ((weightOrderedPivots s n).symm I).isLt

theorem pivotPrefix_mono : Monotone (pivotPrefix s n) := by
  intro a b hab I hI
  exact lt_of_lt_of_le hI hab

theorem pivotPrefix_successor (i : Fin (pivotCount s n)) :
    pivotPrefix s n (i.val+1) = insert (weightOrderedPivots s n i)
      (pivotPrefix s n i.val) := by
  ext I
  change ((weightOrderedPivots s n).symm I).val < i.val+1 ↔
    I = weightOrderedPivots s n i ∨ ((weightOrderedPivots s n).symm I).val < i.val
  constructor
  · intro h
    by_cases he : ((weightOrderedPivots s n).symm I).val = i.val
    · left
      apply (weightOrderedPivots s n).symm.injective
      simpa only [Equiv.symm_apply_apply] using Fin.ext he
    · right
      omega
  · rintro (rfl | h)
    · simp
    · omega

/-- Exactly the weight-refinement properties needed by the genuine
normalized-filtration coordinate-ring theorem. -/
theorem pivotPrefix_earlier (i : Fin (pivotCount s n)) :
    EarlierSet (weightOrderedPivots s n i) (pivotPrefix s n i.val) := by
  constructor
  · intro I hI
    change ((weightOrderedPivots s n).symm I).val < i.val
    by_contra h
    have hi : i ≤ (weightOrderedPivots s n).symm I := Nat.le_of_not_gt h
    have hw := weightOrderedPivots_monotone s n hi
    change pluckerWeight (weightOrderedPivots s n i) ≤
      pluckerWeight (weightOrderedPivots s n ((weightOrderedPivots s n).symm I)) at hw
    rw [Equiv.apply_symm_apply] at hw
    exact (not_lt_of_ge hw) hI
  · intro I hI
    have hi : (weightOrderedPivots s n).symm I < i := hI
    constructor
    · have hw := weightOrderedPivots_monotone s n (le_of_lt hi)
      simpa only [Equiv.apply_symm_apply] using hw
    · intro he
      have hv := congrArg (weightOrderedPivots s n).symm he
      rw [Equiv.symm_apply_apply] at hv
      exact (ne_of_lt hi) hv.symm

end PaperVerification.IsotropicAttractingCharts
