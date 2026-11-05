module

public import PaperVerification.IsotropicAttractingChartRings

/-!
# The original homogeneous coordinates cut out the attracting cells

Order the Plücker coordinates by the sum of their column indices.  On the
chart with pivot `p`, vanishing of every smaller-weight minor is exactly
the row-echelon condition.  Every different minor of equal weight also
vanishes there.  Thus the explicit affine cells are the strata of the
actual homogeneous-coordinate filtration on the original projective
scheme, rather than merely an abstract disjoint family of affine schemes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCharts

open MvPolynomial
open PaperVerification.AlternatingForms
open PaperVerification.IsotropicAttractingCoordinates
open scoped BigOperators

variable {K : Type*} [Field K] {s n : ℕ}

/-- The character of the original Plücker coordinate for the chain torus. -/
def pluckerWeight (p : PluckerIndex s n) : ℕ := ∑ i, (p.val i).val

theorem pluckerWeight_lt_of_le_ne (p I : PluckerIndex s n)
    (hle : ∀ i, p.val i ≤ I.val i) (hne : p ≠ I) : pluckerWeight p < pluckerWeight I := by
  have hstrict : ∃ i, (p.val i).val < (I.val i).val := by
    by_contra h
    push Not at h
    apply hne
    apply Subtype.ext
    funext i
    exact Fin.ext (Nat.le_antisymm (hle i) (h i))
  obtain ⟨i, hi⟩ := hstrict
  exact Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hi⟩

/-- An echelon matrix has no nonpivot minor of weight at most that of
its pivot.  The argument uses the genuine determinant expansion. -/
theorem echelon_minor_eq_zero (p I : PluckerIndex s n)
    (hw : pluckerWeight I ≤ pluckerWeight p) (hne : p ≠ I) :
    Matrix.det (Matrix.of (fun i j : Fin s =>
      row (R := K) (indexEmbedding p) i (I.val j))) = 0 := by
  classical
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  have hmiss : ∃ i, ¬ p.val (σ i) ≤ I.val i := by
    by_contra h
    have hall : ∀ i, p.val (σ i) ≤ I.val i := by
      intro i
      exact not_not.mp (not_exists.mp h i)
    have hdiag := monotone_matching_lower p.val I.val p.property.monotone I.property.monotone σ hall
    exact (not_lt_of_ge hw) (pluckerWeight_lt_of_le_ne p I hdiag hne)
  obtain ⟨i, hi⟩ := hmiss
  have hz : (∏ j, row (R := K) (indexEmbedding p) (σ j) (I.val j)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact row_eq_zero_of_lt (indexEmbedding p) (σ i) (I.val i) (lt_of_not_ge hi)
  simp only [Matrix.of_apply, hz, smul_zero]

theorem fullChartRestriction_minor (p I : PluckerIndex s n) :
    fullChartRestriction (K := K) p
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p) (X I)) =
      Matrix.det (Matrix.of (fun i j : Fin s => row (R := K) (indexEmbedding p) i (I.val j))) := by
  rw [matrixMinorEvaluation, aeval_X, AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  exact fullChartRestriction_matrix (K := K) p i (I.val j)

def earlyMinorIdeal (p : PluckerIndex s n) : Ideal (MvPolynomial (PluckerChartVariable p) K) :=
  Ideal.span {f : MvPolynomial (PluckerChartVariable p) K |
    ∃ I : PluckerIndex s n, pluckerWeight I < pluckerWeight p ∧
    f = matrixMinorEvaluation (K := K) (pluckerChartMatrix p) (X I)}

theorem earlyMinorIdeal_le_kernel (p : PluckerIndex s n) :
    earlyMinorIdeal (K := K) p ≤ RingHom.ker (fullChartRestriction p).toRingHom := by
  apply Ideal.span_le.mpr
  rintro f ⟨I, hw, rfl⟩
  change fullChartRestriction p (matrixMinorEvaluation (pluckerChartMatrix p) (X I)) = 0
  rw [fullChartRestriction_minor]
  exact echelon_minor_eq_zero p I (Nat.le_of_lt hw) (fun he => by simpa [he] using hw)

theorem update_columns_injective (p : PluckerIndex s n) (i : Fin s) (j : Fin n)
    (hj : j ∉ Set.range p.val) : Function.Injective (Function.update p.val i j) := by
  intro a b hab
  by_cases ha : a = i
  · subst a
    by_cases hb : b = i
    · exact hb.symm
    · simp only [Function.update_self, Function.update_of_ne hb] at hab
      exact False.elim (hj ⟨b, hab.symm⟩)
  · by_cases hb : b = i
    · subst b
      simp only [Function.update_self, Function.update_of_ne ha] at hab
      exact False.elim (hj ⟨a, hab⟩)
    · simp only [Function.update_of_ne ha, Function.update_of_ne hb] at hab
      exact p.property.injective hab

theorem sortedPluckerWeight (I : Fin s → Fin n) (hI : Function.Injective I) :
    pluckerWeight (sortedPluckerIndex I hI) = ∑ i, (I i).val :=
  Equiv.sum_comp (Tuple.sort I) (fun i => (I i).val)

/-- A left-of-pivot entry is represented by a strictly earlier genuine
Plücker coordinate, after sorting its replacement column. -/
theorem replacement_weight_lt (p : PluckerIndex s n) (i : Fin s) (j : Fin n)
    (hj : j ∉ Set.range p.val) (hlt : j < p.val i) :
    pluckerWeight (sortedPluckerIndex (Function.update p.val i j)
      (update_columns_injective p i j hj)) < pluckerWeight p := by
  classical
  rw [sortedPluckerWeight]
  apply Finset.sum_lt_sum
  · intro a _
    by_cases ha : a = i
    · subst a
      simpa only [Function.update_self] using Nat.le_of_lt hlt
    · simp [Function.update_of_ne ha]
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    simp only [Function.update_self]
    exact show j.val < (p.val i).val from hlt

theorem cramerCoordinate_mem_early (p : PluckerIndex s n) (i : Fin s) (j : Fin n)
    (hj : j ∉ Set.range p.val) (hlt : j < p.val i) :
    matrixMinorEvaluation (K := K) (pluckerChartMatrix p) (cramerPluckerCoordinate p i j)
      ∈ earlyMinorIdeal (K := K) p := by
  classical
  let hi := update_columns_injective p i j hj
  rw [cramerPluckerCoordinate, orderedPluckerCoordinate, dite_eq_left hi, map_smul,
    Algebra.smul_def]
  apply Ideal.mul_mem_left
  exact Ideal.subset_span ⟨sortedPluckerIndex (Function.update p.val i j) hi,
    replacement_weight_lt p i j hj hlt, rfl⟩

/-- The global homogeneous vanishing conditions induce exactly the
original coordinate ideal of the cell in the pivot affine chart. -/
theorem earlyMinorIdeal_eq_negativeCoordinates (p : PluckerIndex s n) :
    earlyMinorIdeal (K := K) p = Ideal.span (X '' negativeCoordinates p) := by
  apply le_antisymm
  · rw [← fullChartRestriction_kernel]
    exact earlyMinorIdeal_le_kernel p
  · apply Ideal.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    have hne : v.2.val ≠ p.val v.1 := fun h => v.2.property ⟨v.1, h.symm⟩
    have hlt : v.2.val < p.val v.1 := by
      have hnot : ¬ (p.val v.1).val < v.2.val.val := hv
      exact lt_of_le_of_ne (Nat.le_of_not_gt hnot) hne
    have hm := cramerCoordinate_mem_early (K := K) p v.1 v.2.val v.2.property hlt
    rw [matrixMinorEvaluation_cramer, pluckerChartMatrix_pivot, Matrix.cramer_one] at hm
    change pluckerChartMatrix (K := K) p v.1 v.2.val ∈ earlyMinorIdeal p at hm
    rw [pluckerChartMatrix_nonpivot] at hm
    exact hm

/-- Equal-weight coordinates other than the pivot vanish on the same
scheme-theoretic cell; this ensures the frontier has strictly larger
Plücker weight and permits any tie-breaking order in the filtration. -/
theorem nonpivot_low_minor_mem_early (p I : PluckerIndex s n)
    (hw : pluckerWeight I ≤ pluckerWeight p) (hne : p ≠ I) :
    matrixMinorEvaluation (K := K) (pluckerChartMatrix p) (X I) ∈ earlyMinorIdeal (K := K) p := by
  rw [earlyMinorIdeal_eq_negativeCoordinates, ← fullChartRestriction_kernel]
  change fullChartRestriction p (matrixMinorEvaluation (pluckerChartMatrix p) (X I)) = 0
  rw [fullChartRestriction_minor]
  exact echelon_minor_eq_zero p I hw hne

end PaperVerification.IsotropicAttractingCharts
