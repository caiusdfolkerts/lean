module

public import PaperVerification.FermionNewtonMomentComparison
public import PaperVerification.FermionFilteredRegularityLift
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The genuine monic deformations of the Newton contractions

All sums use the actual coefficients of the given monic polynomial. A
negative signed height contributes the zero polynomial, by monic division.
The actual top homogeneous components and regularity are proved rather
than supplied as deformation assumptions.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

/-- Monic division has no polynomial part at a negative signed height. -/
theorem columnContraction_eq_zero_of_negative_height
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i : Fin n)
    (hi : δ i + (earlierPositive σ i).card < (earlierNegative σ i).card) :
    columnContraction β δ σ i = 0 := by
  have hz : columnPolynomialPart (F := F) δ σ i = 0 := by
    apply (Polynomial.divByMonic_eq_zero_iff (columnDenominator_monic σ i)).mpr
    rw [Polynomial.degree_eq_natDegree (columnNumerator_monic δ σ i).ne_zero,
      Polynomial.degree_eq_natDegree (columnDenominator_monic σ i).ne_zero,
      columnNumerator_natDegree, columnDenominator_natDegree]
    exact_mod_cast hi
  simp only [columnContraction, hz, Polynomial.eval_zero, mul_zero, Finset.sum_const_zero]

/-- The truncated natural height is harmless even at negative integer height,
because in that case the actual contraction vanishes. -/
theorem constant_columnContraction_homogeneous
    (β : Fin n → F) (d : ℕ) (σ : Fin n → ℤ)
    (hβ : ∀ k, β k ≠ 0) (i : Fin n) :
    (columnContraction β (fun _ ↦ d) σ i).IsHomogeneous
      (heightDegree (fun _ ↦ d) σ i) := by
  by_cases hi : (earlierNegative σ i).card ≤ d + (earlierPositive σ i).card
  · exact columnContraction_homogeneous β (fun _ ↦ d) σ
      (compatible_constant d σ) hβ i hi
  · rw [columnContraction_eq_zero_of_negative_height β (fun _ ↦ d) σ i (by omega)]
    exact isHomogeneous_zero (Fin n) F _

/-- Apply the coefficients of a one-variable polynomial to an actual family
of multivariable polynomials. -/
def coefficientCombination (G : Polynomial F) (v : ℕ → P (F := F) (n := n)) :
    P (F := F) (n := n) :=
  ∑ d ∈ Finset.range (G.natDegree + 1), C (G.coeff d) * v d

theorem coefficientCombination_bound
    (G : Polynomial F) (v : ℕ → P (F := F) (n := n)) (degree : ℕ → ℕ)
    (hv : ∀ d, (v d).IsHomogeneous (degree d))
    (hle : ∀ d ≤ G.natDegree, degree d ≤ degree G.natDegree) :
    Filtered.Bound (fun _ ↦ 1) (degree G.natDegree) (coefficientCombination G v) := by
  apply Filtered.bound_sum (fun _ ↦ 1) (Finset.range (G.natDegree + 1)) _ _
  intro d hd
  exact (Filtered.homogeneous_bound (fun _ ↦ 1) ((hv d).C_mul (G.coeff d))).mono _
    (hle d (by have := Finset.mem_range.mp hd; omega))

theorem coefficientCombination_highest
    (G : Polynomial F) (hG : G.Monic) (v : ℕ → P (F := F) (n := n))
    (degree : ℕ → ℕ) (hv : ∀ d, (v d).IsHomogeneous (degree d))
    (hlt : ∀ d < G.natDegree, degree d < degree G.natDegree) :
    weightedHomogeneousComponent (fun _ ↦ 1) (degree G.natDegree)
      (coefficientCombination G v) = v G.natDegree := by
  unfold coefficientCombination
  rw [Finset.sum_range_succ, hG.coeff_natDegree, map_one, one_mul, map_add]
  have htop : weightedHomogeneousComponent (fun _ : Fin n ↦ 1)
      (degree G.natDegree) (v G.natDegree) = v G.natDegree := by
    simpa only [Pi.one_def] using weightedHomogeneousComponent_eq_self (hv G.natDegree)
  rw [htop]
  have hz : weightedHomogeneousComponent (fun _ ↦ 1) (degree G.natDegree)
      (∑ d ∈ Finset.range G.natDegree, C (G.coeff d) * v d) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro d hd
    apply Filtered.component_zero_of_strict
    intro u hu
    have hh : (C (G.coeff d) * v d).IsWeightedHomogeneous
        (fun _ : Fin n ↦ 1) (degree d) := by
      simpa only [IsHomogeneous, Pi.one_def] using (hv d).C_mul (G.coeff d)
    have he := hh hu
    rw [he]
    exact hlt d (Finset.mem_range.mp hd)
  rw [hz, zero_add]

/-- An explicit sequence, formed from all coefficients of `G`. -/
def polynomialContraction (β : Fin n → F) (G : Polynomial F) (σ : Fin n → ℤ)
    (i : Fin n) : P (F := F) (n := n) :=
  coefficientCombination G (fun d ↦ columnContraction β (fun _ ↦ d) σ i)

/-- The actual moments in the original polynomial ring. -/
def polynomialMoment (β : Fin n → F) (G : Polynomial F) (j : ℕ) :
    P (F := F) (n := n) :=
  ∑ k, C (β k) * G.eval₂ C (X k) * X k ^ j

def polynomialMomentIdeal (β : Fin n → F) (G : Polynomial F) :
    Ideal (P (F := F) (n := n)) :=
  Ideal.span (Set.range (fun j : Fin n ↦ polynomialMoment β G j))

theorem polynomialMoment_eq_coefficientCombination
    (β : Fin n → F) (G : Polynomial F) (j : ℕ) :
    polynomialMoment β G j = coefficientCombination G (fun d ↦ powerMoment (fun _ ↦ 1) β d j) := by
  classical
  simp only [polynomialMoment, Polynomial.eval₂_eq_sum_range, coefficientCombination,
    powerMoment, one_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_add]
  ring

theorem powerMoment_one_homogeneous (β : Fin n → F) (d j : ℕ) :
    (powerMoment (fun _ ↦ 1) β d j).IsHomogeneous (d + j) := by
  apply IsHomogeneous.sum
  intro k hk
  simpa only [one_mul] using ((isHomogeneous_X F k).pow (d + j)).C_mul (β k)

theorem polynomialMoment_bound (β : Fin n → F) (G : Polynomial F) (j : ℕ) :
    Filtered.Bound (fun _ ↦ 1) (G.natDegree + j) (polynomialMoment β G j) := by
  rw [polynomialMoment_eq_coefficientCombination]
  exact coefficientCombination_bound G _ (fun d ↦ d + j)
    (fun d ↦ powerMoment_one_homogeneous β d j) (fun d hd ↦ by omega)

theorem polynomialMoment_highest (β : Fin n → F) (G : Polynomial F)
    (hG : G.Monic) (j : ℕ) :
    weightedHomogeneousComponent (fun _ ↦ 1) (G.natDegree + j) (polynomialMoment β G j) =
      powerMoment (fun _ ↦ 1) β G.natDegree j := by
  rw [polynomialMoment_eq_coefficientCombination]
  exact coefficientCombination_highest G hG _ (fun d ↦ d + j)
    (fun d ↦ powerMoment_one_homogeneous β d j) (fun d hd ↦ by omega)

theorem polynomialContraction_bound (β : Fin n → F) (G : Polynomial F) (σ : Fin n → ℤ)
    (hβ : ∀ k, β k ≠ 0) (i : Fin n) :
    Filtered.Bound (fun _ ↦ 1) (heightDegree (fun _ ↦ G.natDegree) σ i)
      (polynomialContraction β G σ i) := by
  apply coefficientCombination_bound G _ (fun d ↦ heightDegree (fun _ ↦ d) σ i)
  · intro d
    exact constant_columnContraction_homogeneous β d σ hβ i
  · intro d hd
    dsimp only [heightDegree]
    omega

theorem polynomialContraction_highest (β : Fin n → F) (G : Polynomial F) (hG : G.Monic)
    (σ : Fin n → ℤ) (hβ : ∀ k, β k ≠ 0) (i : Fin n)
    (hi : 0 < heightDegree (fun _ ↦ G.natDegree) σ i) :
    weightedHomogeneousComponent (fun _ ↦ 1) (heightDegree (fun _ ↦ G.natDegree) σ i)
      (polynomialContraction β G σ i) = columnContraction β (fun _ ↦ G.natDegree) σ i := by
  apply coefficientCombination_highest G hG _ (fun d ↦ heightDegree (fun _ ↦ d) σ i)
  · intro d
    exact constant_columnContraction_homogeneous β d σ hβ i
  · intro d hd
    dsimp only [heightDegree] at *
    omega

theorem polynomialMoments_isWeaklyRegular
    (β : Fin n → F) (G : Polynomial F) (hG : G.Monic) (hs : 0 < G.natDegree)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    RingTheory.Sequence.IsWeaklyRegular (P (F := F) (n := n))
      (List.ofFn (fun j : Fin n ↦ polynomialMoment β G j)) := by
  exact Filtered.weaklyRegular_of_regular_highest (fun _ ↦ 1)
    (fun j : Fin n ↦ polynomialMoment β G j)
    (fun j : Fin n ↦ powerMoment (fun _ ↦ 1) β G.natDegree j)
    (fun j ↦ G.natDegree + j.val) (fun j ↦ polynomialMoment_bound β G j)
    (fun j ↦ polynomialMoment_highest β G hG j)
    (powerMoments_isWeaklyRegular (fun _ ↦ 1) β G.natDegree (by simp) hs hβ)

theorem polynomialContractions_isWeaklyRegular
    (β : Fin n → F) (G : Polynomial F) (hG : G.Monic) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight (fun _ ↦ G.natDegree) σ i) :
    RingTheory.Sequence.IsWeaklyRegular (P (F := F) (n := n))
      (List.ofFn (polynomialContraction β G σ)) := by
  exact Filtered.weaklyRegular_of_regular_highest (fun _ ↦ 1)
    (polynomialContraction β G σ) (columnContraction β (fun _ ↦ G.natDegree) σ)
    (heightDegree (fun _ ↦ G.natDegree) σ)
    (fun i ↦ polynomialContraction_bound β G σ (singleton_weight_ne_zero β hβ) i)
    (fun i ↦ polynomialContraction_highest β G hG σ (singleton_weight_ne_zero β hβ) i
      (heightDegree_pos (fun _ ↦ G.natDegree) σ hσ i (hheight i)))
    (columnContractions_isWeaklyRegular β (fun _ ↦ G.natDegree) σ
      (compatible_constant G.natDegree σ) hσ hβ hheight)

end PaperVerification.Fermion.Newton
