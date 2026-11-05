module

public import Ellipsoid.GSZFormula
public import Ellipsoid.CoefficientInjectivity

@[expose] public section

noncomputable section

open Polynomial Set
open scoped BigOperators

namespace EllipsoidVerification

theorem axisCoefficients_zero {n : ℕ} (a : Fin n → ℝ) : axisCoefficients a 0 = 1 := by
  simp [axisCoefficients, axisCoefficientPolynomial, Polynomial.coeff_zero_prod]

theorem axisCoefficients_last {n : ℕ} (a : Fin n → ℝ) :
    axisCoefficients a (Fin.last n) = (∏ i, a i) ^ 2 := by
  have h := Polynomial.coeff_prod_of_natDegree_le (s := Finset.univ)
    (fun i : Fin n => 1 + C (a i ^ 2) * X) 1 (fun i hi => by
      apply Polynomial.natDegree_add_le_of_degree_le (by simp)
      exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp))
  simp only [Finset.card_univ, Fintype.card_fin, mul_one, Polynomial.coeff_add,
    Polynomial.coeff_one, Polynomial.coeff_C_mul_X, one_ne_zero, if_false, if_true,
    zero_add] at h
  simpa only [axisCoefficients, axisCoefficientPolynomial, Fin.val_last, Finset.prod_pow] using h

def internalCoefficients (m : ℕ) (e : Coefficients (m + 1)) : Fin m → ℝ :=
  fun i => e ⟨i.val + 1, by omega⟩

theorem fixedEndpoints_internalCoefficients (m : ℕ) (e : Coefficients (m + 1)) :
    fixedEndpoints m (e 0) (e (Fin.last (m + 1))) (internalCoefficients m e) = e := by
  funext j
  unfold fixedEndpoints
  split_ifs with h0 hn
  · congr 1
    exact Fin.ext h0.symm
  · congr 1
    exact Fin.ext hn.symm
  · dsimp [internalCoefficients]
    exact congrArg e (Fin.ext (show j.val - 1 + 1 = j.val by omega))

theorem axisPolynomial_eq_of_axisCoefficients_eq {n : ℕ} {a b : Fin n → ℝ}
    (h : axisCoefficients a = axisCoefficients b) :
    axisCoefficientPolynomial a = axisCoefficientPolynomial b := by
  apply Polynomial.ext
  intro k
  by_cases hk : k ≤ n
  · exact congrFun h ⟨k, by omega⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      ((axisCoefficientPolynomial_natDegree_le a).trans_lt (lt_of_not_ge hk)),
      Polynomial.coeff_eq_zero_of_natDegree_lt
      ((axisCoefficientPolynomial_natDegree_le b).trans_lt (lt_of_not_ge hk))]

/-- The exact principal reconstruction theorem. The intrinsic volumes are
the coefficients of the actual parallel-body volumes, and the conclusion is
an actual Euclidean isometry between the ellipsoid bodies. -/
theorem intrinsic_reconstruction : IntrinsicReconstruction := by
  intro n E F hV
  cases n with
  | zero =>
      exact E.congruent_of_semiaxes_perm F (Equiv.refl _) (fun i => Fin.elim0 i)
  | succ m =>
      let e := axisCoefficients E.semiaxis
      let f := axisCoefficients F.semiaxis
      have he := axisCoefficients_admissible E.semiaxis E.semiaxis_pos
      have hf := axisCoefficients_admissible F.semiaxis F.semiaxis_pos
      have hprod : (∏ i, E.semiaxis i) = ∏ i, F.semiaxis i := by
        have h := hV (m + 1) (by omega) le_rfl
        rw [E.volume_top (by omega), F.volume_top (by omega)] at h
        exact mul_left_cancel₀ (unitBallVolume_pos (m + 1)).ne' h
      have hen : e (Fin.last (m + 1)) = f (Fin.last (m + 1)) := by
        simp only [e, f, axisCoefficients_last, hprod]
      have he0 : e 0 = 1 := axisCoefficients_zero _
      have hf0 : f 0 = 1 := axisCoefficients_zero _
      let x := internalCoefficients m e
      let y := internalCoefficients m f
      have hx : (0 : Fin m → ℝ) ≤ x := fun i => he.1 _
      have hy : (0 : Fin m → ℝ) ≤ y := fun i => hf.1 _
      have hxe : fixedEndpoints m 1 (e (Fin.last (m + 1))) x = e := by
        simpa only [he0] using fixedEndpoints_internalCoefficients m e
      have hyf : fixedEndpoints m 1 (e (Fin.last (m + 1))) y = f := by
        simpa only [hf0, hen] using fixedEndpoints_internalCoefficients m f
      have hxy : coefficientMap m 1 (e (Fin.last (m + 1))) x =
          coefficientMap m 1 (e (Fin.last (m + 1))) y := by
        funext k
        have h := hV (k.val + 1) (by omega) (by omega)
        rw [E.volume_eq_coefficientTransform (by omega) (by omega),
          F.volume_eq_coefficientTransform (by omega) (by omega)] at h
        simpa only [coefficientMap, hxe, hyf, e, f] using
          mul_left_cancel₀ (unitBallVolume_pos (k.val + 1)).ne' h
      have hcoordinates := coefficientMap_injOn_nonnegative (m := m) (by norm_num)
        he.2.2 hx hy hxy
      have hef : e = f := by
        rw [← hxe, ← hyf, hcoordinates]
      exact E.congruent_of_axisPolynomial_eq F (axisPolynomial_eq_of_axisCoefficients_eq hef)

end EllipsoidVerification
