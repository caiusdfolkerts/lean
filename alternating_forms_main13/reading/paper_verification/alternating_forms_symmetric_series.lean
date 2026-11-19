module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Basic
public import TauCeti.RingTheory.PowerSeries.Geometric
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic.Ring

/-!
# The actual complete-symmetric and first-variation series

The first variation in Section 4 is a partial derivative of the ordinary complete
homogeneous symmetric polynomial.  This file retains that definition and proves
its generating-function formula.  Coefficientwise differentiation is justified by
the finite convolution formula for multiplication of formal power series.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open Finset

section CoefficientDerivation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A derivation of the coefficient ring extends coefficientwise to formal power
series.  This differentiates coefficients, leaving the formal variable fixed. -/
noncomputable def coefficientDerivation (D : Derivation R A A) :
    Derivation R (PowerSeries A) (PowerSeries A) where
  toFun f := PowerSeries.mk fun n => D (PowerSeries.coeff n f)
  map_add' f g := by ext n; simp
  map_smul' a f := by ext n; simp [PowerSeries.coeff_smul]
  map_one_eq_zero' := by
    ext n
    by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]
  leibniz' f g := by
    change PowerSeries.mk (fun n => D (PowerSeries.coeff n (f * g))) =
      f * PowerSeries.mk (fun n => D (PowerSeries.coeff n g)) +
        g * PowerSeries.mk (fun n => D (PowerSeries.coeff n f))
    rw [mul_comm g]
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, map_sum,
      Derivation.leibniz, smul_eq_mul, map_add, Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _

@[simp] theorem coeff_coefficientDerivation (D : Derivation R A A)
    (f : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (coefficientDerivation D f) = D (PowerSeries.coeff n f) :=
  by
    change PowerSeries.coeff n
      (PowerSeries.mk fun m => D (PowerSeries.coeff m f)) = D (PowerSeries.coeff n f)
    exact PowerSeries.coeff_mk n _

@[simp] theorem coefficientDerivation_C (D : Derivation R A A) (a : A) :
    coefficientDerivation D (PowerSeries.C a) = PowerSeries.C (D a) := by
  ext n
  simp only [coeff_coefficientDerivation, PowerSeries.coeff_C]
  split_ifs <;> simp

@[simp] theorem coefficientDerivation_X (D : Derivation R A A) :
    coefficientDerivation D PowerSeries.X = 0 := by
  ext n
  simp only [coeff_coefficientDerivation, PowerSeries.coeff_X, map_zero]
  split_ifs <;> simp

/-- Logarithmic differentiation of a finite product, using explicitly given
multiplicative inverses rather than a field of fractions. -/
theorem derivation_prod_inverse_formula {ι : Type*} [DecidableEq ι]
    (D : Derivation R A A) (S : Finset ι) (f g : ι → A)
    (hfg : ∀ i ∈ S, f i * g i = 1) :
    D (∏ i ∈ S, f i) = (∏ i ∈ S, f i) * ∑ i ∈ S, g i * D (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hfgS : ∀ i ∈ S, f i * g i = 1 := fun i hi => hfg i (by simp [hi])
    have hfgA := hfg a (by simp)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz,
      ih hfgS, smul_eq_mul, smul_eq_mul]
    calc
      f a * ((∏ i ∈ S, f i) * ∑ i ∈ S, g i * D (f i)) +
          (∏ i ∈ S, f i) * D (f a) =
        (f a * ∏ i ∈ S, f i) * (g a * D (f a) + ∑ i ∈ S, g i * D (f i)) := by
          rw [mul_add]
          have hcancel : (f a * ∏ i ∈ S, f i) * (g a * D (f a)) =
              (∏ i ∈ S, f i) * D (f a) := by
            calc
              _ = (f a * g a) * ((∏ i ∈ S, f i) * D (f a)) := by ring
              _ = _ := by rw [hfgA, one_mul]
          rw [hcancel]
          ring

/-- The geometric formal series with coefficient `a^n`. -/
noncomputable def geometricSeries (a : A) : PowerSeries A :=
  PowerSeries.mk fun n => a ^ n

@[simp] theorem geometricSeries_inverse (a : A) :
    geometricSeries a * (1 - PowerSeries.C a * PowerSeries.X) = 1 :=
  TauCeti.powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one a

/-- Coefficientwise differentiation of the geometric series. -/
theorem coefficientDerivation_geometric (D : Derivation R A A) (a : A) :
    coefficientDerivation D (geometricSeries a) =
      geometricSeries a ^ 2 * PowerSeries.C (D a) * PowerSeries.X := by
  rw [(coefficientDerivation D).leibniz_of_mul_eq_one (geometricSeries_inverse a)]
  simp only [map_sub, Derivation.map_one_eq_zero, Derivation.leibniz, coefficientDerivation_C,
    coefficientDerivation_X, smul_eq_mul, mul_zero, add_zero, zero_sub]
  ring

/-- The product of geometric series has the expected logarithmic derivative. -/
theorem coefficientDerivation_prod_geometric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Derivation R A A) (a : ι → A) :
    coefficientDerivation D (∏ i, geometricSeries (a i)) =
      (∏ i, geometricSeries (a i)) *
        ∑ i, geometricSeries (a i) * PowerSeries.C (D (a i)) * PowerSeries.X := by
  rw [derivation_prod_inverse_formula (coefficientDerivation D) Finset.univ
    (fun i => geometricSeries (a i))
    (fun i => 1 - PowerSeries.C (a i) * PowerSeries.X)
    (fun i _ => geometricSeries_inverse (a i))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficientDerivation_geometric]
  calc
    _ = (geometricSeries (a i) * (1 - PowerSeries.C (a i) * PowerSeries.X)) *
        (geometricSeries (a i) * PowerSeries.C (D (a i)) * PowerSeries.X) := by ring
    _ = _ := by rw [geometricSeries_inverse, one_mul]

end CoefficientDerivation

section CompleteSymmetric

variable {K σ : Type*} [CommRing K] [Fintype σ] [DecidableEq σ]

/-- The ordinary complete homogeneous symmetric polynomials, assembled into a
formal power series over their polynomial ring. -/
noncomputable def completeSymmetricSeries : PowerSeries (MvPolynomial σ K) :=
  PowerSeries.mk fun n => MvPolynomial.hsymm σ K n

theorem completeSymmetricSeries_eq_prod :
    completeSymmetricSeries (K := K) (σ := σ) =
      ∏ i, geometricSeries (MvPolynomial.X i : MvPolynomial σ K) :=
  TauCeti.mk_hsymm_eq_prod_mk_pow K

/-- The derivative identity for the actual Mathlib complete homogeneous
symmetric polynomials, valid without division or characteristic assumptions. -/
theorem pderiv_completeSymmetricSeries (i : σ) :
    coefficientDerivation (MvPolynomial.pderiv i)
        (completeSymmetricSeries (K := K) (σ := σ)) =
      PowerSeries.X * completeSymmetricSeries * geometricSeries (MvPolynomial.X i) := by
  rw [completeSymmetricSeries_eq_prod, coefficientDerivation_prod_geometric]
  have hsum : (∑ j : σ, geometricSeries (MvPolynomial.X j : MvPolynomial σ K) *
      PowerSeries.C ((MvPolynomial.pderiv i) (MvPolynomial.X j)) * PowerSeries.X) =
      geometricSeries (MvPolynomial.X i) * PowerSeries.X := by
    simp [MvPolynomial.pderiv_X, Pi.single_apply]
  rw [hsum]
  ring

/-- Complete homogeneous polynomials evaluated at an arbitrary family. -/
noncomputable def completeEvaluationSeries (y : σ → K) : PowerSeries K :=
  PowerSeries.mk fun n => MvPolynomial.eval y (MvPolynomial.hsymm σ K n)

/-- The first variation of the actual complete homogeneous polynomial. -/
noncomputable def firstVariationSeries (y z : σ → K) : PowerSeries K :=
  PowerSeries.mk fun n => ∑ i, z i *
    MvPolynomial.eval y (MvPolynomial.pderiv i (MvPolynomial.hsymm σ K n))

theorem map_completeSymmetricSeries (y : σ → K) :
    PowerSeries.map (MvPolynomial.eval y) (completeSymmetricSeries (K := K) (σ := σ)) =
      completeEvaluationSeries y := by
  ext n
  simp [completeSymmetricSeries, completeEvaluationSeries]

theorem map_geometricSeries {A : Type*} [CommRing A] (f : A →+* K) (a : A) :
    PowerSeries.map f (geometricSeries a) = geometricSeries (f a) := by
  ext n
  simp [geometricSeries]

theorem completeEvaluationSeries_eq_prod (y : σ → K) :
    completeEvaluationSeries y = ∏ i, geometricSeries (y i) := by
  rw [← map_completeSymmetricSeries, completeSymmetricSeries_eq_prod, map_prod]
  simp only [map_geometricSeries, MvPolynomial.eval_X]

/-- The generating formula for the paper's first variations.  After replacing
`t` by `t²` and dividing the zero-constant series by `t`, this is its odd series
`U(t)`. -/
theorem firstVariationSeries_formula (y z : σ → K) :
    firstVariationSeries y z = PowerSeries.X * completeEvaluationSeries y *
      ∑ i, PowerSeries.C (z i) * geometricSeries (y i) := by
  have hsum : firstVariationSeries y z =
      ∑ i, PowerSeries.C (z i) *
        PowerSeries.map (MvPolynomial.eval y)
          (coefficientDerivation (MvPolynomial.pderiv i)
            (completeSymmetricSeries (K := K) (σ := σ))) := by
    ext n
    simp [firstVariationSeries, completeSymmetricSeries]
  rw [hsum]
  simp only [pderiv_completeSymmetricSeries, map_mul, PowerSeries.map_X,
    map_completeSymmetricSeries, map_geometricSeries, MvPolynomial.eval_X]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end CompleteSymmetric

end PaperVerification.AlternatingForms
