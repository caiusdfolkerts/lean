module

public import paper_verification.literal012
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import paper_verification.literal005
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.Algebra.Ring.Subgroup
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Finsupp.Span
import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Localization.Module
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Category
public import paper_verification.literal001
import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.KrullDimension.Field
import paper_verification.literal001
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option Elab.async false

section TAF_LiteralSource_0578
/- Original module: PaperVerification.AlternatingFormsChernSeriesIdentity -/


/-!
# The Chern relation series and their common zeros

Here the recurrence is connected to the actual relations of Section 4.3:
`R₂ₘ = hₘ(x₁²,…,xₛ²)` and
`R₂ₘ₊₁ = ∑ᵢ xᵢ (∂ᵢ hₘ₊₁)(x₁²,…,xₛ²)`.

All formal-series identities are proved by finite-product differentiation and the
geometric-series identity.  No eventual-vanishing or isolated-zero assumption is
introduced.  The remaining cohomological and regular-sequence identifications
belong to separate parts of the paper.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open Finset

variable {K σ : Type*} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ]

@[simp] theorem eulerSeries_one : eulerSeries (1 : PowerSeries K) = 0 := by
  simp [eulerSeries]

theorem eulerSeries_mul (f g : PowerSeries K) :
    eulerSeries (f * g) = f * eulerSeries g + g * eulerSeries f := by
  simp only [eulerSeries, Derivation.leibniz, smul_eq_mul]
  ring

/-- Multiplicativity of the differential identity used in equation (7). -/
theorem chern_product_identity {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c b a : ι → PowerSeries K)
    (hlocal : ∀ i ∈ S, c i * (eulerSeries (b i) + 2 * a i * b i ^ 2) +
      2 * eulerSeries (c i) * b i = 0) :
    (∏ i ∈ S, c i) * (eulerSeries (∏ i ∈ S, b i) +
        2 * (∏ i ∈ S, b i) * ∑ i ∈ S, a i * b i) +
      2 * eulerSeries (∏ i ∈ S, c i) * (∏ i ∈ S, b i) = 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    have hsmall := ih (fun i hi => hlocal i (by simp [hi]))
    have hjlocal := hlocal j (by simp)
    simp only [Finset.prod_insert hj, Finset.sum_insert hj, eulerSeries_mul]
    linear_combination (c j * b j) * hsmall +
      ((∏ i ∈ S, c i) * (∏ i ∈ S, b i)) * hjlocal

/-- The geometric factor `(1-x²t²)⁻¹`. -/
noncomputable def rootGeometricSeries (x : K) : PowerSeries K :=
  PowerSeries.expand 2 (by decide) (geometricSeries (x ^ 2))

theorem rootGeometricSeries_inverse (x : K) :
    rootGeometricSeries x * (1 - (PowerSeries.C x * PowerSeries.X) ^ 2) = 1 := by
  have h := congrArg (PowerSeries.expand 2 (by decide))
    (geometricSeries_inverse (x ^ 2))
  simpa [rootGeometricSeries, PowerSeries.expand_C, mul_pow] using h

/-- The one-variable factor of the differential identity. -/
theorem rootGeometricSeries_identity (x : K) :
    (1 - PowerSeries.C x * PowerSeries.X) *
        (eulerSeries (rootGeometricSeries x) +
          2 * (PowerSeries.C x * PowerSeries.X) * rootGeometricSeries x ^ 2) +
      2 * eulerSeries (1 - PowerSeries.C x * PowerSeries.X) *
        rootGeometricSeries x = 0 := by
  have hinv := rootGeometricSeries_inverse x
  have hderivative := PowerSeries.derivative.leibniz_of_mul_eq_one hinv
  have hB : eulerSeries (rootGeometricSeries x) =
      2 * (PowerSeries.C x * PowerSeries.X) ^ 2 * rootGeometricSeries x ^ 2 := by
    rw [eulerSeries, hderivative]
    simp only [map_sub, Derivation.map_one_eq_zero, PowerSeries.derivative_pow,
      Derivation.leibniz, PowerSeries.derivative_C, PowerSeries.derivative_X,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_sub]
    norm_num
    ring
  have hC : eulerSeries (1 - PowerSeries.C x * PowerSeries.X) =
      -(PowerSeries.C x * PowerSeries.X) := by
    simp [eulerSeries, smul_eq_mul]
    ring
  rw [hB, hC]
  linear_combination (2 * (PowerSeries.C x * PowerSeries.X) *
    rootGeometricSeries x) * hinv

/-- `C(t)=∏ᵢ(1-xᵢt)` as an actual polynomial. -/
noncomputable def chernPolynomial (x : σ → K) : Polynomial K :=
  ∏ i, (1 - Polynomial.C (x i) * Polynomial.X)

theorem chernPolynomial_coe (x : σ → K) :
    (chernPolynomial x : PowerSeries K) =
      ∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X) := by
  change Polynomial.coeToPowerSeries.ringHom (∏ i, (1 - Polynomial.C (x i) * Polynomial.X)) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp

@[simp] theorem chernPolynomial_coeff_zero (x : σ → K) :
    (chernPolynomial x).coeff 0 = 1 := by
  simp [chernPolynomial, Polynomial.coeff_zero_prod]

theorem chernPolynomial_natDegree_le (x : σ → K) :
    (chernPolynomial x).natDegree ≤ Fintype.card σ := by
  calc
    _ ≤ ∑ i : σ, (1 - Polynomial.C (x i) * Polynomial.X).natDegree :=
      Polynomial.natDegree_prod_le Finset.univ _
    _ ≤ ∑ _i : σ, 1 := by
      apply Finset.sum_le_sum
      intro i _
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · simp
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    _ = _ := by simp

/-- The even series from the actual complete symmetric polynomials. -/
noncomputable def evenRootSeries (x : σ → K) : PowerSeries K :=
  PowerSeries.expand 2 (by decide) (completeEvaluationSeries fun i => x i ^ 2)

/-- The odd series in the paper, in its proved rational generating form. -/
noncomputable def oddRootSeries (x : σ → K) : PowerSeries K :=
  PowerSeries.X * evenRootSeries x * ∑ i, PowerSeries.C (x i) * rootGeometricSeries (x i)

theorem evenRootSeries_eq_prod (x : σ → K) :
    evenRootSeries x = ∏ i, rootGeometricSeries (x i) := by
  rw [evenRootSeries, completeEvaluationSeries_eq_prod, map_prod]
  rfl

theorem oddRootSeries_eq_product_sum (x : σ → K) :
    oddRootSeries x = evenRootSeries x *
      ∑ i, (PowerSeries.C (x i) * PowerSeries.X) * rootGeometricSeries (x i) := by
  unfold oddRootSeries
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The odd generating series is obtained from the actual first variation,
including the shift by one power of the formal variable. -/
theorem X_mul_oddRootSeries (x : σ → K) :
    PowerSeries.X * oddRootSeries x =
      PowerSeries.expand 2 (by decide) (firstVariationSeries (fun i => x i ^ 2) x) := by
  rw [firstVariationSeries_formula]
  simp only [map_mul, map_sum, PowerSeries.expand_X, PowerSeries.expand_C]
  change PowerSeries.X * oddRootSeries x =
    PowerSeries.X ^ 2 * evenRootSeries x *
      ∑ i, PowerSeries.C (x i) * rootGeometricSeries (x i)
  unfold oddRootSeries
  ring

/-- The differential identity is proved for the actual symmetric root series. -/
theorem root_series_differential_identity (x : σ → K) :
    (chernPolynomial x : PowerSeries K) *
        (eulerSeries (evenRootSeries x) + 2 * oddRootSeries x) +
      2 * eulerSeries (chernPolynomial x : PowerSeries K) * evenRootSeries x = 0 := by
  rw [oddRootSeries_eq_product_sum, evenRootSeries_eq_prod, chernPolynomial_coe]
  convert chern_product_identity (K := K) Finset.univ
    (fun i => 1 - PowerSeries.C (x i) * PowerSeries.X)
    (fun i => rootGeometricSeries (x i))
    (fun i => PowerSeries.C (x i) * PowerSeries.X)
    (fun i _ => rootGeometricSeries_identity (x i)) using 1 <;> ring

/-- `B(t) C(t) C(-t)=1`, proved in the formal power-series ring. -/
theorem root_series_inverse_identity (x : σ → K) :
    evenRootSeries x * (chernPolynomial x : PowerSeries K) *
      (chernPolynomial (fun i => -x i) : PowerSeries K) = 1 := by
  rw [evenRootSeries_eq_prod, chernPolynomial_coe, chernPolynomial_coe,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  have hinv := rootGeometricSeries_inverse (x i)
  simp only [map_neg]
  convert hinv using 1 <;> ring

/-- The paper's relations, defined through the actual complete homogeneous
symmetric polynomials and their actual partial derivatives. -/
noncomputable def chernRootRelation (x : σ → K) (n : ℕ) : K :=
  if Even n then
    MvPolynomial.eval (fun i => x i ^ 2) (MvPolynomial.hsymm σ K (n / 2))
  else
    ∑ i, x i * MvPolynomial.eval (fun j => x j ^ 2)
      (MvPolynomial.pderiv i (MvPolynomial.hsymm σ K ((n + 1) / 2)))

theorem evenRelationSeries_chernRootRelation (x : σ → K) :
    evenRelationSeries (chernRootRelation x) = evenRootSeries x := by
  ext n
  simp only [coeff_evenRelationSeries, evenRootSeries, PowerSeries.coeff_expand,
    completeEvaluationSeries, PowerSeries.coeff_mk, chernRootRelation,
    ← even_iff_two_dvd]
  split_ifs <;> rfl

theorem oddRelationSeries_chernRootRelation (x : σ → K) :
    oddRelationSeries (chernRootRelation x) = oddRootSeries x := by
  ext n
  have h := congrArg (PowerSeries.coeff (n + 1)) (X_mul_oddRootSeries x)
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand] at h
  rw [h]
  simp only [coeff_oddRelationSeries, firstVariationSeries, PowerSeries.coeff_mk,
    chernRootRelation, ← even_iff_two_dvd, Nat.even_add_one]
  split_ifs <;> rfl

/-- Equation (7), now with no generating-function assumptions and with exactly
the symmetric polynomials defined by the paper. -/
theorem chernRootRelation_recurrence (x : σ → K) (m : ℕ) :
    ∑ i ∈ range (m + 1), (chernPolynomial x).coeff i *
      chernRecurrenceWeight m i * chernRootRelation x (m - i) = 0 := by
  apply chern_recurrence_of_series_identity
  rw [evenRelationSeries_chernRootRelation, oddRelationSeries_chernRootRelation]
  exact root_series_differential_identity x

/-- The isolated-zero step in Section 4.3, for every size and every positive
starting degree.  The conclusions concern the actual root tuple. -/
theorem chernRootRelation_common_zero {w : ℕ} (hw : 0 < w) (x : σ → K)
    (hwindow : ∀ m, w ≤ m → m < w + Fintype.card σ → chernRootRelation x m = 0) :
    ∀ i, x i = 0 := by
  have hC : chernPolynomial x = 1 := by
    apply chern_polynomial_eq_one_of_window hw (chernPolynomial x)
      (chernPolynomial fun i => -x i) (chernPolynomial_coeff_zero x)
      (chernPolynomial_natDegree_le x) (chernRootRelation x)
    · rw [evenRelationSeries_chernRootRelation, oddRelationSeries_chernRootRelation]
      exact root_series_differential_identity x
    · rw [evenRelationSeries_chernRootRelation]
      exact root_series_inverse_identity x
    · exact hwindow
  intro i
  have hdiv : (1 - Polynomial.C (x i) * Polynomial.X) ∣ chernPolynomial x :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  rw [hC] at hdiv
  have hunit : IsUnit (1 - Polynomial.C (x i) * Polynomial.X) :=
    isUnit_iff_dvd_one.mpr hdiv
  have hdegree := Polynomial.natDegree_eq_zero_of_isUnit hunit
  have hcoeff := Polynomial.coeff_eq_zero_of_natDegree_lt
    (p := 1 - Polynomial.C (x i) * Polynomial.X) (n := 1) (by omega)
  simpa [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul_X] using hcoeff

end PaperVerification.AlternatingForms
end
end TAF_LiteralSource_0578

section TAF_LiteralSource_0579
/- Original module: TauCeti.RingTheory.PowerSeries.Rescale -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Rescaling power series

This file records general facts about Mathlib's coefficientwise rescaling
`PowerSeries.rescale` of power series.

## Main results

* `PowerSeries.rescale_C`: rescaling the variable fixes constant power series.
-/

public section

namespace PowerSeries

/-- Rescaling the power-series variable fixes constant power series. -/
@[simp]
theorem rescale_C {R : Type*} [CommSemiring R] (a b : R) :
    rescale a (C b) = C b := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h <;> simp [h]

end PowerSeries
end
end TAF_LiteralSource_0579

section TAF_LiteralSource_0580
/- Original module: TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Elementary symmetric polynomials

This file develops the elementary symmetric polynomials `e_n`.  It defines the integer-indexed
extension `TauCeti.esymmInt`, whose negative degrees vanish, and proves the generating functions
`∑ₙ eₙ tⁿ = ∏ᵢ (1 + xᵢ t)` and `∑ₙ (-1)ⁿ eₙ tⁿ = ∏ᵢ (1 - xᵢ t)`.  The integer indexing is the one
determinantal formulas such as the dual (transpose) Jacobi--Trudi identity use.

The file also gives explicit formulas for elementary symmetric polynomials in small finite
alphabets.  Such expansions support explicit computations of symmetric orbit products; in
particular the four-variable formula is used to express the quartic `D₄` resolvent's orbit
product in elementary symmetric polynomials.

## Main results

* `Multiset.esymm_cons`: adjoining an element `a` to a multiset gives
  `e_{n+1}(a, s) = e_{n+1}(s) + a eₙ(s)`.
* `Multiset.esymm_cons_zero`: adjoining a zero gives `e_{n+1}(0, s) = e_{n+1}(s)`.
* `TauCeti.esymmInt`: the elementary symmetric polynomial `e_m` of an integer degree `m`, which
  is `0` for `m < 0`.
* `TauCeti.coeff_prod_one_add_C_mul_X`: the coefficient of `tⁿ` in `∏ᵢ (1 + xᵢ t)`, as a sum
  over the `n`-element subsets of the variables.
* `TauCeti.mk_esymm_eq_prod_one_add_X`: the generating function of the `eₙ`.
* `TauCeti.mk_neg_one_pow_mul_esymm_eq_prod_one_sub_X`: its signed version
  `∑ₙ (-1)ⁿ eₙ tⁿ = ∏ᵢ (1 - xᵢ t)`.
* `TauCeti.esymm_fin_four`: the four elementary symmetric polynomials in four variables.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  (2.2) and (2.6').
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, §7.6.
-/

public section

open Finset

/-- Adjoining an element `a` to a multiset `s`: `e_{n+1}(a, s) = e_{n+1}(s) + a eₙ(s)`. -/
theorem Multiset.esymm_cons {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

/-- Adjoining a zero to a multiset `s` does not change its positive-degree elementary symmetric
values: `e_{n+1}(0, s) = e_{n+1}(s)`. -/
@[simp]
theorem Multiset.esymm_cons_zero {R : Type*} [CommSemiring R] (s : Multiset R) (n : ℕ) :
    (0 ::ₘ s).esymm (n + 1) = s.esymm (n + 1) := by
  simp [Multiset.esymm_cons]

namespace TauCeti

section esymmInt

variable (σ : Type*) [Fintype σ] (R : Type*) [CommSemiring R]

/-- The **elementary symmetric polynomial of integer degree** `m`: `e_m` for `m ≥ 0` and `0` for
`m < 0`.  This is the indexing determinantal formulas such as the dual Jacobi--Trudi identity
use. -/
noncomputable def esymmInt (m : ℤ) : MvPolynomial σ R :=
  if 0 ≤ m then MvPolynomial.esymm σ R m.toNat else 0

variable {σ R}

/-- In a nonnegative degree, `TauCeti.esymmInt` is `MvPolynomial.esymm`. -/
@[simp]
theorem esymmInt_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    esymmInt σ R m = MvPolynomial.esymm σ R m.toNat := by
  simp [esymmInt, hm]

/-- In a negative degree, `TauCeti.esymmInt` vanishes. -/
@[simp]
theorem esymmInt_of_neg {m : ℤ} (hm : m < 0) : esymmInt σ R m = 0 := by
  simp [esymmInt, not_le.mpr hm]

/-- In a natural-number degree, `TauCeti.esymmInt` is `MvPolynomial.esymm`. -/
theorem esymmInt_natCast (n : ℕ) : esymmInt σ R n = MvPolynomial.esymm σ R n := by
  simp [esymmInt]

/-- `e_0 = 1`. -/
theorem esymmInt_zero : esymmInt σ R 0 = 1 := by
  simp

/-- Changing the coefficients along a ring homomorphism preserves `TauCeti.esymmInt`. -/
@[simp]
theorem map_esymmInt {S : Type*} [CommSemiring S] (m : ℤ) (f : R →+* S) :
    MvPolynomial.map f (esymmInt σ R m) = esymmInt σ S m := by
  unfold esymmInt
  split_ifs <;> simp [MvPolynomial.map_esymm]

/-- Renaming the variables along a bijection preserves `TauCeti.esymmInt`. -/
@[simp]
theorem rename_esymmInt {τ : Type*} [Fintype τ] (m : ℤ) (e : σ ≃ τ) :
    MvPolynomial.rename e (esymmInt σ R m) = esymmInt τ R m := by
  unfold esymmInt
  split_ifs <;> simp [MvPolynomial.rename_esymm]

end esymmInt

section GeneratingFunction

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (R : Type*) [CommSemiring R]

omit [DecidableEq σ] in
/-- **The coefficient of `tⁿ` in `∏ᵢ (1 + xᵢ t)`**: the sum, over the `n`-element subsets `s` of
the variables, of the product of the variables in `s`. -/
theorem coeff_prod_one_add_C_mul_X (n : ℕ) :
    (∏ i, (1 + PowerSeries.C (MvPolynomial.X i : MvPolynomial σ R) *
      PowerSeries.X)).coeff n =
      ∑ s ∈ Finset.powersetCard n (Finset.univ : Finset σ), ∏ i ∈ s, MvPolynomial.X i := by
  classical
  rw [Finset.prod_one_add, map_sum, Finset.powersetCard_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h : ∏ i ∈ s, (PowerSeries.C (MvPolynomial.X i : MvPolynomial σ R) * PowerSeries.X) =
      PowerSeries.C (∏ i ∈ s, (MvPolynomial.X i : MvPolynomial σ R)) *
        PowerSeries.X ^ s.card := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod]
  rw [h, PowerSeries.coeff_C_mul_X_pow]
  by_cases hs : s.card = n
  · subst hs
    simp
  · have hnt : n ≠ s.card := fun h => hs h.symm
    simp [hs, hnt]

omit [DecidableEq σ] in
/-- **The generating function of the elementary symmetric polynomials**:
`∑ₙ eₙ tⁿ = ∏ᵢ (1 + xᵢ t)`. -/
theorem mk_esymm_eq_prod_one_add_X :
    PowerSeries.mk (fun n => MvPolynomial.esymm σ R n) =
      ∏ i, (1 + PowerSeries.C (MvPolynomial.X i : MvPolynomial σ R) * PowerSeries.X) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_mk, coeff_prod_one_add_C_mul_X, MvPolynomial.esymm]

end GeneratingFunction

section SignedGeneratingFunction

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (R : Type*) [CommRing R]

omit [DecidableEq σ] in
/-- **The signed generating function of the elementary symmetric polynomials**:
`∑ₙ (-1)ⁿ eₙ tⁿ = ∏ᵢ (1 - xᵢ t)`. -/
theorem mk_neg_one_pow_mul_esymm_eq_prod_one_sub_X :
    PowerSeries.mk (fun n => (-1 : MvPolynomial σ R) ^ n * MvPolynomial.esymm σ R n) =
      ∏ i, (1 - PowerSeries.C (MvPolynomial.X i : MvPolynomial σ R) * PowerSeries.X) := by
  rw [← PowerSeries.rescale_mk, mk_esymm_eq_prod_one_add_X (σ := σ) R, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [map_add, map_mul, map_neg, map_one, PowerSeries.rescale_X, PowerSeries.rescale_C]
  ring

end SignedGeneratingFunction

/-- The elementary symmetric polynomials in four variables, written out explicitly. -/
theorem esymm_fin_four {R : Type*} [CommSemiring R] :
    MvPolynomial.esymm (Fin 4) R 1 =
        MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.X 3 ∧
      MvPolynomial.esymm (Fin 4) R 2 =
        MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 0 * MvPolynomial.X 2 +
          MvPolynomial.X 0 * MvPolynomial.X 3 + MvPolynomial.X 1 * MvPolynomial.X 2 +
          MvPolynomial.X 1 * MvPolynomial.X 3 + MvPolynomial.X 2 * MvPolynomial.X 3 ∧
      MvPolynomial.esymm (Fin 4) R 3 =
        MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 +
          MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 +
          MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3 +
          MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 ∧
      MvPolynomial.esymm (Fin 4) R 4 =
        MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 := by
  have h1 : Finset.powersetCard 1 (Finset.univ : Finset (Fin 4)) = {{0}, {1}, {2}, {3}} := by
    decide
  have h2 : Finset.powersetCard 2 (Finset.univ : Finset (Fin 4)) =
      {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}} := by
    decide
  have h3 : Finset.powersetCard 3 (Finset.univ : Finset (Fin 4)) =
      {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}} := by
    decide
  have h4 : Finset.powersetCard 4 (Finset.univ : Finset (Fin 4)) = {{0, 1, 2, 3}} := by
    decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp (config := { decide := true }) only [MvPolynomial.esymm, h1, h2, h3, h4,
        Finset.sum_insert, Finset.prod_insert, Finset.sum_singleton, Finset.prod_singleton,
        Finset.mem_insert, Finset.mem_singleton, add_assoc, mul_assoc]

end TauCeti
end
end TAF_LiteralSource_0580

section TAF_LiteralSource_0581
/- Original module: PaperVerification.AlternatingFormsChernDescent -/


/-!
# Descent of the actual Chern relations to elementary symmetric coordinates

The relations are first defined as genuine symmetric polynomials in roots.
The fundamental theorem of symmetric polynomials then gives their unique
expressions in the elementary symmetric coordinates.  Vieta surjectivity is
proved by factoring a polynomial with constant coefficient one, allowing its
degree to drop and padding the root tuple by zeros.  Consequently the isolated
common zero statement concerns arbitrary coefficient tuples, rather than only
tuples already supplied together with chosen roots.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open Finset

variable {K σ : Type*} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ]

/-- Substitution of the squares of the root variables. -/
noncomputable def squareSubstitution :
    MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval fun i => MvPolynomial.X i ^ 2

theorem rename_squareSubstitution (e : Equiv.Perm σ) (p : MvPolynomial σ K) :
    MvPolynomial.rename e (squareSubstitution p) =
      squareSubstitution (MvPolynomial.rename e p) := by
  simp only [squareSubstitution, MvPolynomial.comp_aeval_apply,
    MvPolynomial.aeval_rename, map_pow, MvPolynomial.rename_X, Function.comp_def]

/-- The actual root-coordinate relation polynomial from Section 4.3. -/
noncomputable def chernRootRelationPolynomial (n : ℕ) : MvPolynomial σ K :=
  if Even n then
    squareSubstitution (MvPolynomial.hsymm σ K (n / 2))
  else
    ∑ i, MvPolynomial.X i * squareSubstitution
      (MvPolynomial.pderiv i (MvPolynomial.hsymm σ K ((n + 1) / 2)))

theorem eval_squareSubstitution (x : σ → K) (p : MvPolynomial σ K) :
    MvPolynomial.eval x (squareSubstitution p) =
      MvPolynomial.eval (fun i => x i ^ 2) p := by
  change MvPolynomial.aeval x (MvPolynomial.aeval _ p) = MvPolynomial.aeval _ p
  simp only [MvPolynomial.comp_aeval_apply, map_pow, MvPolynomial.aeval_X]

@[simp] theorem eval_chernRootRelationPolynomial (x : σ → K) (n : ℕ) :
    MvPolynomial.eval x (chernRootRelationPolynomial (K := K) (σ := σ) n) =
      chernRootRelation x n := by
  unfold chernRootRelationPolynomial chernRootRelation
  split_ifs <;> simp [eval_squareSubstitution]

set_option maxHeartbeats 800000 in
theorem chernRootRelationPolynomial_isSymmetric (n : ℕ) :
    (chernRootRelationPolynomial (K := K) (σ := σ) n).IsSymmetric := by
  intro e
  unfold chernRootRelationPolynomial
  split_ifs
  · rw [rename_squareSubstitution, MvPolynomial.rename_hsymm]
  · simp only [map_sum, map_mul, MvPolynomial.rename_X, rename_squareSubstitution]
    calc
      _ = ∑ i, MvPolynomial.X (e i) * squareSubstitution
          (MvPolynomial.pderiv (e i) (MvPolynomial.hsymm σ K ((n + 1) / 2))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← MvPolynomial.pderiv_rename e.injective,
          MvPolynomial.rename_hsymm]
      _ = _ := Equiv.sum_comp e (fun i : σ => MvPolynomial.X i * squareSubstitution
        (MvPolynomial.pderiv i (MvPolynomial.hsymm σ K ((n + 1) / 2))))

/-- Coordinates `c₁,…,cₛ` have indices `0,…,s-1`.  This is the unique polynomial
whose substitution `cᵢ=eᵢ(x)` is the paper's root-coordinate relation. -/
noncomputable def chernCoefficientRelation (s n : ℕ) : MvPolynomial (Fin s) K :=
  (MvPolynomial.esymmAlgEquiv (Fin s) K (Fintype.card_fin s)).symm
    ⟨chernRootRelationPolynomial n, chernRootRelationPolynomial_isSymmetric n⟩

theorem chernCoefficientRelation_substitution (s n : ℕ) :
    MvPolynomial.aeval (fun i : Fin s => MvPolynomial.esymm (Fin s) K (i.val + 1))
        (chernCoefficientRelation (K := K) s n) =
      chernRootRelationPolynomial (K := K) (σ := Fin s) n := by
  have h := (MvPolynomial.esymmAlgEquiv (Fin s) K (Fintype.card_fin s)).apply_symm_apply
    ⟨chernRootRelationPolynomial n, chernRootRelationPolynomial_isSymmetric n⟩
  have hv := congrArg Subtype.val h
  change (MvPolynomial.esymmAlgHom (Fin s) K s (chernCoefficientRelation s n)).val = _ at hv
  simpa only [MvPolynomial.esymmAlgHom_apply] using hv

/-- The root-to-coefficient map used by the splitting principle. -/
noncomputable def chernCoefficientTuple {s : ℕ} (x : Fin s → K) : Fin s → K :=
  fun i => MvPolynomial.eval x (MvPolynomial.esymm (Fin s) K (i.val + 1))

theorem eval_chernCoefficientRelation {s : ℕ} (x : Fin s → K) (n : ℕ) :
    MvPolynomial.eval (chernCoefficientTuple x) (chernCoefficientRelation s n) =
      chernRootRelation x n := by
  have h := congrArg (MvPolynomial.aeval x)
    (chernCoefficientRelation_substitution (K := K) s n)
  rw [MvPolynomial.comp_aeval_apply] at h
  exact h.trans (eval_chernRootRelationPolynomial x n)

/-- The elementary symmetric coefficient formula, including degrees larger
than the number of roots and tuples containing zero roots. -/
theorem chernPolynomial_coeff (x : σ → K) (n : ℕ) :
    (chernPolynomial x).coeff n =
      (-1 : K) ^ n * MvPolynomial.eval x (MvPolynomial.esymm σ K n) := by
  have h := congrArg (PowerSeries.map (MvPolynomial.eval x))
    (TauCeti.mk_neg_one_pow_mul_esymm_eq_prod_one_sub_X (σ := σ) K)
  have hc := congrArg (PowerSeries.coeff n) h
  simp only [PowerSeries.coeff_map, map_mul, map_pow, map_neg, map_one,
    PowerSeries.coeff_mk, map_prod, map_sub, PowerSeries.map_C,
    MvPolynomial.eval_X, PowerSeries.map_X] at hc
  rw [← chernPolynomial_coe, Polynomial.coeff_coe] at hc
  exact hc.symm

/-- A constant-one polynomial factors into exactly `s` normalized linear
factors over an algebraically closed field; zero roots account for degree loss. -/
theorem exists_chernPolynomial [IsAlgClosed K] (s : ℕ) (P : Polynomial K)
    (hP0 : P.coeff 0 = 1) (hPs : P.natDegree ≤ s) :
    ∃ x : Fin s → K, chernPolynomial x = P := by
  induction s generalizing P with
  | zero =>
    have hP : P = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hPs), hP0,
        map_one]
    exact ⟨Fin.elim0, by simp [chernPolynomial, hP]⟩
  | succ s ih =>
    by_cases hP : P = 1
    · exact ⟨fun _ => 0, by simp [chernPolynomial, hP]⟩
    have hdeg : P.natDegree ≠ 0 := by
      intro hzero
      apply hP
      rw [Polynomial.eq_C_of_natDegree_eq_zero hzero, hP0, map_one]
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root P
      (Polynomial.degree_ne_of_natDegree_ne hdeg)
    have hr0 : r ≠ 0 := by
      intro hz
      subst r
      have h : P.eval 0 = 0 := hr
      rw [← Polynomial.coeff_zero_eq_eval_zero, hP0] at h
      exact one_ne_zero h
    obtain ⟨D, hD⟩ := Polynomial.dvd_iff_isRoot.mpr hr
    let Q : Polynomial K := -Polynomial.C r * D
    have hab : Polynomial.C r⁻¹ * Polynomial.C r = (1 : Polynomial K) := by
      rw [← map_mul, inv_mul_cancel₀ hr0, map_one]
    have hfactor : P = (1 - Polynomial.C r⁻¹ * Polynomial.X) * Q := by
      rw [hD]
      dsimp [Q]
      calc
        _ = Polynomial.C r⁻¹ * Polynomial.C r * Polynomial.X * D - Polynomial.C r * D := by
          rw [hab]
          ring
        _ = _ := by ring
    have hQ0 : Q.coeff 0 = 1 := by
      have h := congrArg (fun p : Polynomial K => p.coeff 0) hfactor
      simpa [Polynomial.mul_coeff_zero, hP0] using h.symm
    have hQne : Q ≠ 0 := by
      intro h
      simpa [h] using hQ0
    have hlin : (1 - Polynomial.C r⁻¹ * Polynomial.X).natDegree = 1 := by
      rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
      · exact Polynomial.natDegree_C_mul_X _ (inv_ne_zero hr0)
      · simp [Polynomial.natDegree_C_mul_X _ (inv_ne_zero hr0)]
    have hlinne : (1 - Polynomial.C r⁻¹ * Polynomial.X : Polynomial K) ≠ 0 := by
      intro h
      simpa [h] using hlin
    have hQs : Q.natDegree ≤ s := by
      rw [hfactor, Polynomial.natDegree_mul hlinne hQne, hlin] at hPs
      omega
    obtain ⟨x, hx⟩ := ih Q hQ0 hQs
    refine ⟨Fin.cons r⁻¹ x, ?_⟩
    rw [chernPolynomial, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    change (1 - Polynomial.C r⁻¹ * Polynomial.X) * chernPolynomial x = P
    rw [hx]
    exact hfactor.symm

/-- A polynomial whose signed nonconstant coefficients are an arbitrary
coefficient tuple. -/
noncomputable def coefficientPolynomial {s : ℕ} (c : Fin s → K) : Polynomial K :=
  1 + ∑ i, Polynomial.C ((-1 : K) ^ (i.val + 1) * c i) * Polynomial.X ^ (i.val + 1)

@[simp] theorem coefficientPolynomial_coeff_zero {s : ℕ} (c : Fin s → K) :
    (coefficientPolynomial c).coeff 0 = 1 := by
  simp [coefficientPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]

theorem coefficientPolynomial_natDegree_le {s : ℕ} (c : Fin s → K) :
    (coefficientPolynomial c).natDegree ≤ s := by
  unfold coefficientPolynomial
  apply (Polynomial.natDegree_add_le _ _).trans
  refine max_le (by simp) ?_
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem coefficientPolynomial_coeff {s : ℕ} (c : Fin s → K) (i : Fin s) :
    (coefficientPolynomial c).coeff (i.val + 1) = (-1 : K) ^ (i.val + 1) * c i := by
  simp only [coefficientPolynomial, Polynomial.coeff_add, Polynomial.coeff_one,
    Nat.add_eq_zero, one_ne_zero, and_false, ite_false, zero_add,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have h : i.val ≠ j.val := by
      intro h
      exact hji (Fin.ext h.symm)
    simp [h]
  · simp

/-- Vieta surjectivity, with no assumption that the last coefficient is nonzero. -/
theorem chernCoefficientTuple_surjective [IsAlgClosed K] (s : ℕ) :
    Function.Surjective (chernCoefficientTuple (K := K) (s := s)) := by
  intro c
  obtain ⟨x, hx⟩ := exists_chernPolynomial s (coefficientPolynomial c)
    (coefficientPolynomial_coeff_zero c) (coefficientPolynomial_natDegree_le c)
  refine ⟨x, ?_⟩
  funext i
  have h := congrArg (fun p : Polynomial K => p.coeff (i.val + 1)) hx
  rw [chernPolynomial_coeff, coefficientPolynomial_coeff] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h

/-- The isolated common zero assertion in the abstract Chern coordinates.
This is the same polynomial system as the root system, by the proved
fundamental-theorem substitution and Vieta surjectivity. -/
theorem chernCoefficientRelation_common_zero [IsAlgClosed K] {s w : ℕ} (hw : 0 < w)
    (c : Fin s → K)
    (hwindow : ∀ m, w ≤ m → m < w + s →
      MvPolynomial.eval c (chernCoefficientRelation s m) = 0) :
    c = 0 := by
  obtain ⟨x, rfl⟩ := chernCoefficientTuple_surjective (K := K) s c
  have hx : ∀ i, x i = 0 := by
    apply chernRootRelation_common_zero hw
    intro m hwm hms
    rw [← eval_chernCoefficientRelation]
    exact hwindow m hwm (by simpa using hms)
  funext i
  have hcoeff := chernPolynomial_coeff x (i.val + 1)
  have hP : chernPolynomial x = 1 := by simp [chernPolynomial, hx]
  rw [hP] at hcoeff
  have hz : (-1 : K) ^ (i.val + 1) * chernCoefficientTuple x i = 0 := by
    simpa [chernCoefficientTuple, Polynomial.coeff_one] using hcoeff.symm
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

end PaperVerification.AlternatingForms
end
end TAF_LiteralSource_0581

section TAF_LiteralSource_0582
/- Original module: PaperVerification.AlternatingFormsChernHomogeneity -/


/-!
# Weighted degrees of the Chern relations

The coefficient variable `cᵢ` has weight `i`, while each root variable has weight
one.  The elementary substitution intertwines those two gradings and is
injective.  Therefore the homogeneous root relation of degree `n` descends to
a polynomial of weighted degree exactly `n`.  This is the grading needed for
the complete-intersection assertion, and also proves that every positive-degree
relation vanishes at the origin.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open Finset

variable {K σ : Type*} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ]

theorem squareSubstitution_isHomogeneous {p : MvPolynomial σ K} {n : ℕ}
    (hp : p.IsHomogeneous n) : (squareSubstitution p).IsHomogeneous (2 * n) := by
  exact hp.aeval _ fun i => MvPolynomial.isHomogeneous_X_pow i 2

/-- Both parity families have the claimed degree in the actual root variables. -/
theorem chernRootRelationPolynomial_isHomogeneous (n : ℕ) :
    (chernRootRelationPolynomial (K := K) (σ := σ) n).IsHomogeneous n := by
  unfold chernRootRelationPolynomial
  split_ifs with heven
  · have h := squareSubstitution_isHomogeneous
      (MvPolynomial.isHomogeneous_hsymm (σ := σ) (R := K) (n / 2))
    convert h using 1
    obtain ⟨m, hm⟩ := heven
    omega
  · apply MvPolynomial.IsHomogeneous.sum
    intro i _
    have h := (MvPolynomial.isHomogeneous_X K i).mul
      (squareSubstitution_isHomogeneous
        ((MvPolynomial.isHomogeneous_hsymm (σ := σ) (R := K) ((n + 1) / 2)).pderiv
          (i := i)))
    convert h using 1
    have hodd : n % 2 = 1 := by
      rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero] at heven
      omega
    omega

/-- Positive weights on the coefficient variables, indexed starting at zero. -/
def chernCoefficientWeight {s : ℕ} (i : Fin s) : ℕ := i.val + 1

@[simp] theorem chernCoefficientWeight_ne_zero {s : ℕ} (i : Fin s) :
    chernCoefficientWeight i ≠ 0 := Nat.succ_ne_zero _

/-- The elementary substitution, viewed in the full polynomial ring. -/
noncomputable def elementarySubstitution (s : ℕ) :
    MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin s) K :=
  MvPolynomial.aeval fun i => MvPolynomial.esymm (Fin s) K (i.val + 1)

theorem elementarySubstitution_injective (s : ℕ) :
    Function.Injective (elementarySubstitution (K := K) s) := by
  intro p q h
  apply MvPolynomial.esymmAlgHom_injective K (by simp : s ≤ Fintype.card (Fin s))
  apply Subtype.ext
  simpa only [MvPolynomial.esymmAlgHom_apply, elementarySubstitution] using h

theorem elementarySubstitution_monomial_isHomogeneous {s : ℕ}
    (d : Fin s →₀ ℕ) (r : K) :
    (elementarySubstitution s (MvPolynomial.monomial d r)).IsHomogeneous
      (Finsupp.weight chernCoefficientWeight d) := by
  rw [elementarySubstitution, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  have h := MvPolynomial.IsHomogeneous.prod d.support
    (fun i => MvPolynomial.esymm (Fin s) K (i.val + 1) ^ d i)
    (fun i => (i.val + 1) * d i)
    (fun i _ => (MvPolynomial.isHomogeneous_esymm (σ := Fin s) (R := K)
      (i.val + 1)).pow (d i))
  convert h.C_mul r using 1 <;>
    simp [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, chernCoefficientWeight,
      smul_eq_mul, mul_comm]

/-- The grading comparison is an equality of actual homogeneous projections. -/
theorem elementarySubstitution_weightedHomogeneousComponent {s : ℕ}
    (p : MvPolynomial (Fin s) K) (n : ℕ) :
    MvPolynomial.homogeneousComponent n (elementarySubstitution s p) =
      elementarySubstitution s
        (MvPolynomial.weightedHomogeneousComponent chernCoefficientWeight n p) := by
  classical
  calc
    _ = MvPolynomial.homogeneousComponent n
        (elementarySubstitution s
          (∑ d ∈ p.support, MvPolynomial.monomial d (p.coeff d))) :=
      congrArg (fun q => MvPolynomial.homogeneousComponent n (elementarySubstitution s q))
        p.as_sum
    _ = ∑ d ∈ p.support, MvPolynomial.homogeneousComponent n
        (elementarySubstitution s (MvPolynomial.monomial d (p.coeff d))) := by
      simp only [map_sum]
    _ = _ := by
      rw [MvPolynomial.weightedHomogeneousComponent_apply, map_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      rw [MvPolynomial.homogeneousComponent_of_mem
        (elementarySubstitution_monomial_isHomogeneous d (p.coeff d))]
      by_cases h : Finsupp.weight chernCoefficientWeight d = n
      · simp [h]
      · simp [h, Ne.symm h]

/-- Injectivity of elementary substitution reflects the full weighted grading. -/
theorem isWeightedHomogeneous_of_elementarySubstitution {s : ℕ}
    (p : MvPolynomial (Fin s) K) {n : ℕ}
    (hp : (elementarySubstitution s p).IsHomogeneous n) :
    p.IsWeightedHomogeneous chernCoefficientWeight n := by
  have heq : MvPolynomial.weightedHomogeneousComponent chernCoefficientWeight n p = p := by
    apply elementarySubstitution_injective s
    rw [← elementarySubstitution_weightedHomogeneousComponent,
      MvPolynomial.homogeneousComponent_eq_self hp]
  rw [← heq]
  exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous n p

/-- The precise weighted degree of each descended relation. -/
theorem chernCoefficientRelation_isWeightedHomogeneous (s n : ℕ) :
    (chernCoefficientRelation (K := K) s n).IsWeightedHomogeneous
      chernCoefficientWeight n := by
  apply isWeightedHomogeneous_of_elementarySubstitution
  rw [elementarySubstitution, chernCoefficientRelation_substitution]
  exact chernRootRelationPolynomial_isHomogeneous n

/-- Positive-degree relations lie in the actual maximal ideal of the origin. -/
theorem chernCoefficientRelation_constantCoeff (s n : ℕ) (hn : n ≠ 0) :
    MvPolynomial.constantCoeff (chernCoefficientRelation (K := K) s n) = 0 := by
  rw [MvPolynomial.constantCoeff_eq]
  apply (chernCoefficientRelation_isWeightedHomogeneous s n).coeff_eq_zero 0
  simpa using hn.symm

end PaperVerification.AlternatingForms
end
end TAF_LiteralSource_0582

section TAF_LiteralSource_0583
/- Original module: PaperVerification.AlternatingFormsChernRelationsBasic -/


/-!
# The finite window of Chern relations

The literal ordered list of the Section 4 relations commutes with extension
of the coefficient field. Neither its definition nor these identities assumes
regularity, a quotient dimension formula, or a geometric comparison.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

variable {K L σ : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
  [Fintype σ] [DecidableEq σ]

theorem map_squareSubstitution (φ : K →+* L) (p : MvPolynomial σ K) :
    MvPolynomial.map φ (squareSubstitution p) =
      squareSubstitution (MvPolynomial.map φ p) := by
  change MvPolynomial.map φ
    (MvPolynomial.eval₂ MvPolynomial.C (fun i => MvPolynomial.X i ^ 2) p) = _
  rw [MvPolynomial.map_eval₂]
  congr 1
  funext i
  simp

theorem map_chernRootRelationPolynomial (φ : K →+* L) (n : ℕ) :
    MvPolynomial.map φ (chernRootRelationPolynomial (K := K) (σ := σ) n) =
      chernRootRelationPolynomial (K := L) (σ := σ) n := by
  unfold chernRootRelationPolynomial
  split_ifs
  · rw [map_squareSubstitution, MvPolynomial.map_hsymm]
  · simp only [map_sum, map_mul, MvPolynomial.map_X, map_squareSubstitution,
      ← MvPolynomial.pderiv_map, MvPolynomial.map_hsymm]

theorem map_elementarySubstitution (φ : K →+* L) {s : ℕ}
    (p : MvPolynomial (Fin s) K) :
    MvPolynomial.map φ (elementarySubstitution s p) =
      elementarySubstitution s (MvPolynomial.map φ p) := by
  change MvPolynomial.map φ
    (MvPolynomial.eval₂ MvPolynomial.C
      (fun i : Fin s => MvPolynomial.esymm (Fin s) K (i.val + 1)) p) = _
  rw [MvPolynomial.map_eval₂]
  congr 1
  funext i
  exact MvPolynomial.map_esymm (σ := Fin s) (R := K) (i.val+1) φ

/-- The unique elementary-coordinate relations commute with coefficient maps. -/
theorem map_chernCoefficientRelation (φ : K →+* L) (s n : ℕ) :
    MvPolynomial.map φ (chernCoefficientRelation (K := K) s n) =
      chernCoefficientRelation (K := L) s n := by
  apply elementarySubstitution_injective s
  rw [← map_elementarySubstitution, elementarySubstitution,
    chernCoefficientRelation_substitution, map_chernRootRelationPolynomial,
    elementarySubstitution, chernCoefficientRelation_substitution]

/-- The ordered length-`s` window of the paper's actual coefficient relations. -/
noncomputable def chernRelationSequence (K : Type*) [Field K] [CharZero K]
    (s w : ℕ) : List (MvPolynomial (Fin s) K) :=
  List.ofFn fun i : Fin s => chernCoefficientRelation s (w + i.val)

theorem map_chernRelationSequence (φ : K →+* L) (s w : ℕ) :
    (chernRelationSequence K s w).map (MvPolynomial.map φ) =
      chernRelationSequence L s w := by
  simp only [chernRelationSequence, List.map_ofFn, Function.comp_def,
    map_chernCoefficientRelation]

end PaperVerification.AlternatingForms
end
end TAF_LiteralSource_0583

section TAF_LiteralSource_0584
/- Original module: PaperVerification.HomogeneousLocalization -/


/-!
# Descending homogeneous regularity from the origin

Localization at the origin is not faithfully flat on all polynomial modules.
This file proves the precise homogeneous argument needed here. A homogeneous
polynomial belonging to a homogeneous ideal after localization already belongs
before localization, since the denominator has nonzero constant coefficient.
Applying that statement to every homogeneous component descends regularity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial RingTheory.Sequence

namespace PaperVerification.HomogeneousLocalization

variable {K ι : Type*} [Field K]
local notation "P" => MvPolynomial ι K
attribute [local instance] MvPolynomial.weightedGradedAlgebra

def originIdeal : Ideal P := RingHom.ker (constantCoeff : P →+* K)

instance originIdeal_isMaximal : (originIdeal (K := K) (ι := ι)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, constantCoeff_C ι c⟩)

abbrev OriginLocalRing := Localization.AtPrime (originIdeal (K := K) (ι := ι))

@[simp] theorem mem_originIdeal (f : P) :
    f ∈ originIdeal (K := K) (ι := ι) ↔ constantCoeff f = 0 := Iff.rfl

theorem coe_decompose_eq_component (w : ι → ℕ) (f : P) (d : ℕ) :
    (DirectSum.decompose (weightedHomogeneousSubmodule K w) f d : P) =
      weightedHomogeneousComponent w d f := by
  exact weightedDecomposition.decompose'_apply K w f d

theorem component_mul_of_left_homogeneous (w : ι → ℕ) (f g : P) (e d : ℕ)
    (hf : f.IsWeightedHomogeneous w e) :
    weightedHomogeneousComponent w (e + d) (f * g) =
      f * weightedHomogeneousComponent w d g := by
  simpa only [coe_decompose_eq_component] using
    (DirectSum.coe_decompose_mul_add_of_left_mem
      (weightedHomogeneousSubmodule K w) (j := d) hf (b := g))

theorem component_mul_of_right_homogeneous (w : ι → ℕ) (s f : P) (d : ℕ)
    (hw : ∀ i, w i ≠ 0) (hf : f.IsWeightedHomogeneous w d) :
    weightedHomogeneousComponent w d (s * f) = C (s.coeff 0) * f := by
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule K w) (i := 0) hf (a := s)
  simpa only [zero_add, coe_decompose_eq_component, weightedHomogeneousComponent_zero s hw] using h

/-- Clearing a denominator with nonzero constant term cannot introduce a
homogeneous polynomial into a homogeneous ideal. -/
theorem homogeneous_mem_of_constant_mul_mem (w : ι → ℕ) (hw : ∀ i, w i ≠ 0)
    (I : Ideal P) (hI : I.IsHomogeneous (weightedHomogeneousSubmodule K w))
    (f s : P) (d : ℕ) (hf : f.IsWeightedHomogeneous w d)
    (hs : s.coeff 0 ≠ 0) (hsf : s * f ∈ I) : f ∈ I := by
  have hc : C (s.coeff 0) * f ∈ I := by
    have h := hI d hsf
    rw [coe_decompose_eq_component, component_mul_of_right_homogeneous w s f d hw hf] at h
    exact h
  have hu : IsUnit (C (s.coeff 0) : P) := (isUnit_iff_ne_zero.mpr hs).map C
  exact (Ideal.unit_mul_mem_iff_mem I hu).mp hc

/-- The needed saturation statement is only asserted for homogeneous elements. -/
theorem homogeneous_mem_of_localized (w : ι → ℕ) (hw : ∀ i, w i ≠ 0)
    (I : Ideal P) (hI : I.IsHomogeneous (weightedHomogeneousSubmodule K w))
    (f : P) (d : ℕ) (hf : f.IsWeightedHomogeneous w d)
    (hloc : algebraMap P (OriginLocalRing (K := K) (ι := ι)) f ∈
      I.map (algebraMap P (OriginLocalRing (K := K) (ι := ι)))) : f ∈ I := by
  obtain ⟨s, hs, hsf⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (originIdeal (K := K) (ι := ι)).primeCompl
    (OriginLocalRing (K := K) (ι := ι)) I f).mp hloc
  apply homogeneous_mem_of_constant_mul_mem w hw I hI f s d hf _ hsf
  simpa only [Ideal.mem_primeCompl_iff, mem_originIdeal, constantCoeff_eq] using hs

/-- Regularity modulo a homogeneous ideal descends from localization at the
origin, with every homogeneous component checked separately. -/
theorem regular_of_localized (w : ι → ℕ) (hw : ∀ i, w i ≠ 0)
    (I : Ideal P) (hI : I.IsHomogeneous (weightedHomogeneousSubmodule K w))
    (f : P) (e : ℕ) (hf : f.IsWeightedHomogeneous w e)
    (hreg : IsSMulRegular
      (OriginLocalRing (K := K) (ι := ι) ⧸
        I.map (algebraMap P (OriginLocalRing (K := K) (ι := ι))))
      (algebraMap P (OriginLocalRing (K := K) (ι := ι)) f)) :
    IsSMulRegular (P ⧸ I) f := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem I f).mpr
  intro g hfg
  change f * g ∈ I at hfg
  apply hI.mem_iff.mpr
  intro d
  rw [coe_decompose_eq_component]
  apply homogeneous_mem_of_localized w hw I hI _ d
    (weightedHomogeneousComponent_isWeightedHomogeneous d g)
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mp hreg
  change algebraMap P (OriginLocalRing (K := K) (ι := ι)) f *
    algebraMap P (OriginLocalRing (K := K) (ι := ι))
      (weightedHomogeneousComponent w d g) ∈ _
  rw [← map_mul]
  apply Ideal.mem_map_of_mem
  have hc := hI (e + d) hfg
  rwa [coe_decompose_eq_component, component_mul_of_left_homogeneous w f g e d hf] at hc

/-- A homogeneous sequence is weakly regular as soon as its image at the
origin is weakly regular. No global faithful-flatness assertion is used. -/
theorem sequence_regular_of_localized (w : ι → ℕ) (hw : ∀ i, w i ≠ 0)
    (rs : List P) (hhom : ∀ f ∈ rs, ∃ d, f.IsWeightedHomogeneous w d)
    (hreg : IsWeaklyRegular (OriginLocalRing (K := K) (ι := ι))
      (rs.map (algebraMap P (OriginLocalRing (K := K) (ι := ι))))) :
    IsWeaklyRegular P rs := by
  constructor
  intro i hi
  let I : Ideal P := Ideal.ofList (rs.take i)
  have hI : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro f hf
    obtain ⟨d, hd⟩ := hhom f (List.mem_of_mem_take hf)
    exact ⟨d, hd⟩
  obtain ⟨d, hd⟩ := hhom rs[i] (List.getElem_mem hi)
  have hloc := hreg.regular_mod_prev i (by simpa only [List.length_map] using hi)
  have hprev :
      (Ideal.ofList ((rs.map (algebraMap P (OriginLocalRing (K := K) (ι := ι)))).take i) •
        (⊤ : Submodule (OriginLocalRing (K := K) (ι := ι))
          (OriginLocalRing (K := K) (ι := ι)))) =
      I.map (algebraMap P (OriginLocalRing (K := K) (ι := ι))) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ← List.map_take, ← Ideal.map_ofList]
  rw [hprev] at hloc
  have hloc' : IsSMulRegular
      (OriginLocalRing (K := K) (ι := ι) ⧸
        I.map (algebraMap P (OriginLocalRing (K := K) (ι := ι))))
      (algebraMap P (OriginLocalRing (K := K) (ι := ι)) rs[i]) := by
    simpa only [List.getElem_map] using hloc
  have hprev' : (Ideal.ofList (rs.take i) • (⊤ : Submodule P P)) = I := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  rw [hprev']
  exact regular_of_localized w hw I hI rs[i] d hd hloc'

end PaperVerification.HomogeneousLocalization
end
end
end TAF_LiteralSource_0584

section TAF_LiteralSource_0585
/- Original module: TauCeti.RingTheory.Ideal.Colon -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Colon ideals by one element

For an `R`-algebra `S`, the ideal `(N : x)` of a submodule `N` of an `S`-module commutes with
restricting scalars to `R`.

For an ideal `I` and an element `f` of a commutative ring, `I ∩ (f) = f · (I : f)`. When `f` is
regular this determines `(I : f)`: generators of `I ∩ (f)`, which an intersection computation
supplies, divided by `f` generate `(I : f)`.

## Main results

* `Submodule.comap_colon_singleton`: the ideal `(N : x)` of `R` is the preimage of the ideal
  `(N : x)` of `S`.
* `Ideal.inf_span_singleton_eq_span_singleton_mul_colon`: `I ∩ (f) = f · (I : f)`.
* `Ideal.colon_singleton_eq_of_inf_span_singleton_eq`: for regular `f`, if `I ∩ (f) = f · J`
  then `(I : f) = J`.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 4, §4,
  computing ideal quotients from intersections.
-/

public section

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
  [Module R M] [Module S M] [IsScalarTower R S M]

/-- For a submodule `N` of an `S`-module `M` and `x ∈ M`, the ideal `(N : x)` of `R` is the
preimage of the ideal `(N : x)` of `S`. -/
theorem Submodule.comap_colon_singleton (N : Submodule S M) (x : M) :
    (N.colon {x}).comap (algebraMap R S) = (N.restrictScalars R).colon {x} := by
  ext r
  simp [Submodule.mem_colon_singleton]

namespace Ideal

variable {R : Type*} [CommSemiring R] {I J : Ideal R} {f : R}

/-- The intersection of an ideal `I` with the principal ideal `(f)` is `f` times the colon ideal
`(I : f)`. -/
theorem inf_span_singleton_eq_span_singleton_mul_colon (I : Ideal R) (f : R) :
    I ⊓ span {f} = span {f} * I.colon {f} := by
  ext x
  simp only [mem_inf, mem_span_singleton_mul, mem_span_singleton', Submodule.mem_colon_singleton,
    smul_eq_mul]
  constructor
  · rintro ⟨hx, a, rfl⟩
    exact ⟨a, hx, mul_comm f a⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨mul_comm f a ▸ ha, a, mul_comm a f⟩

/-- **Colon ideals from intersections.** If `f` is regular and `I ∩ (f) = f · J`, then the colon
ideal `(I : f)` is `J`. -/
theorem colon_singleton_eq_of_inf_span_singleton_eq (hf : IsLeftRegular f)
    (h : I ⊓ span {f} = span {f} * J) : I.colon {f} = J := by
  rw [inf_span_singleton_eq_span_singleton_mul_colon, span_singleton_mul_eq_span_singleton_mul]
    at h
  refine le_antisymm (fun x hx ↦ ?_) fun y hy ↦ ?_
  · obtain ⟨y, hy, hxy⟩ := h.1 x hx
    exact hf hxy ▸ hy
  · obtain ⟨x, hx, hxy⟩ := h.2 y hy
    exact hf hxy ▸ hx

end Ideal
end
end TAF_LiteralSource_0585

section TAF_LiteralSource_0586
/- Original module: TauCeti.RingTheory.Ideal.AssociatedPrime.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Associated primes, dimension, and quotients by a regular element

Facts about the associated primes of a module `M` over a commutative ring `R`. The first two are
used to bound the depth of `M` by the dimensions `dim (R ⧸ p)` of its associated primes `p`:

* `IsAssociatedPrime.ringKrullDim_quotient_le_supportDim`: for an associated prime `p` of `M`, the
  dimension of `R ⧸ p` is at most the dimension of the support of `M`.
* `IsAssociatedPrime.exists_le_isAssociatedPrime_quotSMulTop`: if `R` is Noetherian, `M` is
  finite, and `x` is `M`-regular and lies in the Jacobson radical of the annihilator of `M`, then
  every associated prime of `M` lies in an associated prime of `M ⧸ x M`. This comes from
  Nakayama's lemma applied to the elements of `M` killed by `p`.

A separate fact describes the associated primes of a reduced ring:

* `IsAssociatedPrime.mem_minimalPrimes_of_isReduced`: every associated prime of a reduced ring is
  a minimal prime.

For an `R`-algebra `S`, two facts compare the associated primes of an `S`-module `M` over `S`
and over `R`, using `Submodule.comap_colon_singleton` from `TauCeti.RingTheory.Ideal.Colon`:

* `IsAssociatedPrime.comap`: the contraction of an associated prime over `S` is an associated
  prime over `R`.
* `IsAssociatedPrime.exists_isAssociatedPrime_comap_eq`: if `S` is Noetherian, every maximal ideal
  of `R` that is an associated prime over `R` is such a contraction.

## References

* H. Matsumura, *Commutative Ring Theory*, proof of Theorem 17.2.
-/

public section

open Pointwise

section CommSemiring

variable {R : Type*} [CommSemiring R] {p : Ideal R}

/-- Every associated prime of a reduced ring is a minimal prime: an associated prime is the
radical of the annihilator of some `x ≠ 0`, so it lies in a minimal prime that does not contain
`x`. -/
theorem IsAssociatedPrime.mem_minimalPrimes_of_isReduced [IsReduced R]
    (hp : IsAssociatedPrime p R) : p ∈ minimalPrimes R := by
  obtain ⟨hp, x, rfl⟩ := hp
  have hx0 : x ≠ 0 := fun h ↦ hp.ne_top (by simp [h])
  obtain ⟨q, hq, hxq⟩ : ∃ q ∈ minimalPrimes R, x ∉ q := by
    by_contra! h
    have hx : x ∈ nilradical R := by
      rw [nilradical, ← Ideal.sInf_minimalPrimes]
      exact Submodule.mem_sInf.2 h
    simp [nilradical_eq_zero, hx0] at hx
  have hle : (⊥ : Submodule R R).colon {x} ≤ q := fun r hr ↦ by
    refine (hq.1.1.mem_or_mem ?_).resolve_right hxq
    rw [← smul_eq_mul, (Submodule.mem_bot R).1 (Submodule.mem_colon_singleton.1 hr)]
    exact q.zero_mem
  have hle' := hq.1.1.radical_le_iff.2 hle
  rw [le_antisymm hle' (hq.2 ⟨hp, bot_le⟩ hle')]
  exact hq

end CommSemiring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : Ideal R}

namespace IsAssociatedPrime

/-- The quotient by an associated prime of `M` has dimension at most the dimension of the support
of `M`: every prime containing an associated prime lies in the support. -/
theorem ringKrullDim_quotient_le_supportDim (hp : IsAssociatedPrime p M) :
    ringKrullDim (R ⧸ p) ≤ Module.supportDim R M := by
  obtain ⟨-, z, rfl⟩ := hp
  rw [ringKrullDim_quotient, Module.supportDim]
  refine Order.krullDim_le_of_strictMono (fun q ↦ ⟨q.1,
    Module.mem_support_iff_exists_annihilator.2 ⟨z, ?_⟩⟩) fun _ _ h ↦ h
  rw [← Submodule.bot_colon']
  exact Ideal.le_radical.trans (SetLike.coe_subset_coe.1 ((PrimeSpectrum.mem_zeroLocus _ _).1 q.2))

/-- Let `M` be a finite module over a Noetherian ring and `x` an `M`-regular element of the
Jacobson radical of the annihilator of `M`. Every associated prime of `M` is contained in an
associated prime of `M ⧸ x M`. -/
theorem exists_le_isAssociatedPrime_quotSMulTop [IsNoetherianRing R] [Module.Finite R M] {x : R}
    (hp : IsAssociatedPrime p M) (reg : IsSMulRegular M x)
    (hx : x ∈ (Module.annihilator R M).jacobson) :
    ∃ q, IsAssociatedPrime q (QuotSMulTop x M) ∧ p ≤ q := by
  let N := Submodule.torsionBySet R M p
  -- Some element of `M` killed by `p` does not lie in `x M`: otherwise `N ≤ x N`, since `x` is
  -- `M`-regular, and Nakayama's lemma would force `N = 0`.
  obtain ⟨w, hwN, hw⟩ : ∃ w ∈ N, w ∉ x • (⊤ : Submodule R M) := by
    by_contra! h
    have hle : N ≤ Ideal.span {x} • N := by
      intro w hwN
      obtain ⟨w', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (h w hwN)
      refine Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) ?_
      rw [Submodule.mem_torsionBySet_iff] at hwN ⊢
      exact fun a ↦ reg <| by simp only [smul_comm x (a : R) w', hwN a, smul_zero]
    have hN : N = ⊥ := by
      rw [Submodule.eq_smul_of_le_smul_of_le_jacobson (IsNoetherian.noetherian N) hle
        ((Ideal.span_singleton_le_iff_mem _).2 hx), eq_bot_iff, ← Submodule.annihilator_top,
        ← Submodule.annihilator_smul (⊤ : Submodule R M)]
      exact Submodule.smul_mono le_rfl le_top
    obtain ⟨z, rfl⟩ := (isAssociatedPrime_iff.1 hp).2
    have hz : z ≠ 0 := by
      rintro rfl
      exact hp.isPrime.ne_top (by simp)
    refine hz <| (Submodule.mem_bot R).1 <| hN ▸ (Submodule.mem_torsionBySet_iff _ _).2 ?_
    exact fun a ↦ Submodule.mem_colon_singleton.1 a.2
  have hw' : (Submodule.Quotient.mk w : QuotSMulTop x M) ≠ 0 :=
    (Submodule.Quotient.mk_eq_zero _).not.2 hw
  obtain ⟨q, hq, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hw'
  refine ⟨q, hq, fun a ha ↦ hle <| Submodule.mem_colon_singleton.2 ?_⟩
  rw [← Submodule.Quotient.mk_smul, (Submodule.mem_torsionBySet_iff _ _).1 hwN ⟨a, ha⟩,
    Submodule.Quotient.mk_zero]
  exact Submodule.zero_mem _

end IsAssociatedPrime

section Algebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
  [Module R M] [Module S M] [IsScalarTower R S M]

namespace IsAssociatedPrime

/-- An associated prime of an `S`-module `M` contracts to an associated prime of `M` as an
`R`-module. -/
theorem comap {q : Ideal S} (hq : IsAssociatedPrime q M) :
    IsAssociatedPrime (q.comap (algebraMap R S)) M := by
  obtain ⟨hq, x, rfl⟩ := hq
  exact ⟨Ideal.comap_isPrime _ _, x, by
    rw [Ideal.comap_radical, Submodule.comap_colon_singleton, Submodule.restrictScalars_bot]⟩

/-- Let `S` be a Noetherian `R`-algebra. A maximal ideal of `R` that is an associated prime of an
`S`-module `M`, viewed as an `R`-module, is the contraction of an associated prime of `M` over
`S`. -/
theorem exists_isAssociatedPrime_comap_eq [IsNoetherianRing S] {p : Ideal R} [hmax : p.IsMaximal]
    (hp : IsAssociatedPrime p M) :
    ∃ q : Ideal S, IsAssociatedPrime q M ∧ q.comap (algebraMap R S) = p := by
  obtain ⟨-, x, hpx⟩ := hp
  have hx : x ≠ 0 := by
    rintro rfl
    exact hmax.ne_top (by simp [hpx])
  obtain ⟨q, hq, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing S x hx
  have := hq.isPrime
  -- The contraction of `q` is a prime containing the annihilator of `x` in `R`, hence `p`.
  refine ⟨q, hq, (hmax.eq_of_le (Ideal.comap_isPrime _ q).ne_top ?_).symm⟩
  have hcolon := Submodule.comap_colon_singleton (R := R) (⊥ : Submodule S M) x
  rw [Submodule.restrictScalars_bot] at hcolon
  rw [hpx, ← hcolon]
  exact (Ideal.comap_isPrime _ q).radical_le_iff.2 (Ideal.comap_mono hle)

end IsAssociatedPrime

end Algebra
end
end TAF_LiteralSource_0586

section TAF_LiteralSource_0587
/- Original module: TauCeti.RingTheory.Ideal.AssociatedPrime.Localization -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Associated primes and localization at a prime

For a module `M` over a Noetherian ring `R` and a prime `p`, this file characterises when the
maximal ideal of `R_p` is an associated prime of `M_p`.

## Main results

* `TauCeti.maximalIdeal_mem_associatedPrimes_localizedModule_iff`: the maximal ideal of `R_p` is
  associated to `M_p` exactly when `p` is an associated prime of `M`.
-/

public section

universe u v

open IsLocalRing

namespace TauCeti

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M]

open Module

/-- For a module `M` over a Noetherian ring `R` and a prime `p`, the maximal ideal of `R_p` is an
associated prime of `M_p` exactly when `p` is an associated prime of `M`. This upgrades Mathlib's
`Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes` to an iff. -/
theorem maximalIdeal_mem_associatedPrimes_localizedModule_iff {p : Ideal R} [p.IsPrime] :
    maximalIdeal (Localization.AtPrime p) ∈
        associatedPrimes (Localization.AtPrime p) (LocalizedModule p.primeCompl M) ↔
      p ∈ associatedPrimes R M := by
  refine ⟨fun h ↦ ?_, associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes⟩
  simpa [← Ideal.under_def, Localization.AtPrime.under_maximalIdeal] using
    associatedPrimes.comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
      p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) _ h (IsNoetherian.noetherian _)

end TauCeti
end
end TAF_LiteralSource_0587

section TAF_LiteralSource_0588
/- Original module: TauCeti.Algebra.Ring.Subgroup -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Additive closures in rings

This file gives criteria for the additive closure of a set in a ring to be closed under
multiplication, and hence to coincide with the underlying additive subgroup of the subring
generated by that set.

## Main results

* `TauCeti.AddSubgroup.mul_mem_closure_of_mul_mem`: products of elements of an additive closure
  remain in the closure when this holds for its generators.
* `AddSubgroup.closure_mul_closure`: the product of two additive closures is the additive
  closure of the pairwise products.
* `Subring.toAddSubgroup_closure_of_one_mem_of_mul_mem`: under the corresponding
  hypotheses, the subring and additive-subgroup closures have the same underlying additive group.
* `AddSubgroup.multiplierRing`: the subring of elements `x` with `x W ⊆ W`, for an additive
  subgroup `W` of a ring.
-/

public section

open scoped Pointwise

namespace TauCeti

variable {R : Type*} [NonUnitalNonAssocRing R]

/-- The product of two additive closures is the additive closure of the pairwise products.

This is the additive-subgroup analogue of `AddSubmonoid.closure_mul_closure` from
`Mathlib.Algebra.Ring.Submonoid.Pointwise`. -/
theorem _root_.AddSubgroup.closure_mul_closure (S T : Set R) :
    AddSubgroup.closure S * AddSubgroup.closure T = AddSubgroup.closure (S * T) := by
  apply AddSubgroup.toAddSubmonoid_injective
  simp only [AddSubgroup.mul_toAddSubmonoid, AddSubgroup.closure_toAddSubmonoid,
    AddSubmonoid.closure_union, AddSubmonoid.closure_neg,
    AddSubmonoid.sup_mul, AddSubmonoid.mul_sup, AddSubmonoid.closure_mul_closure,
    neg_mul, mul_neg, AddSubmonoid.neg_sup, neg_neg, sup_idem, sup_comm]

/-- If products of generators lie in their additive closure, then that additive closure is
closed under multiplication. -/
theorem AddSubgroup.mul_mem_closure_of_mul_mem {R : Type*} [NonUnitalNonAssocRing R] {s : Set R}
    (hs : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ AddSubgroup.closure s) {x y : R}
    (hx : x ∈ AddSubgroup.closure s) (hy : y ∈ AddSubgroup.closure s) :
    x * y ∈ AddSubgroup.closure s := by
  induction hx, hy using AddSubgroup.closure_induction₂ with
  | mem x y hx hy => exact hs x hx y hy
  | zero_left => simp
  | zero_right => simp
  | add_left _ _ _ _ _ _ hx hy => simpa [add_mul] using AddSubgroup.add_mem _ hx hy
  | add_right _ _ _ _ _ _ hx hy => simpa [mul_add] using AddSubgroup.add_mem _ hx hy
  | neg_left _ _ _ _ hx => simpa [neg_mul] using AddSubgroup.neg_mem _ hx
  | neg_right _ _ _ _ hx => simpa [mul_neg] using AddSubgroup.neg_mem _ hx

/-- If the additive closure of a set contains one and products of generators lie in that closure,
then it is the underlying additive subgroup of the subring closure of the set. -/
theorem _root_.Subring.toAddSubgroup_closure_of_one_mem_of_mul_mem {R : Type*} [NonAssocRing R]
    {s : Set R}
    (h1 : (1 : R) ∈ AddSubgroup.closure s)
    (hmul : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ AddSubgroup.closure s) :
    (Subring.closure s).toAddSubgroup = AddSubgroup.closure s := by
  refine le_antisymm (fun x hx => ?_) ((AddSubgroup.closure_le _).2 fun x hx => ?_)
  · rw [Subring.mem_toAddSubgroup] at hx
    induction hx using Subring.closure_induction with
    | mem x hx => exact AddSubgroup.subset_closure hx
    | zero => exact zero_mem _
    | one => exact h1
    | add _ _ _ _ hx hy => exact add_mem hx hy
    | neg _ _ hx => exact neg_mem hx
    | mul _ _ _ _ hx hy => exact AddSubgroup.mul_mem_closure_of_mul_mem hmul hx hy
  · exact Subring.mem_toAddSubgroup.2 (Subring.subset_closure hx)

/-- The *multiplier ring* of an additive subgroup `W` of a ring: the elements `x` with `x W ⊆ W`,
that is, the transporter of `W` into itself under left multiplication. It is a subring even when
`W` is not. -/
def _root_.AddSubgroup.multiplierRing {R : Type*} [Ring R] (W : AddSubgroup R) : Subring R where
  carrier := {x | ∀ z ∈ W, x * z ∈ W}
  one_mem' z hz := by rwa [one_mul]
  mul_mem' hx hy z hz := by
    rw [mul_assoc]
    exact hx _ (hy z hz)
  zero_mem' z _ := by
    rw [zero_mul]
    exact zero_mem W
  add_mem' hx hy z hz := by
    rw [add_mul]
    exact add_mem (hx z hz) (hy z hz)
  neg_mem' hx z hz := by
    rw [neg_mul]
    exact neg_mem (hx z hz)

@[simp]
theorem _root_.AddSubgroup.mem_multiplierRing {R : Type*} [Ring R] {W : AddSubgroup R} {x : R} :
    x ∈ W.multiplierRing ↔ ∀ z ∈ W, x * z ∈ W :=
  Iff.rfl

end TauCeti
end
end TAF_LiteralSource_0588

section TAF_LiteralSource_0589
/- Original module: TauCeti.RingTheory.Ideal.Operations -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Complements on ideal multiplication and the ideal action

This file collects general facts about the multiplication of ideals and about the action `I • N`
of an ideal on a module, complementing `Mathlib/RingTheory/Ideal/Operations.lean`.

## Main results

* `Ideal.eq_one_of_mul_eq_one`: a two-sided left factor of the unit ideal is the unit ideal.
  Over a commutative semiring, this implies that the divisor antidiagonal of the unit ideal
  is a singleton.
* `Ideal.toAddSubgroup_mul_eq_closure_mul`: additive generators of a product of ideals.
* `Ideal.smul_top_eq_top_of_pi`: an ideal that expands the whole of a product of modules expands
  the whole of every factor.
* `Ideal.smul_top_eq_comap_mul`: the action on an ideal identifies its product submodule.
* `Ideal.smul_top_eq_top_of_isIdempotentElem`: an idempotent ideal `I` satisfies `I • I = I`.
* `Ideal.span_range_fin_two_eq_top_iff`: a pair generates the unit ideal exactly when its entries
  are coprime.
* `LinearMap.apply_mem_of_mem_smul_top`: a linear functional carries `I • M` into `I`.
* `Module.Basis.mem_smul_top_iff`: for a module with a basis, `I • M` consists of the vectors
  whose coordinates all lie in `I`.
* `Ideal.span_insert_eq_top_of_subset`: a generating set `S` may be replaced by a set `S'`, both
  taken together with a common element `a`, as soon as every element of `S` is `a` itself or
  belongs to `S'`.
* `IsSMulRegular.of_span_singleton_le`: if a regular element belongs to the principal ideal
  generated by another element, then the latter is regular.
* `Ideal.span_pair_sq_eq_span_singleton_of_isCoprime`: if `x ^ 2 = z m` with `z` and `m`
  coprime, then `(z, x) ^ 2 = (z)`.
* `IsSMulRegular.span_singleton_mul_right_mono` and
  `IsSMulRegular.span_singleton_mul_right_inj`: multiplication by the principal ideal of a regular
  element preserves and reflects inclusion and equality of ideals.
* `Ideal.span_singleton_pow_sup_span_singleton_pow`: the left ideals generated by `a ^ j` and
  `a ^ m` have as supremum the left ideal generated by `a ^ min j m`.
* `Ideal.sup_pow_le_sup_pow_right`: modulo a two-sided ideal `I`, powers of
  `I ⊔ J` are controlled by the corresponding power of the left ideal `J`.
* `Ideal.span_pair_pow_eq_span_singleton`: if `z (1 - t) = x ^ n` with `t ∈ (x, z)` and
  the left ideals `(x, z)` and `(z)` are two-sided, then `(x, z) ^ n = (z)`.
* `Ideal.isTwoSided_span_of_subset_center`: a left ideal spanned by central elements is two-sided.
* `Ideal.coe_span_subset_of_forall_mul_mem`: a left ideal lies in an additive submonoid containing
  every left multiple of its generators.
* `Submodule.mem_span_algebraMap_smul_iff`: over an algebra `A`, the action on a submodule `N` of
  the left ideal spanned by a scalar `x` produces exactly the multiples `x • w` with `w ∈ N`.
* `Submodule.mem_span_range_smul_top_iff_exists_fun`: the action on `M` of the ideal generated by
  finitely many elements `fᵢ` produces exactly the sums `∑ fᵢ • mᵢ`.
* `Subalgebra.toSubmodule_sup_pow_restrictScalars_eq_top`: if a subalgebra and a principal left
  ideal additively span the ambient algebra, and the subalgebra contains a generator of the
  ideal, then the same holds with the ideal replaced by any power.
-/

public section

open scoped Pointwise

namespace Ideal

variable {R : Type*} [Ring R] {I J : Ideal R} {S T : Set R}

/-- If `S` and `T` additively generate the ideals `I` and `J`, then their pairwise products
additively generate `I * J`. -/
theorem toAddSubgroup_mul_eq_closure_mul
    (hI : I.toAddSubgroup = AddSubgroup.closure S)
    (hJ : J.toAddSubgroup = AddSubgroup.closure T) :
    (I * J).toAddSubgroup = AddSubgroup.closure (S * T) := by
  apply AddSubgroup.toAddSubmonoid_injective
  rw [Submodule.toAddSubgroup_toAddSubmonoid, _root_.Submodule.mul_toAddSubmonoid,
    ← Submodule.toAddSubgroup_toAddSubmonoid I, ← Submodule.toAddSubgroup_toAddSubmonoid J,
    hI, hJ, ← _root_.AddSubgroup.mul_toAddSubmonoid,
    AddSubgroup.closure_mul_closure]

section Mul

variable {R : Type*} [Semiring R] {I J : Ideal R}

/-- If a two-sided ideal times a left ideal is the unit ideal, then the first ideal is the
unit ideal. -/
theorem eq_one_of_mul_eq_one [I.IsTwoSided] (h : I * J = 1) : I = 1 := by
  rw [Ideal.one_eq_top] at h ⊢
  exact eq_top_mono Ideal.mul_le_left h

end Mul

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The product `I * J`, viewed as a submodule of `I`, is the action of `J` on `I`. -/
theorem smul_top_eq_comap_mul (I J : Ideal R) :
    J • (⊤ : Submodule R I) = Submodule.comap I.subtype (I * J) := by
  ext x
  simp only [Submodule.mem_smul_top_iff, Submodule.mem_comap, Submodule.coe_subtype,
    Ideal.smul_eq_mul, mul_comm J I]

/-- If `I * I = I`, then `I • I = I`: every element of `I` is a sum of products of two elements
of `I`. -/
theorem smul_top_eq_top_of_isIdempotentElem {I : Ideal R} (hI : IsIdempotentElem I) :
    I • (⊤ : Submodule R I) = ⊤ := by
  apply Submodule.map_injective_of_injective I.injective_subtype
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype, Ideal.smul_eq_mul, hI.eq]

/-- The two entries of a pair generate the unit ideal exactly when they are coprime. -/
theorem span_range_fin_two_eq_top_iff (v : Fin 2 → R) :
    span (Set.range v) = ⊤ ↔ IsCoprime (v 0) (v 1) := by
  have hv : Set.range v = {v 0, v 1} := by
    ext x
    simp [Fin.exists_fin_two, eq_comm]
  rw [hv, span_insert, sup_eq_top_iff_isCoprime]

end CommSemiring

section Pi

variable {R : Type*} [Semiring R] {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)]

/-- **Expanding a product expands every factor**: if `I • ⊤ = ⊤` in `∀ i, M i` then `I • ⊤ = ⊤` in
each `M i`. Thus properness of `I • ⊤` in one factor implies properness in the product. -/
theorem smul_top_eq_top_of_pi (I : Ideal R) (h : I • (⊤ : Submodule R (∀ i, M i)) = ⊤) (i : ι) :
    I • (⊤ : Submodule R (M i)) = ⊤ := by
  have := congrArg (Submodule.map (LinearMap.proj (R := R) (φ := M) i)) h
  rwa [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (Function.surjective_eval i)] at this

end Pi

end Ideal

namespace Submodule

variable {R A V : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid V]
  [Module R V] [Module A V] [IsScalarTower R A V]

/-- For an `R`-algebra `A`, possibly noncommutative, the action on a submodule `N` of the
left ideal spanned by a scalar `x : R` consists of the multiples `x • w` with `w ∈ N`.
This extends the membership criterion from `Submodule.ideal_span_singleton_smul` to
noncommutative algebras. -/
theorem mem_span_algebraMap_smul_iff (N : Submodule A V) (x : R) {v : V} :
    v ∈ Ideal.span {algebraMap R A x} • N ↔ ∃ w ∈ N, x • w = v := by
  constructor
  · intro hv
    refine Submodule.smul_induction_on hv (fun r hr w hw ↦ ?_)
      fun _ _ ⟨w, hw, h⟩ ⟨w', hw', h'⟩ ↦
        ⟨w + w', N.add_mem hw hw', by rw [smul_add, h, h']⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    exact ⟨a • w, N.smul_mem a hw, by rw [mul_smul, algebraMap_smul, smul_comm]⟩
  · rintro ⟨w, hw, rfl⟩
    rw [← algebraMap_smul A]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hw

end Submodule

namespace Submodule

variable {R M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype ι]

/-- The elements of `(f₁, …, f_r) M` are exactly the sums `∑ fᵢ mᵢ` with `mᵢ ∈ M`. -/
theorem mem_span_range_smul_top_iff_exists_fun {f : ι → R} {x : M} :
    x ∈ Ideal.span (Set.range f) • (⊤ : Submodule R M) ↔ ∃ m : ι → M, ∑ i, f i • m i = x := by
  rw [span_smul_eq, ← LinearMap.range_id, ← range_lsum_smul, LinearMap.mem_range,
    Finsupp.equivFunOnFinite.exists_congr_left]
  simp [Finsupp.sum_fintype]

end Submodule

namespace IsSMulRegular

variable {R : Type*} [Semiring R] {a b : R}

/-- If a regular element `b` belongs to the principal ideal generated by `a`, then `a` is regular.
Equivalently, regularity descends along an inclusion `(b) ⊆ (a)` of principal left ideals. -/
theorem of_span_singleton_le (hb : IsSMulRegular R b) (h : Ideal.span {b} ≤ Ideal.span {a}) :
    IsSMulRegular R a := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (h (Ideal.mem_span_singleton_self b))
  rw [← hr] at hb
  exact hb.of_mul

/-- Multiplication by the principal ideal of a regular element preserves and reflects
inclusion of ideals. This generalizes `Ideal.span_singleton_mul_right_mono`, which assumes
a domain and a nonzero element. -/
theorem span_singleton_mul_right_mono {R : Type*} [CommSemiring R] {a : R}
    (ha : IsSMulRegular R a) {I J : Ideal R} :
    Ideal.span {a} * I ≤ Ideal.span {a} * J ↔ I ≤ J := by
  constructor
  · intro h x hx
    obtain ⟨y, hy, hyx⟩ := (Submodule.mem_span_algebraMap_smul_iff J a).mp (by
      simpa only [Algebra.algebraMap_self_apply, Ideal.smul_eq_mul] using
        h (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self a) hx))
    exact ha hyx ▸ hy
  · exact Ideal.mul_mono_right

/-- Multiplication by the principal ideal of a regular element is injective on ideals. This
generalizes `Ideal.span_singleton_mul_right_inj`, which assumes a domain and a nonzero element. -/
theorem span_singleton_mul_right_inj {R : Type*} [CommSemiring R] {a : R}
    (ha : IsSMulRegular R a) {I J : Ideal R} :
    Ideal.span {a} * I = Ideal.span {a} * J ↔ I = J := by
  simp only [le_antisymm_iff, ha.span_singleton_mul_right_mono]

end IsSMulRegular

namespace Ideal

section Span

variable {R : Type*} [Semiring R] {a : R} {S S' : Set R}

/-- **Replacing one generating set by another**: if every element of `S` is either `a` itself or an
element of `S'`, then `S'` together with `a` generates the unit ideal as soon as `S` together with
`a` does. Note that `S'` need not be contained in `S`, and may be larger: the hypothesis constrains
only where the elements of `S` are found. Both spans contain `a`, so only the rest of `S` has to be
accounted for. -/
theorem span_insert_eq_top_of_subset (hsub : S ⊆ insert a S')
    (hspan : Ideal.span (insert a S) = ⊤) : Ideal.span (insert a S') = ⊤ :=
  eq_top_mono (Ideal.span_mono <| Set.insert_subset (Set.mem_insert _ _) hsub) hspan

/-- The left ideals generated by two powers of the same element have as supremum the left ideal
generated by the smaller power. -/
theorem span_singleton_pow_sup_span_singleton_pow (a : R) (j m : ℕ) :
    span {a ^ j} ⊔ span {a ^ m} = span {a ^ min j m} := by
  rcases le_total j m with h | h
  · rw [min_eq_left h, sup_eq_left, span_singleton_le_iff_mem, mem_span_singleton']
    exact ⟨a ^ (m - j), pow_sub_mul_pow a h⟩
  · rw [min_eq_right h, sup_eq_right, span_singleton_le_iff_mem, mem_span_singleton']
    exact ⟨a ^ (j - m), pow_sub_mul_pow a h⟩

/-- A left ideal lies in an additive submonoid `U` as soon as every left multiple of each of its
generators lies in `U`. -/
theorem coe_span_subset_of_forall_mul_mem {U : AddSubmonoid R} (h : ∀ x ∈ S, ∀ r : R, r * x ∈ U) :
    (span S : Set R) ⊆ U := by
  intro y hy
  have hy' : y ∈ (Submodule.span R S).toAddSubmonoid := hy
  rw [Submodule.span_eq_closure] at hy'
  refine (AddSubmonoid.closure_le (S := U)).mpr ?_ hy'
  rintro _ ⟨r, -, x, hx, rfl⟩
  exact h x hx r

variable {A : Type*} [Semiring A] {s : Set A}

/-- A left ideal spanned by central elements is two-sided. -/
theorem isTwoSided_span_of_subset_center (hs : s ⊆ Set.center A) :
    (Ideal.span s).IsTwoSided where
  mul_mem_of_left b hz := by
    refine Submodule.span_induction (p := fun z _ ↦ z * b ∈ Ideal.span s)
      (fun z hz ↦ ?_) (by simp) (fun x y _ _ hx hy ↦ ?_)
      (fun c x _ hx ↦ ?_) hz
    · rw [← (Semigroup.mem_center_iff.mp (hs hz) b)]
      exact Ideal.mul_mem_left _ b (Ideal.subset_span hz)
    · rw [add_mul]
      exact Ideal.add_mem _ hx hy
    · rw [smul_eq_mul, mul_assoc]
      exact Ideal.mul_mem_left _ c hx

end Span

end Ideal

namespace LinearMap

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A linear functional `f : M → R` carries `I • M` into the ideal `I`: the ideal action on `R`
itself is multiplication, and `f` is linear over it. -/
theorem apply_mem_of_mem_smul_top (f : M →ₗ[R] R) {I : Ideal R} [I.IsTwoSided] {x : M}
    (hx : x ∈ I • (⊤ : Submodule R M)) : f x ∈ I := by
  have := Submodule.smul_top_le_comap_smul_top I f hx
  rwa [Submodule.mem_comap, smul_eq_mul, Ideal.mul_top] at this

end LinearMap

namespace Module.Basis

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- For a module with a basis `b`, a vector lies in `I • M` exactly when all of its coordinates
lie in the ideal `I`. -/
theorem mem_smul_top_iff (b : Basis ι R M) {I : Ideal R} [I.IsTwoSided] {x : M} :
    x ∈ I • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  refine ⟨fun hx i ↦ LinearMap.apply_mem_of_mem_smul_top (b.coord i) hx, fun hx ↦ ?_⟩
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hx i) Submodule.mem_top

end Module.Basis

universe u

/-- A supremum of two two-sided ideals is two-sided. -/
instance (priority := low) Ideal.isTwoSided_sup {R : Type u} [Semiring R] (I J : Ideal R)
    [I.IsTwoSided] [J.IsTwoSided] : (I ⊔ J).IsTwoSided where
  mul_mem_of_left b ha := by
    obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp ha
    rw [add_mul]
    exact Submodule.add_mem _ (Ideal.mem_sup_left (I.mul_mem_right b hi))
      (Ideal.mem_sup_right (J.mul_mem_right b hj))

/-- The `n`-th power of the supremum of a two-sided ideal and a left ideal is contained in
the first ideal plus the `n`-th power of the second. -/
theorem Ideal.sup_pow_le_sup_pow_right {R : Type u} [Semiring R] (I J : Ideal R)
    [I.IsTwoSided] (n : ℕ) :
    (I ⊔ J) ^ n ≤ I ⊔ J ^ n := by
  induction n with
  | zero =>
      rw [Submodule.pow_zero, Submodule.pow_zero]
      exact le_sup_right
  | succ n ih =>
      rw [Submodule.pow_succ, Submodule.pow_succ]
      refine (Ideal.mul_mono_left ih).trans ?_
      rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
      exact sup_le
        (sup_le (Ideal.mul_le_left.trans le_sup_left)
          (Ideal.mul_le_left.trans le_sup_left))
        (sup_le (Ideal.mul_le_right.trans le_sup_left) le_sup_right)

/-- **A pair generating a power of one of its members.** If the left ideals `(x, z)` and
`(z)` are two-sided and `z (1 - t) = x ^ n` for some `t` in `(x, z)`, then `(x, z) ^ n = (z)`.
The two-sidedness hypotheses hold automatically in a commutative ring.
Modulo `z`, the ideal `(x, z)` becomes `(x)`, whose `n`-th power vanishes; conversely
`z = x ^ n (1 + t + ⋯ + t ^ (n - 1)) + z t ^ n`. -/
theorem Ideal.span_pair_pow_eq_span_singleton {R : Type u} [Ring R] {x z t : R} {n : ℕ}
    [(Ideal.span {x, z}).IsTwoSided] [(Ideal.span {z}).IsTwoSided]
    (hz : z * (1 - t) = x ^ n) (ht : t ∈ Ideal.span {x, z}) :
    Ideal.span {x, z} ^ n = Ideal.span {z} := by
  refine le_antisymm ?_ ?_
  · have hpow (k : ℕ) : Ideal.span {x, z} ^ k ≤ Ideal.span {x ^ k} ⊔ Ideal.span {z} := by
      induction k with
      | zero => simp [Submodule.pow_zero]
      | succ k ih =>
        calc Ideal.span {x, z} ^ (k + 1) =
            Ideal.span {x, z} ^ k * (Ideal.span {x} ⊔ Ideal.span {z}) := by
              rw [Submodule.pow_succ, ← Ideal.span_insert]
          _ = Ideal.span {x, z} ^ k * Ideal.span {x} ⊔
              Ideal.span {x, z} ^ k * Ideal.span {z} := Ideal.mul_sup _ _ _
          _ ≤ Ideal.span {x ^ (k + 1)} ⊔ Ideal.span {z} := by
            refine sup_le ?_ (Ideal.mul_le_right.trans le_sup_right)
            intro y hy
            obtain ⟨a, ha, rfl⟩ := Ideal.mem_mul_span_singleton.mp hy
            obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp (ih ha)
            obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hb
            rw [add_mul, mul_assoc, ← pow_succ]
            exact add_mem
              (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
              (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ hc))
    refine (hpow n).trans (sup_le ?_ le_rfl)
    rw [Ideal.span_singleton_le_iff_mem, ← hz]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self z)
  · have hz' : x ^ n * ∑ i ∈ Finset.range n, t ^ i + z * t ^ n = z := by
      rw [← hz, mul_assoc, mul_neg_geom_sum]
      simp [mul_sub]
    have hxm : x ∈ Ideal.span {x, z} := Ideal.subset_span (Set.mem_insert x _)
    rw [Ideal.span_singleton_le_iff_mem]
    suffices x ^ n * ∑ i ∈ Finset.range n, t ^ i + z * t ^ n ∈ Ideal.span {x, z} ^ n by
      rwa [hz'] at this
    exact add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hxm n))
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow ht n))

/-- **A pair whose square is principal.** In a commutative semiring, if `x ^ 2 = z m` with `z`
and `m` coprime, then `(z, x) ^ 2 = (z)`. For a squarefree integer `d = p m` with `p` prime,
applied to a square root `x` of `d`, this is the ramified factorization `(p) = (p, √d) ^ 2`. -/
theorem Ideal.span_pair_sq_eq_span_singleton_of_isCoprime {R : Type u} [CommSemiring R]
    {z x m : R} (hx : x ^ 2 = z * m) (hm : IsCoprime z m) :
    Ideal.span {z, x} ^ 2 = Ideal.span {z} := by
  refine le_antisymm ?_ ?_
  · rw [sq, Ideal.span_pair_mul_span_pair, Ideal.span_le]
    rintro y (rfl | rfl | rfl | rfl)
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self z)
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self z)
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self z)
    · rw [← sq, hx]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self z)
  · obtain ⟨u, v, huv⟩ := hm
    have hz : z = u * z ^ 2 + v * x ^ 2 := by
      rw [hx]
      calc z = z * (u * z + v * m) := by rw [huv, mul_one]
        _ = u * z ^ 2 + v * (z * m) := by ring
    have hzI : z ∈ Ideal.span {z, x} := Ideal.subset_span (Set.mem_insert z _)
    have hxI : x ∈ Ideal.span {z, x} := Ideal.subset_span (by simp)
    have h := add_mem (Ideal.mul_mem_left _ u (Ideal.pow_mem_pow hzI 2))
      (Ideal.mul_mem_left _ v (Ideal.pow_mem_pow hxI 2))
    rwa [← hz, ← Ideal.span_singleton_le_iff_mem] at h

namespace Subalgebra

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

/-- If every element of `S` is a sum of an element of a subalgebra `T` and an element of a
principal left ideal `I`, and `T` contains a generator of `I`, then the same holds with `I`
replaced by any power. -/
theorem toSubmodule_sup_pow_restrictScalars_eq_top {T : Subalgebra R S} {I : Ideal S} {π : S}
    (hπ : Ideal.span {π} = I) (hπT : π ∈ T)
    (h : T.toSubmodule ⊔ I.restrictScalars R = ⊤) (n : ℕ) :
    T.toSubmodule ⊔ (I ^ n).restrictScalars R = ⊤ := by
  subst I
  induction n with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    refine eq_top_iff.mpr fun s _ => ?_
    obtain ⟨t, ht, m, hm, rfl⟩ := Submodule.mem_sup.mp (h.ge Submodule.mem_top : s ∈ _)
    obtain ⟨u, rfl⟩ : ∃ u, u * π = m := by
      rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton'] at hm
      exact hm
    obtain ⟨t', ht', m', hm', rfl⟩ := Submodule.mem_sup.mp (ih.ge Submodule.mem_top : u ∈ _)
    refine Submodule.mem_sup.mpr ⟨t + t' * π, ?_, m' * π, ?_, by
      simp only [add_mul, add_assoc]⟩
    · rw [Subalgebra.mem_toSubmodule] at ht ht' ⊢
      exact add_mem ht (mul_mem ht' hπT)
    · rw [Submodule.restrictScalars_mem, Submodule.pow_succ]
      exact Ideal.mul_mem_mul hm' (Ideal.mem_span_singleton_self _)

end Subalgebra

end
end TAF_LiteralSource_0589

section TAF_LiteralSource_0590
/- Original module: TauCeti.Algebra.Module.Projective.LinearMap -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Hom spaces out of a projective module

Let `k` be a field and `A` a `k`-algebra. For a projective `A`-module `P` the functor
`Hom_A(P, -)` is exact, so when `Hom_A(P, M)` is finite-dimensional over `k` its dimension
is the sum of the dimensions of the hom spaces into a submodule of `M` and its quotient.

Exactness of `Hom_A(P, -)` also computes the maps from `P` into a reduction `V ⧸ x • V`, for `A`
an algebra over a commutative ring `R` and any `x : R`: they are the reductions modulo `x` of
the maps `P → V`. Over `R = ℤ_p` and `x = p`, this makes the number of maps from a projective
`ℤ_p[G]`-lattice into the reduction of another lattice a function of the
`ℤ_p`-module of maps between the lattices.

## Main results

* `TauCeti.finrank_linearMap_quotient_add_finrank_linearMap`: additivity of `dim_k Hom_A(P, -)`
  for a projective `P`.
* `TauCeti.compRight_mkQ_surjective`: every map from a projective `P` into `V ⧸ N` lifts to `V`.
* `TauCeti.ker_compRight_mkQ_eq_smul_top`: a map `P → V` vanishes modulo a non-zero-divisor `x`
  exactly when it is `x` times a map.
* `TauCeti.ker_compRight_mkQ_eq_smul_top_of_projective`: the same kernel computation for
  a projective `P` and any scalar `x`.
* `TauCeti.quotientSMulTopLinearMapEquiv`: `Hom_A(P, V) ⧸ x • Hom_A(P, V) ≃ Hom_A(P, V ⧸ x • V)`
  for a projective `P` and any scalar `x`.
-/

public section

namespace TauCeti

section Quotient

variable {R A P V : Type*} [CommSemiring R] [Ring A] [Algebra R A] [AddCommGroup P]
  [Module A P] [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]

variable (R P) [Module.Projective A P] in
/-- **Maps from a projective module into a quotient lift.** For `P` projective, every map
`P → V ⧸ N` is the reduction of a map `P → V`. -/
theorem compRight_mkQ_surjective (N : Submodule A V) :
    Function.Surjective (LinearMap.compRight (M := P) R N.mkQ) := fun g ↦
  Module.projective_lifting_property N.mkQ g N.mkQ_surjective

end Quotient

variable {k A P M : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup P] [Module A P] [Module.Projective A P]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [FiniteDimensional k (P →ₗ[A] M)]

variable (k P) in
/-- **`dim_k Hom_A(P, -)` is additive**, for `P` projective and `Hom_A(P, M)` finite-dimensional
over `k`: a submodule and its quotient split the dimension of the hom space out of `P`. Neither
`P` nor `M` needs to be finite-dimensional over `k`. -/
theorem finrank_linearMap_quotient_add_finrank_linearMap (N : Submodule A M) :
    Module.finrank k (P →ₗ[A] M ⧸ N) + Module.finrank k (P →ₗ[A] N)
      = Module.finrank k (P →ₗ[A] M) := by
  set α : (P →ₗ[A] N) →ₗ[k] (P →ₗ[A] M) := LinearMap.compRight k N.subtype with hα
  set β : (P →ₗ[A] M) →ₗ[k] (P →ₗ[A] M ⧸ N) := LinearMap.compRight k N.mkQ with hβ
  have hβsurj : Function.Surjective β := compRight_mkQ_surjective k P N
  have hαinj : Function.Injective α := N.injective_subtype.injective_linearMapComp_left
  have hker : LinearMap.ker β = LinearMap.range α := by
    ext g
    refine ⟨fun hg => ?_, ?_⟩
    · have hmem : ∀ p, g p ∈ N := fun p =>
        (Submodule.Quotient.mk_eq_zero N).mp (DFunLike.congr_fun hg p)
      exact ⟨g.codRestrict N hmem, by ext p; simp [hα]⟩
    · rintro ⟨g', rfl⟩
      ext p
      simp [hα, hβ]
  have h1 := LinearMap.finrank_range_add_finrank_ker β
  rw [hker, LinearMap.range_eq_top.mpr hβsurj, Submodule.topEquiv.finrank_eq,
    ← (LinearEquiv.ofInjective α hαinj).finrank_eq] at h1
  exact h1

section Reduction

open Pointwise

variable {R A P V : Type*} [Ring A] [AddCommGroup P] [Module A P]
  [AddCommGroup V] [Module A V] {x : R}

section CommSemiring

variable [CommSemiring R] [Algebra R A] [Module R V] [IsScalarTower R A V]

variable (P) in
/-- **Maps into `x • V` are multiples of `x`.** For `x : R` a non-zero-divisor on the `A`-module
`V`, a map `P → V` reduces to zero in `V ⧸ x • V` exactly when it is `x` times a map `P → V`. -/
theorem ker_compRight_mkQ_eq_smul_top (hx : IsSMulRegular V x) :
    LinearMap.ker (LinearMap.compRight (M := P) R
      (Ideal.span {algebraMap R A x} • (⊤ : Submodule A V)).mkQ) = x • ⊤ := by
  ext h
  simp only [LinearMap.mem_ker, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
    true_and]
  constructor
  · -- A map into `x • V` is `x` times a map, because multiplication by `x` is injective on `V`.
    intro h0
    have hp (p : P) : ∃ w, x • w = h p := by
      simpa only [Submodule.mem_top, true_and] using
        (Submodule.mem_span_algebraMap_smul_iff (⊤ : Submodule A V) x).mp
          ((Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun h0 p))
    choose w hw using hp
    refine ⟨{ toFun := w, map_add' := fun p p' ↦ hx ?_, map_smul' := fun a p ↦ hx ?_ }, ?_⟩
    · simp only [smul_add, hw, map_add]
    · simp only [RingHom.id_apply, hw, map_smul, smul_comm x a]
    · ext p
      exact hw p
  · rintro ⟨g, rfl⟩
    ext p
    simp only [LinearMap.compRight_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact (Submodule.mem_span_algebraMap_smul_iff ⊤ x).mpr ⟨g p, Submodule.mem_top, rfl⟩

variable (P) [Module.Projective A P] in
/-- For `P` projective, a map `P → V` vanishes modulo `x` exactly when it is `x` times a map,
without any regularity assumption on `x`. -/
@[simp]
theorem ker_compRight_mkQ_eq_smul_top_of_projective :
    LinearMap.ker (LinearMap.compRight (M := P) R
      (Ideal.span {algebraMap R A x} • (⊤ : Submodule A V)).mkQ) = x • ⊤ := by
  let N : Submodule A V := Ideal.span {algebraMap R A x} • ⊤
  let sx : V →ₗ[A] N := (DistribSMul.toLinearMap A V x).codRestrict N fun v =>
    (Submodule.mem_span_algebraMap_smul_iff ⊤ x).mpr ⟨v, Submodule.mem_top, rfl⟩
  have hsx : Function.Surjective sx := by
    intro v
    obtain ⟨w, _, hw⟩ := (Submodule.mem_span_algebraMap_smul_iff ⊤ x).mp v.property
    refine ⟨w, Subtype.ext ?_⟩
    simpa only [sx, LinearMap.codRestrict_apply, DistribSMul.toLinearMap_apply] using hw
  ext h
  simp only [LinearMap.mem_ker, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_top, true_and]
  constructor
  · intro hh
    have hmem : ∀ p, h p ∈ N := fun p =>
      (Submodule.Quotient.mk_eq_zero N).mp (LinearMap.congr_fun hh p)
    obtain ⟨g, hg⟩ := Module.projective_lifting_property sx (h.codRestrict N hmem) hsx
    refine ⟨g, ?_⟩
    ext p
    have hp := congrArg Subtype.val (LinearMap.congr_fun hg p)
    simpa only [sx, LinearMap.comp_apply, LinearMap.codRestrict_apply,
      DistribSMul.toLinearMap_apply, LinearMap.smul_apply] using hp
  · rintro ⟨g, rfl⟩
    ext p
    simp only [LinearMap.compRight_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact (Submodule.mem_span_algebraMap_smul_iff ⊤ x).mpr ⟨g p, Submodule.mem_top, rfl⟩

end CommSemiring

variable [CommRing R] [Algebra R A] [Module R V] [IsScalarTower R A V]
  [Module.Projective A P]

variable (P x) in
/-- **Maps from a projective module into a reduction.** Let `A` be an algebra over a commutative
ring `R`, let `P` be a projective `A`-module, and let `x : R`. Composition with `V → V ⧸ x • V`
identifies the maps `P → V ⧸ x • V` with the reductions modulo `x` of the maps `P → V`: every
map lifts because `P` is projective, and a map with values in `x • V` is `x` times a map. -/
noncomputable def quotientSMulTopLinearMapEquiv :
    ((P →ₗ[A] V) ⧸ x • (⊤ : Submodule R (P →ₗ[A] V))) ≃ₗ[R]
      (P →ₗ[A] V ⧸ Ideal.span {algebraMap R A x} • (⊤ : Submodule A V)) :=
  (Submodule.quotEquivOfEq _ _
    (ker_compRight_mkQ_eq_smul_top_of_projective (x := x) P).symm).trans <|
    LinearMap.quotKerEquivOfSurjective _ (compRight_mkQ_surjective R P _)

@[simp]
theorem quotientSMulTopLinearMapEquiv_mk (f : P →ₗ[A] V) :
    quotientSMulTopLinearMapEquiv P x (Submodule.Quotient.mk f) =
      (Ideal.span {algebraMap R A x} • (⊤ : Submodule A V)).mkQ ∘ₗ f := by
  rw [quotientSMulTopLinearMapEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, LinearMap.compRight_apply]

end Reduction

end TauCeti
end
end TAF_LiteralSource_0590

section TAF_LiteralSource_0591
/- Original module: TauCeti.RingTheory.Regular.LinearMap -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Regular sequences on modules of linear maps

A regular element on a module `N` remains regular on `M →ₗ[R] N`. More generally, a weakly
regular sequence on `N` of length at most two remains weakly regular on `M →ₗ[R] N`.
No local-ring, Noetherian, or finiteness hypotheses are needed for these transfer results.

## Main results

* `IsSMulRegular.linearMap`: a regular element remains regular on the module of linear maps.
* `IsSMulRegular.quotSMulTop_linearMap`: the second element remains regular after quotienting
  the module of linear maps by the first regular element.
* `RingTheory.Sequence.IsWeaklyRegular.linearMap`: weak regularity of sequences of length at
  most two passes from the target to the module of linear maps.
-/

public section

open RingTheory.Sequence Pointwise

/-- A regular element on the target is regular on the module of linear maps. -/
theorem IsSMulRegular.linearMap {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {scalar : R} (regular : IsSMulRegular N scalar) :
    IsSMulRegular (M →ₗ[R] N) scalar := by
  intro first second equality
  ext element
  apply regular
  simpa only [LinearMap.smul_apply] using congrArg (fun linear ↦ linear element) equality

section LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

/-- The second element of a weakly regular pair on the target remains regular after quotienting
the module of linear maps by the first element. -/
theorem IsSMulRegular.quotSMulTop_linearMap {first second : R}
    (regular : IsSMulRegular N first)
    (quotientRegular : IsSMulRegular (QuotSMulTop first N) second) :
    IsSMulRegular (QuotSMulTop first (M →ₗ[R] N)) second := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro linear membership
  obtain ⟨other, -, equality⟩ :=
    (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 membership
  have pointwise (element : M) : linear element ∈ first • (⊤ : Submodule R N) := by
    apply mem_of_isSMulRegular_quotient_of_smul_mem quotientRegular
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
      ⟨other element, Submodule.mem_top, congrArg (fun map ↦ map element) equality⟩
  have inKernel : linear ∈ LinearMap.ker (LinearMap.compRight (M := M) R
      (Ideal.span {algebraMap R R first} • (⊤ : Submodule R N)).mkQ) := by
    rw [LinearMap.mem_ker]
    ext element
    exact (Submodule.Quotient.mk_eq_zero _).mpr (by
      simpa only [Algebra.algebraMap_self_apply, Submodule.ideal_span_singleton_smul]
        using pointwise element)
  rwa [TauCeti.ker_compRight_mkQ_eq_smul_top M regular] at inKernel

/-- A weakly regular sequence of length at most two on the target is weakly regular on the
module of linear maps. -/
theorem RingTheory.Sequence.IsWeaklyRegular.linearMap {scalars : List R}
    (regular : IsWeaklyRegular N scalars) (length : scalars.length ≤ 2) :
    IsWeaklyRegular (M →ₗ[R] N) scalars := by
  cases scalars with
  | nil => exact .nil _ _
  | cons first tail =>
    obtain ⟨firstRegular, tailRegular⟩ := (isWeaklyRegular_cons_iff _ _ _).1 regular
    cases tail with
    | nil => exact (IsWeaklyRegular.nil _ _).cons firstRegular.linearMap
    | cons second rest =>
      have restEmpty : rest = [] := by
        have : rest.length = 0 := by
          simp only [List.length_cons] at length
          omega
        exact List.length_eq_zero_iff.mp this
      subst rest
      have secondRegular := (isWeaklyRegular_cons_iff _ _ _).1 tailRegular |>.1
      exact ((IsWeaklyRegular.nil _ _).cons
        (firstRegular.quotSMulTop_linearMap secondRegular)).cons firstRegular.linearMap

end LinearMap
end
end TAF_LiteralSource_0591

section TAF_LiteralSource_0592
/- Original module: TauCeti.Algebra.Category.ModuleCat.Ext.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Annihilators of `Ext` groups of modules

For modules `N` and `M` over a commutative ring `R`, the `R`-module `Ext N M n` is killed both by
the annihilator of `N` and by the annihilator of `M`, since multiplication by `r` on `Ext N M n`
is induced by multiplication by `r` on either argument. In particular `Ext N M n` vanishes when
these two annihilators are comaximal, for example `Ext (R ⧸ I) M n = 0` when `I M = M` for a
finite module `M`. A map out of a finite free module with image in `I F`, for an ideal `I` killing
`N`, is a combination of maps with coefficients in `I`, so it induces zero on `Ext N - n`; for
`N` the residue field of a local ring this is the property of minimal free presentations used to
compute depths.

## Main results

* `CategoryTheory.Abelian.Ext.smul_eq_zero_of_mem_annihilator_left` and
  `CategoryTheory.Abelian.Ext.smul_eq_zero_of_mem_annihilator_right`: elements of the annihilator
  of either argument act by zero on `Ext N M n`.
* `CategoryTheory.Abelian.Ext.subsingleton_of_annihilator_sup_eq_top`: `Ext N M n` vanishes when
  the annihilators of `N` and `M` are comaximal.
* `CategoryTheory.Abelian.Ext.comp_mk₀_eq_zero_of_range_le_smul_top`: if `I` annihilates `N`, a map
  `K ⟶ F` from a finite free module with image in `I • ⊤` induces zero on `Ext N - n`.
-/

public section

universe v u

open CategoryTheory

namespace CategoryTheory.Abelian

variable {R : Type u} [CommRing R] [Small.{v} R] {N M : ModuleCat.{v} R}

/-- An element of the annihilator of `N` acts by zero on `Ext N M n`. This restates
`Ext.postcomp_smul_id_eq_zero_of_mem_annihilator` as a statement about the scalar action. -/
theorem Ext.smul_eq_zero_of_mem_annihilator_left {r : R} (hr : r ∈ Module.annihilator R N)
    {n : ℕ} (x : Ext N M n) : r • x = 0 := by
  simpa [Ext.mk₀_smul] using
    congrArg (fun f ↦ f.hom x) (Ext.postcomp_smul_id_eq_zero_of_mem_annihilator (M := M) hr n)

/-- An element of the annihilator of `M` acts by zero on `Ext N M n`. -/
theorem Ext.smul_eq_zero_of_mem_annihilator_right {r : R} (hr : r ∈ Module.annihilator R M)
    {n : ℕ} (x : Ext N M n) : r • x = 0 := by
  have : r • 𝟙 M = 0 := by
    simp [← ModuleCat.lsmul_eq_smul_id, Module.mem_annihilator_iff_lsmul_eq_zero.mp hr]
  simp [Ext.smul_eq_comp_mk₀, this]

/-- `Ext N M n` vanishes when the annihilators of `N` and `M` are comaximal. -/
theorem Ext.subsingleton_of_annihilator_sup_eq_top
    (h : Module.annihilator R N ⊔ Module.annihilator R M = ⊤) (n : ℕ) :
    Subsingleton (Ext N M n) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h ▸ Submodule.mem_top : (1 : R) ∈ _)
  refine subsingleton_of_forall_eq 0 fun z ↦ ?_
  rw [← one_smul R z, ← hab, add_smul, smul_eq_zero_of_mem_annihilator_left ha,
    smul_eq_zero_of_mem_annihilator_right hb, add_zero]

/-- Let the ideal `I` annihilate `N`, and let `f : K ⟶ F` be a map out of a finite free module
whose image lies in `I • F`. Then `f` induces the zero map `Ext N K n → Ext N F n`. -/
theorem Ext.comp_mk₀_eq_zero_of_range_le_smul_top {K F : ModuleCat.{v} R} [Module.Free R K]
    [Module.Finite R K] {I : Ideal R} (hI : I ≤ Module.annihilator R N) (f : K ⟶ F)
    (hf : LinearMap.range f.hom ≤ I • ⊤) {n : ℕ} (x : Ext N K n) :
    x.comp (Ext.mk₀ f) (add_zero n) = 0 := by
  let b := Module.Free.chooseBasis R K
  -- A rank-one map `k ↦ φ k • y` with `y ∈ I • F` induces zero.
  have key (φ : K →ₗ[R] R) {y : F} (hy : y ∈ I • (⊤ : Submodule R F)) :
      x.comp (Ext.mk₀ (ModuleCat.ofHom (φ.smulRight y))) (add_zero n) = 0 := by
    refine Submodule.smul_induction_on hy (fun a ha y _ ↦ ?_) (fun y z hy hz ↦ ?_)
    · have : ModuleCat.ofHom (φ.smulRight (a • y)) = a • ModuleCat.ofHom (φ.smulRight y) := by
        ext k
        simp only [ModuleCat.hom_ofHom, ModuleCat.hom_smul, LinearMap.smulRight_apply,
          LinearMap.smul_apply]
        exact smul_comm _ _ _
      rw [this, Ext.mk₀_smul, Ext.comp_smul, smul_eq_zero_of_mem_annihilator_left (hI ha)]
    · have : ModuleCat.ofHom (φ.smulRight (y + z)) =
          ModuleCat.ofHom (φ.smulRight y) + ModuleCat.ofHom (φ.smulRight z) := by
        ext; simp
      rw [this, Ext.mk₀_add, Ext.comp_add, hy, hz, add_zero]
  -- Write `f` as a sum of rank-one maps, using a basis of `K`.
  have hsum : f = ∑ j, ModuleCat.ofHom ((b.coord j).smulRight (f (b j))) := by
    ext1
    refine b.ext fun j ↦ ?_
    simp [Finsupp.single_apply]
  rw [hsum, Ext.mk₀_sum, Ext.comp_sum]
  exact Finset.sum_eq_zero fun j _ ↦ key _ (hf ⟨b j, rfl⟩)

end CategoryTheory.Abelian
end
end TAF_LiteralSource_0592

section TAF_LiteralSource_0593
/- Original module: TauCeti.Data.ENat.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Successor inequalities in `ℕ∞`

Depth inequalities for a short exact sequence `0 → A → B → C → 0` bound one depth below by the
minimum of the other two, shifted by one. This file collects the `ℕ∞` arithmetic that combines
such bounds into equalities.

## Main results

* `ENat.le_of_inf_le_of_inf_le`: if `c ⊓ (b + 1) ≤ a` and `c ⊓ (a + 1) ≤ b`, then `c ≤ a`.
* `ENat.add_succ_eq_of_le_of_le`: the bounds `(b + p) ⊓ (b - 1) ≤ a` and `a + 1 ≤ b` give
  `a + (p + 1) = b + p`.
-/

public section

namespace ENat

/-- If `c ⊓ (b + 1) ≤ a` and `c ⊓ (a + 1) ≤ b`, then `c ≤ a`. -/
theorem le_of_inf_le_of_inf_le {a b c : ℕ∞} (ha : c ⊓ (b + 1) ≤ a)
    (hb : c ⊓ (a + 1) ≤ b) : c ≤ a := by
  induction a using ENat.recTopCoe <;> induction b using ENat.recTopCoe <;>
    induction c using ENat.recTopCoe <;> simp_all <;> norm_cast at * <;> omega

/-- If `(b + p) ⊓ (b - 1) ≤ a` and `a + 1 ≤ b`, then `a + (p + 1) = b + p`. -/
theorem add_succ_eq_of_le_of_le {a b : ℕ∞} {p : ℕ}
    (h₁ : (b + p) ⊓ (b - 1) ≤ a) (h₂ : a + 1 ≤ b) : a + (p + 1 : ℕ) = b + p := by
  induction b using ENat.recTopCoe with
  | top => simp_all
  | coe b =>
    induction a using ENat.recTopCoe with
    | top => simp at h₂
    | coe a =>
      norm_cast at h₂ ⊢
      rcases min_le_iff.mp h₁ with h | h <;> norm_cast at h <;> omega

end ENat
end
end TAF_LiteralSource_0593

section TAF_LiteralSource_0594
/- Original module: TauCeti.RingTheory.Localization.Module -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Localized linear maps

Facts about the localization `LocalizedModule.map S f : Mₛ → Nₛ` of a linear map at a
submonoid `S`:

* `LocalizedModule.map_comp`: localization is functorial, `(g ∘ f)ₛ = gₛ ∘ fₛ`.
* `LocalizedModule.bijective_map_lsmul`: multiplication by an element of `S` becomes bijective
  after localizing at `S`.
* `LinearMap.exists_comp_eq_lsmul_of_comp_localizedModule_map_eq_id`: if `M` is finitely
  presented and `N` is finitely generated, a left inverse of the localization `iₛ` of
  `i : N → M` descends to a map `φ : M → N` with `φ ∘ i` multiplication by some element of `S`.
* `LocalizedModule.bijective_map_dual_eval_iff`: if `M` and its dual are finitely presented, the
  map `M → M**` becomes bijective after localizing at `S` exactly when the localization `Mₛ` is
  reflexive over `Rₛ`. Taking duals commutes with localization for finitely presented modules,
  so `(M**)ₛ` is the double dual of `Mₛ` over `Rₛ`.

We also record that localization commutes with dividing by an element:

* `TauCeti.localizedQuotSMulTopEquiv`: localizing `M ⧸ a M` gives `M_S ⧸ a M_S`.
-/

public section

namespace LocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M N P : Type*} [AddCommMonoid M]
  [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- Localization of a composite is the composite of the localizations. -/
@[simp]
theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map S (g ∘ₗ f) = map S g ∘ₗ map S f := by
  ext x
  induction x using induction_on with
  | h m s => simp

variable {S} (M) in
/-- Multiplication by an element of `S` becomes bijective after localizing at `S`. -/
theorem bijective_map_lsmul {s : R} (hs : s ∈ S) :
    Function.Bijective (map S (LinearMap.lsmul R M s)) := by
  convert (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (mkLinearMap S M) ⟨s, hs⟩)
    using 1
  ext x
  induction x using induction_on with
  | h m t => simp [smul'_mk]

end LocalizedModule

namespace LinearMap

open LocalizedModule

variable {R : Type*} [CommRing R] {S : Submonoid R} {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Let `M` be finitely presented and `N` finitely generated. If the localization of
`i : N →ₗ[R] M` at `S` has a left inverse, then some `φ : M →ₗ[R] N` is a left inverse of `i` up
to multiplication by an element of `S`. -/
theorem exists_comp_eq_lsmul_of_comp_localizedModule_map_eq_id
    [Module.FinitePresentation R M] [Module.Finite R N]
    (i : N →ₗ[R] M) {ρ : LocalizedModule S M →ₗ[Localization S] LocalizedModule S N}
    (hρ : ρ ∘ₗ LocalizedModule.map S i = LinearMap.id) :
    ∃ s ∈ S, ∃ φ : M →ₗ[R] N, φ ∘ₗ i = LinearMap.lsmul R N s := by
  -- Lift `ρ` to `φ : M → N` with denominator `s`; then `φ ∘ i` and `s` agree after localizing,
  -- hence after multiplication by some `u ∈ S`.
  obtain ⟨φ, s, hφ⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S
    (mkLinearMap S N) (ρ.restrictScalars R ∘ₗ mkLinearMap S M)
  have key : mkLinearMap S N ∘ₗ (φ ∘ₗ i) = mkLinearMap S N ∘ₗ LinearMap.lsmul R N s := by
    ext n
    have h₁ := congr($hφ (i n))
    have h₂ := congr($hρ (LocalizedModule.mk n 1))
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, mkLinearMap_apply,
      LinearMap.smul_apply, map_mk, LinearMap.id_apply] at h₁ h₂
    simp [h₁, h₂, Submonoid.smul_def, smul'_mk]
  obtain ⟨u, hu⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S
    (mkLinearMap S N) _ _ key
  refine ⟨u * s, mul_mem u.2 s.2, (u : R) • φ, ?_⟩
  ext n
  simpa [Submonoid.smul_def, mul_smul] using congr($hu n)

end LinearMap

namespace LocalizedModule

open Module

variable {R : Type*} [CommRing R] (S : Submonoid R) (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ]
  [IsLocalization S Rₛ] {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] [Module Rₛ M'] [IsScalarTower R Rₛ M']

/-- Let `f : M → M'` be a localization of `M` at `S`, over the localization `Rₛ` of `R`. If `M`
and its dual are finitely presented, the canonical map `M → M**` becomes bijective after
localizing at `S` exactly when `M'` is reflexive over `Rₛ`. -/
theorem bijective_map_dual_eval_iff (f : M →ₗ[R] M') [IsLocalizedModule S f]
    [FinitePresentation R M] [FinitePresentation R (Dual R M)] :
    Function.Bijective (map S (Dual.eval R M)) ↔ Function.Bijective (Dual.eval Rₛ M') := by
  -- Localizing the dual and the double dual: `D` and `E` are localizations at `S`, because
  -- `M` and `M*` are finitely presented.
  let g := Algebra.linearMap R Rₛ
  let D : Dual R M →ₗ[R] Dual Rₛ M' := IsLocalizedModule.mapExtendScalars S f g Rₛ
  let E : Dual R (Dual R M) →ₗ[R] Dual Rₛ (Dual Rₛ M') :=
    IsLocalizedModule.mapExtendScalars S D g Rₛ
  -- Under these identifications, the localization of `M → M**` is `M' → M'**`.
  have key : IsLocalizedModule.map S f E (Dual.eval R M) =
      (Dual.eval Rₛ M').restrictScalars R := by
    refine IsLocalizedModule.linearMap_ext S f E ?_
    rw [IsLocalizedModule.map_comp]
    ext m : 1
    refine LinearMap.restrictScalars_injective R (IsLocalizedModule.linearMap_ext S D g ?_)
    ext φ
    simp [E, D, g]
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective f E, key,
    LinearMap.coe_restrictScalars]

end LocalizedModule

namespace TauCeti

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

variable (M) in
/-- Localization commutes with dividing a module by an element: for `a : R` and a submonoid `S`,
the localization of `M ⧸ a M` at `S` is `M_S ⧸ a M_S`, linearly over `R_S`. -/
noncomputable def localizedQuotSMulTopEquiv (a : R) (S : Submonoid R) :
    LocalizedModule S (QuotSMulTop a M) ≃ₗ[Localization S]
      QuotSMulTop (algebraMap R (Localization S) a) (LocalizedModule S M) :=
  (localizedQuotientEquiv _ _).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ (by
    rw [Submodule.localized, ← Submodule.ideal_span_singleton_smul,
      Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top,
      Ideal.map_span, Set.image_singleton, Submodule.ideal_span_singleton_smul])

/-- `TauCeti.localizedQuotSMulTopEquiv` sends `(m mod a M) / s` to `(m / s) mod a M_S`. -/
@[simp]
theorem localizedQuotSMulTopEquiv_mk (a : R) (S : Submonoid R) (m : M) (s : S) :
    localizedQuotSMulTopEquiv M a S (LocalizedModule.mk (Submodule.Quotient.mk m) s) =
      Submodule.Quotient.mk (LocalizedModule.mk m s) := by
  have h1 : localizedQuotSMulTopEquiv M a S
      (LocalizedModule.mkLinearMap S (QuotSMulTop a M) (Submodule.Quotient.mk m)) =
        Submodule.Quotient.mk (LocalizedModule.mkLinearMap S M m) := by
    rw [localizedQuotSMulTopEquiv, LinearEquiv.trans_apply]
    -- `localizedQuotientEquiv` is `IsLocalizedModule.linearEquiv` with scalars restricted.
    exact (congrArg _ (IsLocalizedModule.linearEquiv_symm_apply S
      (Submodule.toLocalizedQuotient S _) (LocalizedModule.mkLinearMap S _)
      (Submodule.Quotient.mk m))).trans (Submodule.quotEquivOfEq_mk _ _ _ _)
  -- Divide by `s` using `Localization S`-linearity.
  have hs {N : Type v} [AddCommGroup N] [Module R N] (x : N) :
      LocalizedModule.mk x s = Localization.mk (1 : R) s • LocalizedModule.mk x 1 := by
    rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
  rw [hs, map_smul, ← LocalizedModule.mkLinearMap_apply, h1, LocalizedModule.mkLinearMap_apply,
    ← Submodule.Quotient.mk_smul, hs]

end TauCeti
end
end TAF_LiteralSource_0594

section TAF_LiteralSource_0595
/- Original module: TauCeti.RingTheory.Depth.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Basic depth of modules

Mathlib defines the depth `IsLocalRing.depth M` of a module over a local ring `R` through the
vanishing of `Ext (R ⧸ 𝔪) M`, and identifies it, for a finite nonzero module over a Noetherian local
ring, with the supremum of the lengths of `M`-regular sequences in `𝔪`. This file relates depth
to dimension, quotients by regular sequences, short exact sequences and modules of linear maps,
and, after localization, to associated primes. The short exact sequence bounds hold for
`Ideal.depth I` over any commutative ring; the other results are for Noetherian local rings
or, after localization, Noetherian rings.
The regular-sequence transfer lemmas for linear maps live in
`TauCeti.RingTheory.Regular.LinearMap`.

## Main results

* `RingTheory.Sequence.IsRegular.mem_maximalIdeal`: over a local ring, every element of an
  `M`-regular sequence lies in the maximal ideal.
* `RingTheory.Sequence.IsRegular.length_le_supportDim`: over a Noetherian local ring, the length
  of an `M`-regular sequence on a finite module `M` is at most the dimension of its support.
* `IsLocalRing.depth_le_supportDim`: the depth of a finite nonzero module over a Noetherian local
  ring is at most the dimension of its support (Stacks, Lemma 10.72.3 (00LK)).
* `Ideal.depth_min_snd_trd_add_one_le_fst_of_exact`,
  `Ideal.depth_min_snd_fst_sub_one_le_trd_of_exact`, and
  `Ideal.depth_min_fst_trd_le_snd_of_exact` (with `IsLocalRing.` specializations): the depth
  inequalities for short exact sequences of linear maps, across module universes. They are the
  linear-map forms of Mathlib's `ModuleCat.depth_min_snd_trd_add_one_le_fst_right`,
  `ModuleCat.depth_min_snd_fst_sub_one_le_trd_right` and
  `ModuleCat.depth_min_fst_trd_le_snd_right`, transported through
  `ModuleCat.shortComplexOfConj_shortExact`.
* `ModuleCat.depth_trd_add_one_le_fst_of_comp_mk₀_eq_zero`: for a short exact sequence
  `0 → X₁ → X₂ → X₃ → 0` whose first map induces zero on `Ext N - n` for every `n`, the depth
  of `X₁` is at least one more than that of `X₃`. This sharpens Mathlib's
  `ModuleCat.depth_min_snd_trd_add_one_le_fst_right`.
* `IsLocalRing.depth_prod` and `IsLocalRing.depth_eq_depth_self_of_free`: the depth of a product
  is the minimum of the depths, so a nonzero finite free module has the depth of the ring.
* `IsLocalRing.depth_add_one_le_depth_ker`: for a free presentation `0 → K → F → M → 0` with
  `K` finite free and `K ⊆ 𝔪 F`, `depth M + 1 ≤ depth K`.
* `IsLocalRing.depth_quotSMulTop_succ_eq_depth`: dividing a finite module by an `M`-regular element
  of the maximal ideal lowers the depth by exactly one.
* `IsLocalRing.depth_quotSMulTop_eq_of_surjective` and
  `IsLocalRing.depth_eq_add_one_of_surjective`: the same statements for a module `Q` presented as
  the target of a surjection with kernel `x M`.
* `IsLocalRing.depth_add_length_eq_depth_of_isRegular`: dividing a finite module by an `M`-regular
  sequence `r₁, …, rₙ` lowers the depth by exactly `n`.
* `IsLocalRing.depth_eq_depth_of_surjective`: along a surjective homomorphism of local rings
  `R → T`, a finite `T`-module has the same depth over `R` as over `T`.
* `RingEquiv.depth_self_eq`: isomorphic Noetherian local rings have the same depth over
  themselves.
* `IsLocalRing.depth_hom_ge`: depth at least one or two passes from the target
  module to the module of linear maps (Stacks, Lemma 15.24.10 (0AV5)).
* `IsLocalRing.mem_span_singleton_of_forall_mul_mem_of_two_le_depth`: in a Noetherian local ring
  of depth at least two, `𝔪 c ⊆ (b)` for a nonzerodivisor `b` forces `c ∈ (b)`, so the maximal
  ideal is not an associated prime of `R ⧸ (b)`.
* `IsLocalRing.depth_le_ringKrullDim_quotient_of_isAssociatedPrime`: the depth of a finite module
  is at most `dim (R ⧸ p)` for every associated prime `p` of the module (Matsumura, Theorem 17.2).
* `IsLocalRing.depth_eq_zero_iff_nontrivial_linearMap` and
  `IsLocalRing.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes`: the depth vanishes exactly
  when the residue field maps nontrivially to the module, that is, when the maximal ideal is an
  associated prime.
* `TauCeti.depth_localizedModule_eq_zero_iff`: `M_p` has depth zero exactly when `p` is an
  associated prime of `M`, and `TauCeti.one_le_depth_localizedModule_iff` is its negation. This
  combines the depth-zero criterion with
  `TauCeti.maximalIdeal_mem_associatedPrimes_localizedModule_iff` from
  `TauCeti.RingTheory.Ideal.AssociatedPrime.Localization`.
* `TauCeti.depth_localizedModule_quotSMulTop_add_one`: dividing a finite module by an `M`-regular
  element of a prime `p` lowers the depth of the localization at `p` by exactly one.

The two quotient-depth results, together with Mathlib's
`Module.supportDim_add_length_eq_supportDim_of_isRegular`, make Cohen–Macaulayness stable under
quotients by regular sequences.
-/

public section

universe u v w t

open IsLocalRing RingTheory.Sequence Pointwise

/-- Over a local ring, every element of an `M`-regular sequence lies in the maximal ideal. -/
theorem RingTheory.Sequence.IsRegular.mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {rs : List R} (reg : IsRegular M rs) {r : R}
    (hr : r ∈ rs) : r ∈ maximalIdeal R := by
  by_contra h
  refine reg.top_ne_smul ?_
  rw [Ideal.eq_top_of_isUnit_mem (Ideal.ofList rs) (Ideal.subset_span hr)
    (notMem_maximalIdeal.1 h), Submodule.top_smul]

/-- Over a Noetherian local ring, the length of an `M`-regular sequence on a finite module `M` is at
most the dimension of the support of `M`. -/
theorem RingTheory.Sequence.IsRegular.length_le_supportDim {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {rs : List R} (reg : IsRegular M rs) :
    (rs.length : WithBot ℕ∞) ≤ Module.supportDim R M := by
  have := reg.quot_ofList_smul_nontrivial ⊤
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.1
    (Module.supportDim_ne_bot_of_nontrivial R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)))
  rw [← Module.supportDim_add_length_eq_supportDim_of_isRegular rs reg, ← he]
  exact_mod_cast le_add_self

namespace ModuleCat

open CategoryTheory Abelian

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- In a short exact sequence `0 → X₁ → X₂ → X₃ → 0` whose first map induces the zero map
`Ext N X₁ n → Ext N X₂ n` for every `n`, the depth of `X₁` with respect to `N` is at least one
more than that of `X₃`: the connecting maps `Ext N X₃ n → Ext N X₁ (n + 1)` are surjective. -/
theorem depth_trd_add_one_le_fst_of_comp_mk₀_eq_zero (N : ModuleCat.{v} R)
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    (h : ∀ (n : ℕ) (x : Ext N S.X₁ n), x.comp (Ext.mk₀ S.f) (add_zero n) = 0) :
    N.depth S.X₃ + 1 ≤ N.depth S.X₁ := by
  apply le_sSup
  intro i hi
  match i with
  | 0 =>
    -- `Hom (N, X₁) → Hom (N, X₂)` is injective, and zero by assumption.
    exact ⟨fun x y ↦ Ext.postcomp_mk₀_injective_of_mono N S.f (hf := hS.mono_f)
      ((h 0 x).trans (h 0 y).symm)⟩
  | i + 1 =>
    have hi' : (i : ℕ∞) < N.depth S.X₃ := by simpa using hi
    have := subsingleton_ext_of_lt_depth hi'
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ N hS x (h _ x) rfl
    obtain ⟨y₃, rfl⟩ := Ext.covariant_sequence_exact₁ N hS y (h _ y) rfl
    rw [Subsingleton.elim x₃ y₃]

end ModuleCat

namespace Ideal

section Exact

variable {R : Type u} [CommRing R] (I : Ideal R)
  {M : Type v} {N : Type w} {Q : Type t}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup Q] [Module R Q] [Small.{v} R] [Small.{w} R] [Small.{t} R]

private theorem depth_bounds_of_exact (first : M →ₗ[R] N) (second : N →ₗ[R] Q)
    (exactness : Function.Exact first second) (injective : Function.Injective first)
    (surjective : Function.Surjective second) :
    (Ideal.depth.{w, u} I (ModuleCat.of R N) ⊓ (Ideal.depth.{t, u} I (ModuleCat.of R Q) + 1) ≤
      Ideal.depth.{v, u} I (ModuleCat.of R M)) ∧
    (Ideal.depth.{w, u} I (ModuleCat.of R N) ⊓ (Ideal.depth.{v, u} I (ModuleCat.of R M) - 1) ≤
      Ideal.depth.{t, u} I (ModuleCat.of R Q)) ∧
    (Ideal.depth.{v, u} I (ModuleCat.of R M) ⊓ Ideal.depth.{t, u} I (ModuleCat.of R Q) ≤
      Ideal.depth.{w, u} I (ModuleCat.of R N)) := by
  let sourceEquiv : ULift.{max u v w t} M ≃ₗ[R] M := ULift.moduleEquiv
  let middleEquiv : ULift.{max u v w t} N ≃ₗ[R] N := ULift.moduleEquiv
  let targetEquiv : ULift.{max u v w t} Q ≃ₗ[R] Q := ULift.moduleEquiv
  have shortExact := ModuleCat.shortComplexOfConj_shortExact sourceEquiv middleEquiv
    targetEquiv first second exactness injective surjective
  have lower := ModuleCat.depth_min_snd_trd_add_one_le_fst_right
    (ModuleCat.of R (Shrink.{max u v w t} (R ⧸ I))) _ shortExact
  have upper := ModuleCat.depth_min_snd_fst_sub_one_le_trd_right
    (ModuleCat.of R (Shrink.{max u v w t} (R ⧸ I))) _ shortExact
  have middle := ModuleCat.depth_min_fst_trd_le_snd_right
    (ModuleCat.of R (Shrink.{max u v w t} (R ⧸ I))) _ shortExact
  have bounds :
      (Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} N)) ⊓
        (Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} Q)) + 1) ≤
        Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} M))) ∧
      (Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} N)) ⊓
        (Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} M)) - 1) ≤
        Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} Q))) ∧
      (Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} M)) ⊓
        Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} Q)) ≤
        Ideal.depth.{max u v w t, u} I (ModuleCat.of R (ULift.{max u v w t} N))) := by
    -- `Ideal.depth` is `ModuleCat.depth` from the shrunk residue module. After unfolding, the
    -- goal is `lower`, `upper`, `middle` up to the projections `S.X₁`, `S.X₂`, `S.X₃` of the
    -- explicit short complex, which `exact` unfolds.
    simp only [Ideal.depth]
    exact ⟨lower, upper, middle⟩
  rwa [Ideal.depth_eq_of_linearEquiv I sourceEquiv, Ideal.depth_eq_of_linearEquiv I middleEquiv,
    Ideal.depth_eq_of_linearEquiv I targetEquiv] at bounds

/-- For a short exact sequence of linear maps, the source depth with respect to an ideal is at
least the minimum of the middle depth and one plus the target depth. The modules may lie in
different universes. -/
@[stacks 00LX "(3), for linear maps in different universes"]
theorem depth_min_snd_trd_add_one_le_fst_of_exact (first : M →ₗ[R] N) (second : N →ₗ[R] Q)
    (exactness : Function.Exact first second) (injective : Function.Injective first)
    (surjective : Function.Surjective second) :
    Ideal.depth.{w, u} I (ModuleCat.of R N) ⊓ (Ideal.depth.{t, u} I (ModuleCat.of R Q) + 1) ≤
      Ideal.depth.{v, u} I (ModuleCat.of R M) :=
  (depth_bounds_of_exact I first second exactness injective surjective).1

/-- For a short exact sequence of linear maps, the target depth with respect to an ideal is at
least the minimum of the middle depth and the source depth minus one. The modules may lie in
different universes. -/
@[stacks 00LX "(2), for linear maps in different universes"]
theorem depth_min_snd_fst_sub_one_le_trd_of_exact (first : M →ₗ[R] N) (second : N →ₗ[R] Q)
    (exactness : Function.Exact first second) (injective : Function.Injective first)
    (surjective : Function.Surjective second) :
    Ideal.depth.{w, u} I (ModuleCat.of R N) ⊓ (Ideal.depth.{v, u} I (ModuleCat.of R M) - 1) ≤
      Ideal.depth.{t, u} I (ModuleCat.of R Q) :=
  (depth_bounds_of_exact I first second exactness injective surjective).2.1

/-- For a short exact sequence of linear maps, the middle depth with respect to an ideal is at
least the minimum of the source and target depths. The modules may lie in different universes. -/
@[stacks 00LX "(1), for linear maps in different universes"]
theorem depth_min_fst_trd_le_snd_of_exact (first : M →ₗ[R] N) (second : N →ₗ[R] Q)
    (exactness : Function.Exact first second) (injective : Function.Injective first)
    (surjective : Function.Surjective second) :
    Ideal.depth.{v, u} I (ModuleCat.of R M) ⊓ Ideal.depth.{t, u} I (ModuleCat.of R Q) ≤
      Ideal.depth.{w, u} I (ModuleCat.of R N) :=
  (depth_bounds_of_exact I first second exactness injective surjective).2.2

end Exact

end Ideal

namespace IsLocalRing

section Exact

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {M : Type v} {N : Type w} {Q : Type t}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup Q] [Module R Q] [Small.{v} R] [Small.{w} R] [Small.{t} R]

/-- Local-ring form of `Ideal.depth_min_snd_trd_add_one_le_fst_of_exact`. -/
@[stacks 00LX "(3), for linear maps in different universes"]
theorem depth_min_snd_trd_add_one_le_fst_of_exact (first : M →ₗ[R] N) (second : N →ₗ[R] Q)
    (exactness : Function.Exact first second) (injective : Function.Injective first)
    (surjective : Function.Surjective second) :
    depth (ModuleCat.of R N) ⊓ (depth (ModuleCat.of R Q) + 1) ≤
      depth (ModuleCat.of R M) :=
  Ideal.depth_min_snd_trd_add_one_le_fst_of_exact
    (M := M) (N := N) (Q := Q) (maximalIdeal R) first second exactness injective
    surjective

/-- Local-ring form of `Ideal.depth_min_snd_fst_sub_one_le_trd_of_exact`. -/
@[stacks 00LX "(2), for linear maps in different universes"]
theorem depth_min_snd_fst_sub_one_le_trd_of_exact (first : M →ₗ[R] N) (second : N →ₗ[R] Q)
    (exactness : Function.Exact first second) (injective : Function.Injective first)
    (surjective : Function.Surjective second) :
    depth (ModuleCat.of R N) ⊓ (depth (ModuleCat.of R M) - 1) ≤
      depth (ModuleCat.of R Q) :=
  Ideal.depth_min_snd_fst_sub_one_le_trd_of_exact
    (M := M) (N := N) (Q := Q) (maximalIdeal R) first second exactness injective
    surjective

/-- Local-ring form of `Ideal.depth_min_fst_trd_le_snd_of_exact`. -/
@[stacks 00LX "(1), for linear maps in different universes"]
theorem depth_min_fst_trd_le_snd_of_exact (first : M →ₗ[R] N) (second : N →ₗ[R] Q)
    (exactness : Function.Exact first second) (injective : Function.Injective first)
    (surjective : Function.Surjective second) :
    depth (ModuleCat.of R M) ⊓ depth (ModuleCat.of R Q) ≤
      depth (ModuleCat.of R N) :=
  Ideal.depth_min_fst_trd_le_snd_of_exact
    (M := M) (N := N) (Q := Q) (maximalIdeal R) first second exactness injective
    surjective

end Exact

section Free

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R]

/-- The depth of a product of two modules over a local ring is the minimum of their depths. -/
@[simp]
theorem depth_prod (M N : Type v) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    depth (ModuleCat.of R (M × N)) = depth (ModuleCat.of R M) ⊓ depth (ModuleCat.of R N) := by
  have hM := depth_min_snd_trd_add_one_le_fst_of_exact (LinearMap.inl R M N)
    (LinearMap.snd R M N) Function.Exact.inl_snd LinearMap.inl_injective LinearMap.snd_surjective
  have hN := depth_min_snd_trd_add_one_le_fst_of_exact (LinearMap.inr R M N)
    (LinearMap.fst R M N) Function.Exact.inr_fst LinearMap.inr_injective LinearMap.fst_surjective
  exact le_antisymm (le_inf (ENat.le_of_inf_le_of_inf_le hM hN) (ENat.le_of_inf_le_of_inf_le hN hM))
    (depth_min_fst_trd_le_snd_of_exact (LinearMap.inl R M N) (LinearMap.snd R M N)
      Function.Exact.inl_snd LinearMap.inl_injective LinearMap.snd_surjective)

/-- A nonzero finite free module over a local ring has the same depth as the ring. -/
theorem depth_eq_depth_self_of_free (M : Type v) [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] [Nontrivial M] :
    depth (ModuleCat.of R M) = depth (ModuleCat.of R R) := by
  have key (k : ℕ) (hk : 0 < k) :
      depth (ModuleCat.of R (Fin k → R)) = depth (ModuleCat.of R R) := by
    induction k, hk using Nat.le_induction with
    | base => exact depth_eq_of_linearEquiv (LinearEquiv.funUnique (Fin 1) R R)
    | succ k hk ih =>
      rw [← depth_eq_of_linearEquiv (Fin.consLinearEquiv R fun _ : Fin (k + 1) ↦ R), depth_prod,
        ih, inf_idem]
  let b := Module.Free.chooseBasis R M
  have := b.index_nonempty
  rw [depth_eq_of_linearEquiv (b.equivFun.trans
    (LinearEquiv.funCongrLeft R R (Fintype.equivFin _).symm)), key _ Fintype.card_pos]

open CategoryTheory Abelian in
/-- If `0 → K → F → M → 0` is a free presentation with `K` finite free and `K ⊆ 𝔪 F`, then
`depth M + 1 ≤ depth K`. -/
theorem depth_add_one_le_depth_ker {F M : Type v} [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] {g : F →ₗ[R] M} (hg : Function.Surjective g)
    [Module.Free R (LinearMap.ker g)] [Module.Finite R (LinearMap.ker g)]
    (hker : LinearMap.ker g ≤ maximalIdeal R • ⊤) :
    depth (ModuleCat.of R M) + 1 ≤ depth (ModuleCat.of R (LinearMap.ker g)) := by
  have hI : maximalIdeal R ≤ Module.annihilator R (Shrink.{v} (R ⧸ maximalIdeal R)) := by
    rw [(Shrink.linearEquiv R _).annihilator_eq, Ideal.annihilator_quotient]
  have hrange : LinearMap.range (LinearMap.ker g).subtype ≤ maximalIdeal R • ⊤ := by
    rwa [Submodule.range_subtype]
  have key (n : ℕ) (x : Ext (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R)))
      (ModuleCat.of R (LinearMap.ker g)) n) :
      x.comp (Ext.mk₀ (ModuleCat.ofHom (LinearMap.ker g).subtype)) (add_zero n) = 0 :=
    Ext.comp_mk₀_eq_zero_of_range_le_smul_top hI _ hrange x
  have h := ModuleCat.depth_trd_add_one_le_fst_of_comp_mk₀_eq_zero
    (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) (LinearMap.shortExact_shortComplexKer hg) key
  unfold IsLocalRing.depth Ideal.depth
  exact h

end Free

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R]
  {M : Type v} [AddCommGroup M] [Module R M]

/-- The depth of a finite nonzero module `M` over a Noetherian local ring is at most the dimension
of its support. Stacks, Lemma 10.72.3 (00LK). -/
@[stacks 00LK]
theorem depth_le_supportDim [IsNoetherianRing R] [Module.Finite R M] [Nontrivial M] :
    (depth (ModuleCat.of R M) : WithBot ℕ∞) ≤ Module.supportDim R M := by
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.1 (Module.supportDim_ne_bot_of_nontrivial R M)
  rw [← hd, WithBot.coe_le_coe, depth_eq_sSup_length_isRegular]
  refine sSup_le ?_
  rintro _ ⟨rs, reg, -, rfl⟩
  exact WithBot.coe_le_coe.1 (hd ▸ reg.length_le_supportDim)

/-- Dividing a module `M` by an `M`-regular element `x` lowers the depth by at most one. No
finiteness or Noetherian hypothesis is needed. -/
theorem depth_le_depth_quotSMulTop_succ {x : R} (reg : IsSMulRegular M x) :
    depth (ModuleCat.of R M) ≤ depth (ModuleCat.of R (QuotSMulTop x M)) + 1 := by
  have h := ModuleCat.depth_min_snd_fst_sub_one_le_trd_right
    (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) _
    (IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R M) reg)
  -- The long exact `Ext` sequence of `0 → M → M → M ⧸ x M → 0`; unfolding `smulShortComplex`
  -- exposes its three objects.
  simp only [ModuleCat.smulShortComplex] at h
  rw [min_eq_right tsub_le_self] at h
  exact tsub_le_iff_right.1 h

/-- Dividing a finite module `M` over a Noetherian local ring by an `M`-regular element `x` of the
maximal ideal lowers the depth by exactly one. -/
theorem depth_quotSMulTop_succ_eq_depth [IsNoetherianRing R] [Module.Finite R M]
    {x : R} (reg : IsSMulRegular M x) (hx : x ∈ maximalIdeal R) :
    depth (ModuleCat.of R (QuotSMulTop x M)) + 1 = depth (ModuleCat.of R M) := by
  refine le_antisymm ?_ (depth_le_depth_quotSMulTop_succ reg)
  cases subsingleton_or_nontrivial M
  · rw [depth_eq_top_of_subsingleton (ModuleCat.of R M)]
    exact le_top
  have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  -- Prepending `x` to an `(M ⧸ x M)`-regular sequence gives an `M`-regular sequence.
  rw [depth_eq_sSup_length_isRegular, depth_eq_sSup_length_isRegular]
  refine (ENat.sSup_add ?_).trans_le (iSup₂_le ?_)
  · exact ⟨_, [], IsRegular.nil R _, by simp, rfl⟩
  · rintro _ ⟨rs, reg', mem, rfl⟩
    exact le_sSup ⟨x :: rs, reg'.cons reg, List.forall_mem_cons.2 ⟨hx, mem⟩, by simp⟩

/-- If `g : M → Q` is a surjective linear map with kernel `x M`, then `M ⧸ x M` and `Q` have the
same depth. -/
theorem depth_quotSMulTop_eq_of_surjective {Q : Type v} [AddCommGroup Q] [Module R Q] {x : R}
    (g : M →ₗ[R] Q) (hg : Function.Surjective g) (hker : LinearMap.ker g = x • ⊤) :
    depth (ModuleCat.of R (QuotSMulTop x M)) = depth (ModuleCat.of R Q) :=
  depth_eq_of_linearEquiv <| (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (g.quotKerEquivOfSurjective hg)

/-- Over a Noetherian local ring, let `x` in the maximal ideal be regular on a finite module `M`
and let `g : M → Q` be a surjective linear map with kernel `x M`. Then the depth of `M` is one
more than the depth of `Q`. This is `IsLocalRing.depth_quotSMulTop_succ_eq_depth` with the
quotient replaced by an isomorphic module. -/
theorem depth_eq_add_one_of_surjective [IsNoetherianRing R] [Module.Finite R M] {Q : Type v}
    [AddCommGroup Q] [Module R Q] {x : R} (hx : x ∈ maximalIdeal R) (reg : IsSMulRegular M x)
    (g : M →ₗ[R] Q) (hg : Function.Surjective g) (hker : LinearMap.ker g = x • ⊤) :
    depth (ModuleCat.of R M) = depth (ModuleCat.of R Q) + 1 := by
  rw [← depth_quotSMulTop_eq_of_surjective g hg hker, depth_quotSMulTop_succ_eq_depth reg hx]

/-- Dividing a finite module `M` over a Noetherian local ring by an `M`-regular sequence
`r₁, …, rₙ` lowers the depth by exactly `n`. -/
theorem depth_add_length_eq_depth_of_isRegular [IsNoetherianRing R] [Module.Finite R M]
    (rs : List R) (reg : IsRegular M rs) :
    depth (ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))) + rs.length =
      depth (ModuleCat.of R M) := by
  induction rs generalizing M with
  | nil =>
    rw [List.length_nil, Nat.cast_zero, add_zero]
    exact depth_eq_of_linearEquiv (Submodule.quotEquivOfEqBot _ (by simp))
  | cons x rs ih =>
    obtain ⟨hx, hrs⟩ := (isRegular_cons_iff M x rs).1 reg
    rw [depth_eq_of_linearEquiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs),
      ← depth_quotSMulTop_succ_eq_depth hx (reg.mem_maximalIdeal List.mem_cons_self), ← ih hrs,
      List.length_cons, Nat.cast_succ, add_assoc]

omit [Small.{v} R] in
/-- The length of an `M`-regular sequence is at most `dim (R ⧸ p)` for every associated prime `p`
of `M`. -/
private theorem length_le_ringKrullDim_quotient_of_isRegular [IsNoetherianRing R]
    [Module.Finite R M] {rs : List R} (reg : IsRegular M rs) {p : Ideal R}
    (hp : IsAssociatedPrime p M) : (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  induction rs generalizing M p with
  | nil =>
    have := hp.isPrime
    simpa using ringKrullDim_nonneg_of_nontrivial (R := R ⧸ p)
  | cons x rs ih =>
    obtain ⟨hx, hrs⟩ := (isRegular_cons_iff M x rs).1 reg
    -- `p` lies in an associated prime `q` of `M ⧸ x M`. As `x` kills `M ⧸ x M` but is
    -- `M`-regular, `x ∈ q ∖ p`, so `dim (R ⧸ q) + 1 ≤ dim (R ⧸ p)`.
    obtain ⟨q, hq, hpq⟩ := hp.exists_le_isAssociatedPrime_quotSMulTop hx
      (maximalIdeal_le_jacobson _ (reg.mem_maximalIdeal List.mem_cons_self))
    have hxq : x ∈ q := hq.annihilator_le <| by
      rw [Submodule.annihilator_top]
      exact QuotSMulTop.mem_annihilator M x
    have hxp : x ∉ p := fun hxp ↦ by
      have hmem : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := Set.mem_biUnion hp hxp
      rw [biUnion_associatedPrimes_eq_compl_regular R M] at hmem
      exact hmem hx
    have := hp.isPrime
    calc ((x :: rs).length : WithBot ℕ∞) = rs.length + 1 := by simp
      _ ≤ ringKrullDim (R ⧸ q) + 1 := by gcongr; exact ih hrs hq
      _ ≤ ringKrullDim (R ⧸ p) := TauCeti.ringKrullDim_quotient_add_one_le_of_lt <|
        lt_of_le_of_ne hpq fun h ↦ hxp (h ▸ hxq)

/-- The depth of a finite module `M` over a Noetherian local ring is at most `dim (R ⧸ p)` for
every associated prime `p` of `M`. H. Matsumura, *Commutative Ring Theory*, Theorem 17.2. -/
theorem depth_le_ringKrullDim_quotient_of_isAssociatedPrime [IsNoetherianRing R]
    [Module.Finite R M] {p : Ideal R} (hp : IsAssociatedPrime p M) :
    (depth (ModuleCat.of R M) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  have : Nontrivial M :=
    not_subsingleton_iff_nontrivial.1 fun _ ↦ not_isAssociatedPrime_of_subsingleton hp
  have := hp.isPrime
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.1 <|
    ne_bot_of_le_ne_bot WithBot.zero_ne_bot (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ p))
  rw [← hd, WithBot.coe_le_coe, depth_eq_sSup_length_isRegular]
  refine sSup_le ?_
  rintro _ ⟨rs, reg, -, rfl⟩
  exact WithBot.coe_le_coe.1 (hd ▸ length_le_ringKrullDim_quotient_of_isRegular reg hp)

/-- The depth of a module over a local ring is zero exactly when there is a nonzero linear map to
it from the residue field `R ⧸ 𝔪`. This is Mathlib's
`ModuleCat.depth_eq_zero_iff_nontrivial_linearMap` with the universe-adjusting `Shrink` in the
definition of `IsLocalRing.depth` removed. -/
theorem depth_eq_zero_iff_nontrivial_linearMap :
    depth (ModuleCat.of R M) = 0 ↔ Nontrivial (R ⧸ maximalIdeal R →ₗ[R] M) := by
  rw [depth, Ideal.depth, ModuleCat.depth_eq_zero_iff_nontrivial_linearMap]
  exact ((Shrink.linearEquiv R (R ⧸ maximalIdeal R)).arrowCongr
    (LinearEquiv.refl R M)).nontrivial_congr

/-- The depth of a module over a Noetherian local ring is zero exactly when the maximal ideal is
an associated prime of the module, that is, when some nonzero element is killed by the maximal
ideal. -/
theorem depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes [IsNoetherianRing R] :
    depth (ModuleCat.of R M) = 0 ↔ maximalIdeal R ∈ associatedPrimes R M := by
  have : IsSimpleModule R (R ⧸ maximalIdeal R) :=
    isSimpleModule_iff_quot_maximal.2 ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
  rw [depth_eq_zero_iff_nontrivial_linearMap, AssociatedPrimes.mem_iff,
    isAssociatedPrime_iff_exists_injective_linearMap,
    and_iff_right (maximalIdeal.isMaximal R).isPrime]
  -- A nonzero linear map out of the simple module `R ⧸ 𝔪` is injective.
  refine ⟨fun ⟨f, g, hfg⟩ ↦ ⟨f - g, ?_⟩, fun ⟨f, hf⟩ ↦ ⟨f, 0, fun h ↦ ?_⟩⟩
  · exact (f - g).injective_or_eq_zero.resolve_right (sub_ne_zero.2 hfg)
  · exact zero_ne_one (hf (by simp [h]) : (0 : R ⧸ maximalIdeal R) = 1)

/-- Over a Noetherian local ring, depth at least `n ≤ 2` passes from a finite target module
to the module of linear maps from a finite module. Stacks, Lemma 15.24.10 (0AV5). -/
@[stacks 0AV5]
theorem depth_hom_ge {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] {M N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R M] [Module.Finite R N]
    {bound : ℕ} (bound_le_two : bound ≤ 2)
    (depth_bound : (bound : ℕ∞) ≤ depth (ModuleCat.of R N)) :
    (bound : ℕ∞) ≤ depth (ModuleCat.of R (M →ₗ[R] N)) := by
  classical
  cases subsingleton_or_nontrivial N
  · rw [depth_eq_top_of_subsingleton]
    exact le_top
  cases subsingleton_or_nontrivial (M →ₗ[R] N)
  · rw [depth_eq_top_of_subsingleton]
    exact le_top
  cases bound with
  | zero => exact zero_le
  | succ predecessor =>
    rw [depth_eq_sSup_length_isRegular] at depth_bound ⊢
    have strict := lt_of_lt_of_le
      (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self predecessor)) depth_bound
    obtain ⟨_, ⟨scalars, regular, membership, rfl⟩, strict⟩ := lt_sSup_iff.mp strict
    have length : predecessor + 1 ≤ scalars.length :=
      Nat.succ_le_of_lt (ENat.natCast_lt_natCast.mp strict)
    have prefixRegular : IsWeaklyRegular N (scalars.take (predecessor + 1)) :=
      ((isWeaklyRegular_append_iff N _ (scalars.drop (predecessor + 1))).1
        (by simpa only [List.take_append_drop] using regular.toIsWeaklyRegular)).1
    have prefixMembership : ∀ scalar ∈ scalars.take (predecessor + 1),
        scalar ∈ maximalIdeal R :=
      fun scalar member ↦ membership scalar (List.mem_of_mem_take member)
    have homRegular : IsRegular (M →ₗ[R] N) (scalars.take (predecessor + 1)) :=
      (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal prefixMembership).2
        (prefixRegular.linearMap (by simpa [List.length_take, Nat.min_eq_left length]
          using bound_le_two))
    exact le_sSup ⟨scalars.take (predecessor + 1), homRegular, prefixMembership,
      by simp [List.length_take, Nat.min_eq_left length]⟩

/-- Depth is unchanged under restriction of scalars along a surjective homomorphism of local rings
`R → T`: a finite `T`-module `M` has the same depth over `R` as over `T`. The `M`-regular
sequences in the maximal ideal of `T` are exactly the images of those in the maximal ideal of
`R`. -/
theorem depth_eq_depth_of_surjective [IsNoetherianRing R] {T : Type*} [CommRing T]
    [IsLocalRing T] [Algebra R T] [Small.{v} T] [Module T M] [IsScalarTower R T M]
    [Module.Finite T M] (hsurj : Function.Surjective (algebraMap R T)) :
    depth (ModuleCat.of R M) = depth (ModuleCat.of T M) := by
  have : IsLocalHom (algebraMap R T) := .of_surjective _ hsurj
  have : IsNoetherianRing T := isNoetherianRing_of_surjective R T (algebraMap R T) hsurj
  have : Module.Finite R T := .of_surjective (Algebra.linearMap R T) hsurj
  have : Module.Finite R M := .trans T M
  cases subsingleton_or_nontrivial M
  · rw [depth_eq_top_of_subsingleton, depth_eq_top_of_subsingleton]
  -- A sequence in `R` is `M`-regular in `𝔪_R` exactly when its image is `M`-regular in `𝔪_T`.
  have key (rs : List R) : (IsRegular M (rs.map (algebraMap R T)) ∧
      ∀ t ∈ rs.map (algebraMap R T), t ∈ maximalIdeal T) ↔
      (IsRegular M rs ∧ ∀ r ∈ rs, r ∈ maximalIdeal R) := by
    have hmem : (∀ t ∈ rs.map (algebraMap R T), t ∈ maximalIdeal T) ↔
        ∀ r ∈ rs, r ∈ maximalIdeal R := by
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact forall₂_congr fun r _ ↦ by rw [← Ideal.mem_comap, maximalIdeal_comap]
    rw [hmem, and_congr_left_iff]
    intro hm
    rw [isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hm,
      isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (hmem.2 hm),
      isWeaklyRegular_map_algebraMap_iff]
  rw [depth_eq_sSup_length_isRegular, depth_eq_sSup_length_isRegular]
  congr 1
  ext n
  refine ⟨fun ⟨rs, h, hm, hn⟩ ↦ ?_, fun ⟨ts, h, hm, hn⟩ ↦ ?_⟩
  · obtain ⟨h, hm⟩ := (key rs).2 ⟨h, hm⟩
    exact ⟨_, h, hm, by rw [List.length_map, hn]⟩
  · obtain ⟨rs, rfl⟩ : ∃ rs : List R, rs.map (algebraMap R T) = ts :=
      ⟨ts.map (Function.surjInv hsurj), by simp⟩
    obtain ⟨h, hm⟩ := (key rs).1 ⟨h, hm⟩
    exact ⟨rs, h, hm, by rw [← hn, List.length_map]⟩

/-- In a Noetherian local ring `R` of depth at least two, the maximal ideal is not an associated
prime of `R ⧸ (b)` for a nonzerodivisor `b`: if `𝔪 c ⊆ (b)`, then `c ∈ (b)`. -/
theorem mem_span_singleton_of_forall_mul_mem_of_two_le_depth {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (hdepth : 2 ≤ depth (ModuleCat.of R R)) {b c : R}
    (hb : IsSMulRegular R b) (hc : ∀ z ∈ maximalIdeal R, z * c ∈ Ideal.span {b}) :
    c ∈ Ideal.span {b} := by
  by_cases hbm : b ∈ maximalIdeal R
  swap
  · rw [Ideal.span_singleton_eq_top.2 (notMem_maximalIdeal.1 hbm)]
    exact Submodule.mem_top
  have hspan (x : R) : x ∈ b • (⊤ : Submodule R R) ↔ x ∈ Ideal.span {b} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  -- `depth (R ⧸ (b)) + 1 = depth R ≥ 2`, so no nonzero map `R ⧸ 𝔪 → R ⧸ (b)` exists
  have hdepth' : depth (ModuleCat.of R (QuotSMulTop b R)) ≠ 0 := fun h ↦ by
    have h1 := depth_quotSMulTop_succ_eq_depth hb hbm
    rw [h, zero_add] at h1
    exact absurd (h1 ▸ hdepth) (by decide)
  have : Subsingleton (R ⧸ maximalIdeal R →ₗ[R] QuotSMulTop b R) :=
    not_nontrivial_iff_subsingleton.1 (mt depth_eq_zero_iff_nontrivial_linearMap.2 hdepth')
  -- the map `r ↦ r c` is such a map, and it sends `1` to the class of `c`
  let g : R ⧸ maximalIdeal R →ₗ[R] QuotSMulTop b R :=
    (maximalIdeal R).liftQ (LinearMap.toSpanSingleton R _ (Submodule.Quotient.mk c))
      fun z hz ↦ by
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
          Submodule.Quotient.mk_eq_zero, hspan]
        exact hc z hz
  have hg : g (Submodule.Quotient.mk 1) = 0 := by
    rw [Subsingleton.elim g 0, LinearMap.zero_apply]
  rwa [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul,
    Submodule.Quotient.mk_eq_zero, hspan] at hg

end IsLocalRing

namespace RingEquiv

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-- A ring isomorphism carries regular sequences in the maximal ideal to regular sequences in the
maximal ideal, so it can only increase the depth of a Noetherian local ring over itself. -/
private theorem depth_self_le [IsNoetherianRing R] [IsNoetherianRing S] (e : R ≃+* S) :
    depth (ModuleCat.of R R) ≤ depth (ModuleCat.of S S) := by
  rw [depth_eq_sSup_length_isRegular, depth_eq_sSup_length_isRegular]
  refine sSup_le_sSup ?_
  rintro _ ⟨rs, reg, mem, rfl⟩
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.of_ringEquiv_symm e
  refine ⟨rs.map e, (e.toSemilinearEquiv.isRegular_congr' rs).1 reg, ?_, by simp⟩
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro r hr
  simpa [mem_maximalIdeal, mem_nonunits_iff] using mem r hr

/-- Isomorphic Noetherian local rings have the same depth over themselves. -/
theorem depth_self_eq [IsNoetherianRing R] (e : R ≃+* S) :
    depth (ModuleCat.of R R) = depth (ModuleCat.of S S) :=
  have : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  le_antisymm (depth_self_le e) (depth_self_le e.symm)

end RingEquiv

namespace TauCeti

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M]

open Module

/-- For a module `M` over a Noetherian ring `R` and a prime `p`, the localization `M_p` has depth
zero over `R_p` exactly when `p` is an associated prime of `M`. -/
theorem depth_localizedModule_eq_zero_iff {p : Ideal R} [p.IsPrime] :
    depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) = 0 ↔
      p ∈ associatedPrimes R M :=
  depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes.trans
    maximalIdeal_mem_associatedPrimes_localizedModule_iff

/-- For a module `M` over a Noetherian ring `R` and a prime `p`, the localization `M_p` has depth
at least one over `R_p` exactly when `p` is not an associated prime of `M`. -/
theorem one_le_depth_localizedModule_iff {p : Ideal R} [p.IsPrime] :
    1 ≤ depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) ↔
      p ∉ associatedPrimes R M := by
  rw [Order.one_le_iff_ne_zero, Ne, depth_localizedModule_eq_zero_iff]


/-- Let `M` be a finite module over a Noetherian ring and `a` an `M`-regular element of a prime
`p`. Dividing by `a` lowers the depth of the localization at `p` by exactly one:
`depth (M ⧸ a M)_p + 1 = depth M_p`. -/
theorem depth_localizedModule_quotSMulTop_add_one [Module.Finite R M] {a : R}
    (reg : IsSMulRegular M a) (p : Ideal R) [p.IsPrime] (ha : a ∈ p) :
    depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl (QuotSMulTop a M))) +
      1 = depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) := by
  let Rₚ := Localization.AtPrime p
  have hmax : algebraMap R Rₚ a ∈ maximalIdeal Rₚ :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p a).2 ha
  -- Localization commutes with the quotient by `a`.
  rw [IsLocalRing.depth_eq_of_linearEquiv (localizedQuotSMulTopEquiv M a p.primeCompl)]
  exact depth_quotSMulTop_succ_eq_depth (reg.of_isLocalizedModule (S := Rₚ) p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)) hmax

end TauCeti
end
end TAF_LiteralSource_0595

section TAF_LiteralSource_0596
/- Original module: TauCeti.RingTheory.Localization.Annihilator -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Annihilators of finite modules commute with localization

Let `M` be a finitely generated module over a commutative ring `R`, and let `M'` be its
localization at a submonoid `S`, a module over the localization `A` of `R` at `S`. Then

`Ann_A(M') = Ann_R(M) A`.

An element `r / s` annihilates `M'` exactly when every generator of `M` is killed by `r` after
multiplication by some element of `S`; the product of these finitely many elements of `S` then
multiplies `r` into `Ann_R(M)`. Without finite generation only the inclusion `⊇` holds.

This is the compatibility that lets the annihilators of the modules of sections of a
quasi-coherent module of finite type glue to an ideal sheaf.

## Main results

* `IsLocalizedModule.map_annihilator_le`: `Ann_R(M) A ≤ Ann_A(M')` for an arbitrary module `M`.
* `IsLocalizedModule.annihilator_eq_map`: `Ann_A(M') = Ann_R(M) A` for a finite module `M`.
* `IsLocalization.map_annihilator_span_singleton`: the annihilator of an element `a` of `R`,
  extended to `A`, is the annihilator of the image of `a`.

## References

* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Proposition 3.14.
-/

public section

open Submodule

variable {R : Type*} [CommRing R] (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
  [IsLocalization S A] {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] [Module A M'] [IsScalarTower R A M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]

namespace IsLocalizedModule

omit [IsLocalization S A] in
include S f in
/-- The extension of the annihilator of `M` annihilates every localization of `M`. This holds
without any finiteness assumption on `M`, and for any `R`-algebra `A` acting compatibly on `M'`. -/
theorem map_annihilator_le :
    (Module.annihilator R M).map (algebraMap R A) ≤ Module.annihilator A M' := by
  refine Ideal.map_le_iff_le_comap.mpr fun r hr ↦ Module.mem_annihilator.mpr fun m' ↦ ?_
  -- Write `m' = f m / s`; then `r • m' = f (r • m) / s = 0`.
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f m'
  simp [algebraMap_smul, ← IsLocalizedModule.mk'_smul, Module.mem_annihilator.mp hr]

include S f in
/-- **Annihilators of finite modules commute with localization.** If `M` is a finite `R`-module
and `f : M → M'` is the localization of `M` at a submonoid `S`, with `A` the localization of `R`
at `S`, then the annihilator of `M'` over `A` is the extension of the annihilator of `M`. -/
theorem annihilator_eq_map [Module.Finite R M] :
    Module.annihilator A M' = (Module.annihilator R M).map (algebraMap R A) := by
  classical
  refine le_antisymm (fun x hx ↦ ?_) (map_annihilator_le S A f)
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := R) (M := M)
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj S x
  -- Each element `m` of `M` is killed by `r` after multiplication by some `t m ∈ S`.
  have hgen (m : M) : ∃ t : S, (t : R) • r • m = 0 := by
    have hfm : f (r • m) = 0 := calc
      f (r • m) = (x * algebraMap R A s) • f m := by rw [map_smul, hrs, algebraMap_smul]
      _ = 0 := by rw [mul_smul, Module.mem_annihilator.mp hx]
    simpa [Submonoid.smul_def] using (IsLocalizedModule.eq_zero_iff S f).mp hfm
  choose t ht using hgen
  -- The product `u` of the `t m` over the generators multiplies `r` into `Ann_R(M)`.
  let u : S := ∏ m ∈ T, t m
  have hu : (u : R) * r ∈ Module.annihilator R M := by
    rw [← Submodule.annihilator_top, ← hT, Submodule.mem_annihilator_span]
    rintro ⟨m, hm⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem t hm
    have hcu : (u : R) * r = c * (t m * r) := by simp only [u, hc, Submonoid.coe_mul]; ring
    simp [hcu, mul_smul, ht m]
  -- `x = r / s = (u * r) / (u * s)`.
  have hx : x = algebraMap R A ((u : R) * r) * IsLocalization.mk' A (1 : R) (u * s) := by
    rw [← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.eq_mk'_iff_mul_eq]
    simp only [Submonoid.coe_mul, map_mul, ← hrs]
    ring
  rw [hx]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hu)

end IsLocalizedModule

namespace IsLocalization

include S in
/-- **The annihilator of an element commutes with localization.** The ideal of elements of the
localization `A` killing the image of `a` is the extension of the ideal of elements of `R` killing
`a`. This is the cyclic case `M = R ∙ a` of `IsLocalizedModule.annihilator_eq_map`, stated for the
principal ideal `(a)` of `R` and its image in `A` rather than for an abstract localized module. -/
theorem map_annihilator_span_singleton (a : R) :
    (Ideal.span {a}).annihilator.map (algebraMap R A) =
      (Ideal.span {algebraMap R A a}).annihilator := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_) fun y hy ↦ ?_
  · rw [Ideal.span, mem_annihilator_span_singleton, smul_eq_mul] at hx
    rw [Ideal.mem_comap, Ideal.span, mem_annihilator_span_singleton, smul_eq_mul, ← map_mul, hx,
      map_zero]
  · -- Write `y = x / s`; then `y * a = 0` means that `t * x * a = 0` for some `t ∈ S`.
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq S y
    rw [Ideal.span, mem_annihilator_span_singleton, smul_eq_mul, mul_comm,
      IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hy
    obtain ⟨t, ht⟩ := hy
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    refine ⟨t, t.2, ?_⟩
    rw [Ideal.span, mem_annihilator_span_singleton, smul_eq_mul, mul_assoc, mul_comm x, ht]

end IsLocalization
end
end TAF_LiteralSource_0596

section TAF_LiteralSource_0597
/- Original module: TauCeti.RingTheory.KrullDimension.Module -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Support dimension of a localized module

Let `M` be a finite module over a Noetherian ring `R` and `p` a prime containing the annihilator
of `M`. The support of the localization `M_p` over `R_p` is zero-dimensional exactly when `p` is a
minimal prime of the support of `M`. Primes of the support of `M_p` contract to primes of the
support of `M` below `p`, and a minimal prime strictly below `p` is associated to `M`, so it
survives in `M_p` as a non-maximal associated prime.

This is the dimension input to the characterization of Serre's condition `(S_1)` as the absence of
embedded primes.

## Main results

* `Module.exists_supportDim_eq_natCast`: a nonzero module over a ring of finite Krull dimension,
  such as a Noetherian local ring, has support of finite dimension.
* `Module.supportDim_localizedModule_nonpos_iff`: `M_p` has zero-dimensional support exactly when
  `p` is a minimal prime of the support of `M`.
-/

public section

open IsLocalRing

namespace Module

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The support of a nonzero module over a ring of finite Krull dimension, such as a Noetherian
local ring, has finite dimension: it is neither `⊥` nor `⊤`. -/
theorem exists_supportDim_eq_natCast [FiniteRingKrullDim R] [Nontrivial M] :
    ∃ k : ℕ, supportDim R M = k := by
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.1 (supportDim_ne_bot_of_nontrivial R M)
  have hd_top : d ≠ ⊤ := by
    rintro rfl
    exact (hd ▸ (supportDim_le_ringKrullDim R M).trans_lt ringKrullDim_lt_top).ne rfl
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.1 hd_top
  exact ⟨k, hd.symm⟩

/-- Let `M` be a finite module over a Noetherian ring and `p` a prime containing the annihilator
of `M`. The support of `M_p` has dimension zero exactly when `p` is a minimal prime of the support
of `M`. -/
theorem supportDim_localizedModule_nonpos_iff [IsNoetherianRing R] [Module.Finite R M]
    {p : Ideal R} [p.IsPrime] (hp : annihilator R M ≤ p) :
    supportDim (Localization.AtPrime p) (LocalizedModule p.primeCompl M) ≤ 0 ↔
      p ∈ (annihilator R M).minimalPrimes := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- A minimal prime `q ⊊ p` of the support is associated to `M`, so `q R_p` is an associated
    -- prime of `M_p` strictly below the maximal ideal, and `1 ≤ dim (R_p ⧸ q R_p) ≤ dim Supp M_p`.
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hp
    refine by_contra fun hpmin ↦ ?_
    have hqp : q < p := lt_of_le_of_ne hqp fun h ↦ hpmin (h ▸ hq)
    have := hq.isPrime
    have hdisj : Disjoint (p.primeCompl : Set R) q :=
      Set.disjoint_left.2 fun _ hx hxq ↦ hx (hqp.le hxq)
    set Q := q.map (algebraMap R (Localization.AtPrime p))
    have hQ : Q.under R = q := IsLocalization.under_map_of_isPrime_disjoint _ _ ‹_› hdisj
    have hQass : IsAssociatedPrime Q (LocalizedModule p.primeCompl M) :=
      associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
        p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) Q
        (by rw [← Ideal.under_def, hQ]
            exact associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hq)
    have := hQass.isPrime
    have hQlt : Q < maximalIdeal (Localization.AtPrime p) :=
      lt_of_le_of_ne (le_maximalIdeal this.ne_top) fun h ↦
        hqp.ne (hQ.symm.trans (Localization.AtPrime.eq_maximalIdeal_iff_under_eq.2 h))
    have hdim := (TauCeti.ringKrullDim_quotient_add_one_le_of_lt hQlt).trans
      hQass.ringKrullDim_quotient_le_supportDim
    rw [ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 inferInstance), zero_add] at hdim
    exact absurd (hdim.trans h) (by decide)
  · -- Every prime `Q` of the support of `M_p` contracts to a prime between the annihilator of `M`
    -- and `p`, hence to `p`, so `Q` is the maximal ideal and the support is a single point.
    refine Order.krullDim_nonpos_iff_forall_isMax.2 fun Q Q' _ ↦ ?_
    suffices key : ∀ Q ∈ support (Localization.AtPrime p) (LocalizedModule p.primeCompl M),
        Q.asIdeal = maximalIdeal (Localization.AtPrime p) by
      exact (Subtype.ext (PrimeSpectrum.ext ((key _ Q'.2).trans (key _ Q.2).symm))).le
    intro Q hQ
    have hQp : Q.asIdeal.under R ≤ p :=
      (Ideal.comap_mono (le_maximalIdeal Q.isPrime.ne_top)).trans_eq
        Localization.AtPrime.under_maximalIdeal
    -- The annihilator of `M` extends into the annihilator of `M_p`, hence into `Q`.
    have hann : annihilator R M ≤ Q.asIdeal.under R := Ideal.map_le_iff_le_comap.1 <|
      (IsLocalizedModule.map_annihilator_le p.primeCompl _
        (LocalizedModule.mkLinearMap p.primeCompl M)).trans (annihilator_le_of_mem_support hQ)
    exact Localization.AtPrime.eq_maximalIdeal_iff_under_eq.1
      (le_antisymm hQp (h.2 ⟨Ideal.IsPrime.under R Q.asIdeal, hann⟩ hQp))

end Module
end
end TAF_LiteralSource_0597

section TAF_LiteralSource_0598
/- Original module: TauCeti.RingTheory.CohenMacaulay.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Cohen–Macaulay modules over a local ring

A finite module `M` over a Noetherian local ring `R` is *Cohen–Macaulay* if `M = 0` or its depth
equals the dimension of its support (Stacks, Definition 10.103.1 (00N3)). Depth is Mathlib's
`IsLocalRing.depth`, defined through the vanishing of `Ext (R ⧸ 𝔪) M`, and the dimension of the
support is Mathlib's `Module.supportDim`. Since the depth of a finite nonzero module never exceeds
the dimension of its support (`IsLocalRing.depth_le_supportDim`), being Cohen–Macaulay is the
reverse inequality.

The zero module is Cohen–Macaulay by convention: its depth is `⊤` while its support dimension is
`⊥`, so the depth equation alone would exclude it.

## Main definitions and results

* `Module.IsCohenMacaulay R M`: the `R`-module `M` is Cohen–Macaulay.
* `Module.isCohenMacaulay_iff_supportDim_le_depth`: a finite nonzero module over a Noetherian local
  ring is Cohen–Macaulay if and only if the dimension of its support is at most its depth.
* `RingEquiv.isCohenMacaulay_self_iff`: being Cohen–Macaulay over itself is invariant under
  isomorphisms of Noetherian local rings.
* `Module.isCohenMacaulay_iff_isCohenMacaulay_self_of_surjective`: along a surjective homomorphism
  of local rings `R → T`, `T` is Cohen–Macaulay over `R` exactly when it is over itself.
* `IsLocalization.AtPrime.isCohenMacaulay_self_iff`: a localization of a Noetherian ring at a
  prime is Cohen–Macaulay over itself exactly when `Localization.AtPrime p` is.
* `Module.isCohenMacaulay_quotSMulTop_iff`: for an `M`-regular element `x` of the maximal ideal,
  `M ⧸ x M` is Cohen–Macaulay if and only if `M` is (Stacks, Lemma 10.103.5 (0C6G)), and
  `Module.isCohenMacaulay_quotient_ofList_smul_iff` is the same for an `M`-regular sequence.
* `Module.isCohenMacaulay_of_krullDimLE_zero`: every finite module over a Noetherian local ring of
  dimension zero, such as a field, is Cohen–Macaulay.
* `Module.isCohenMacaulay_self_of_isDomain_of_krullDimLE_one`: a Noetherian local domain of
  dimension at most one, such as a discrete valuation ring, is Cohen–Macaulay over itself.
* `Module.IsCohenMacaulay.ringKrullDim_quotient_eq_supportDim` and
  `Module.IsCohenMacaulay.associatedPrimes_eq_minimalPrimes`: a Cohen–Macaulay module is unmixed.
  For every associated prime `p`, the dimension of `R ⧸ p` is the dimension of the support, and
  the associated primes are exactly the minimal primes of the support, so there are no embedded
  primes (Stacks, Lemma 10.103.7 (0BUS)).
-/

public section

universe u v w

open IsLocalRing RingTheory.Sequence Pointwise

namespace Module

variable (R : Type u) [CommRing R] [IsLocalRing R] [Small.{v} R]
  (M : Type v) [AddCommGroup M] [Module R M]

/-- An `R`-module `M` over a local ring `R` is *Cohen–Macaulay* if it is zero or its depth equals
the dimension of its support. This is meant for finite modules over a Noetherian local ring, where
the depth never exceeds the dimension of the support. Stacks, Definition 10.103.1 (00N3). -/
@[stacks 00N3]
def IsCohenMacaulay : Prop :=
  Subsingleton M ∨ (depth (ModuleCat.of R M) : WithBot ℕ∞) = supportDim R M

/-- Unfolds `Module.IsCohenMacaulay`. -/
theorem isCohenMacaulay_iff : IsCohenMacaulay R M ↔
    Subsingleton M ∨ (depth (ModuleCat.of R M) : WithBot ℕ∞) = supportDim R M :=
  Iff.rfl

variable {R M}

/-- The zero module is Cohen–Macaulay. -/
theorem isCohenMacaulay_of_subsingleton [Subsingleton M] : IsCohenMacaulay R M :=
  Or.inl ‹_›

/-- A nonzero module is Cohen–Macaulay if and only if its depth equals the dimension of its
support. -/
theorem isCohenMacaulay_iff_depth_eq [Nontrivial M] :
    IsCohenMacaulay R M ↔ (depth (ModuleCat.of R M) : WithBot ℕ∞) = supportDim R M := by
  rw [isCohenMacaulay_iff, or_iff_right (not_subsingleton M)]

/-- The depth of a nonzero Cohen–Macaulay module equals the dimension of its support. -/
theorem IsCohenMacaulay.depth_eq [Nontrivial M] (h : IsCohenMacaulay R M) :
    (depth (ModuleCat.of R M) : WithBot ℕ∞) = supportDim R M :=
  isCohenMacaulay_iff_depth_eq.1 h

/-- A finite nonzero module over a Noetherian local ring is Cohen–Macaulay if and only if the
dimension of its support is at most its depth, the reverse inequality being
`IsLocalRing.depth_le_supportDim`. -/
theorem isCohenMacaulay_iff_supportDim_le_depth [IsNoetherianRing R] [Module.Finite R M]
    [Nontrivial M] :
    IsCohenMacaulay R M ↔ supportDim R M ≤ (depth (ModuleCat.of R M) : WithBot ℕ∞) := by
  rw [isCohenMacaulay_iff_depth_eq, le_antisymm_iff, and_iff_right depth_le_supportDim]

end Module

namespace LinearEquiv

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R] [Small.{w} R]
  {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N]

/-- Being Cohen–Macaulay is invariant under linear equivalence. -/
theorem isCohenMacaulay_iff (e : M ≃ₗ[R] N) :
    Module.IsCohenMacaulay R M ↔ Module.IsCohenMacaulay R N := by
  rw [Module.isCohenMacaulay_iff, Module.isCohenMacaulay_iff, e.toEquiv.subsingleton_congr,
    depth_eq_of_linearEquiv e, Module.supportDim_eq_of_equiv e]

end LinearEquiv

namespace RingEquiv

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [IsNoetherianRing R]

/-- A Noetherian local ring is Cohen–Macaulay over itself exactly when an isomorphic ring is. -/
theorem isCohenMacaulay_self_iff (e : R ≃+* S) :
    Module.IsCohenMacaulay R R ↔ Module.IsCohenMacaulay S S := by
  rw [Module.isCohenMacaulay_iff_depth_eq, Module.isCohenMacaulay_iff_depth_eq,
    Module.supportDim_self_eq_ringKrullDim, Module.supportDim_self_eq_ringKrullDim,
    e.depth_self_eq, ringKrullDim_eq_of_ringEquiv e]

end RingEquiv

namespace Module

variable {R : Type u} {T : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
  [CommRing T] [IsLocalRing T] [Algebra R T]

/-- Along a surjective homomorphism of local rings `R → T` with `R` Noetherian, `T` is
Cohen–Macaulay as an `R`-module exactly when it is Cohen–Macaulay over itself. For instance, a
quotient `R ⧸ I` that is Cohen–Macaulay as an `R`-module is a Cohen–Macaulay ring. -/
theorem isCohenMacaulay_iff_isCohenMacaulay_self_of_surjective
    (hsurj : Function.Surjective (algebraMap R T)) :
    IsCohenMacaulay R T ↔ IsCohenMacaulay T T := by
  have : Module.Finite R T := .of_surjective (Algebra.linearMap R T) hsurj
  have hann : annihilator R T = RingHom.ker (algebraMap R T) := by
    rw [← comap_annihilator (R := T), annihilator_eq_bot.mpr inferInstance,
      RingHom.ker_eq_comap_bot]
  rw [isCohenMacaulay_iff, isCohenMacaulay_iff, depth_eq_depth_of_surjective hsurj,
    supportDim_self_eq_ringKrullDim, supportDim_eq_ringKrullDim_quotient_annihilator, hann,
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj)]

end Module

namespace IsLocalization.AtPrime

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime]
  (B : Type v) [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalization.AtPrime B p]

/-- A localization `B` of a Noetherian ring `A` at a prime `p` is Cohen–Macaulay over itself
exactly when `Localization.AtPrime p` is. The local-ring instance on `B` is taken as an argument
so that it can be the one already present, as on the stalks of a scheme; it always holds, by
`IsLocalization.AtPrime.isLocalRing`. -/
theorem isCohenMacaulay_self_iff :
    Module.IsCohenMacaulay B B ↔
      Module.IsCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) :=
  have := IsLocalization.isNoetherianRing p.primeCompl B inferInstance
  (IsLocalization.algEquiv p.primeCompl B (Localization.AtPrime p)).toRingEquiv
    |>.isCohenMacaulay_self_iff

end IsLocalization.AtPrime

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- For an `M`-regular element `x` of the maximal ideal, `M ⧸ x M` is Cohen–Macaulay if and only if
`M` is. Stacks, Lemma 10.103.5 (0C6G). -/
@[stacks 0C6G]
theorem isCohenMacaulay_quotSMulTop_iff {x : R} (reg : IsSMulRegular M x)
    (hx : x ∈ maximalIdeal R) : IsCohenMacaulay R (QuotSMulTop x M) ↔ IsCohenMacaulay R M := by
  cases subsingleton_or_nontrivial M
  · exact iff_of_true isCohenMacaulay_of_subsingleton isCohenMacaulay_of_subsingleton
  have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  rw [isCohenMacaulay_iff_depth_eq, isCohenMacaulay_iff_depth_eq,
    ← depth_quotSMulTop_succ_eq_depth reg hx, ← supportDim_quotSMulTop_succ_eq_supportDim reg hx,
    WithBot.coe_add, WithBot.coe_one, ENat.WithBot.add_one_cancel]

/-- For an `M`-regular sequence `r₁, …, rₙ`, `M ⧸ (r₁, …, rₙ) M` is Cohen–Macaulay if and only if
`M` is. Stacks, Lemma 10.103.5 (0C6G), applied `n` times. -/
theorem isCohenMacaulay_quotient_ofList_smul_iff (rs : List R) (reg : IsRegular M rs) :
    IsCohenMacaulay R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) ↔ IsCohenMacaulay R M := by
  have := reg.nontrivial
  have := reg.quot_ofList_smul_nontrivial ⊤
  rw [isCohenMacaulay_iff_depth_eq, isCohenMacaulay_iff_depth_eq,
    ← depth_add_length_eq_depth_of_isRegular rs reg,
    ← supportDim_add_length_eq_supportDim_of_isRegular rs reg, WithBot.coe_add,
    WithBot.coe_natCast, ENat.WithBot.add_natCast_cancel]

/-- Every finite module over a Noetherian local ring of dimension zero is Cohen–Macaulay. -/
theorem isCohenMacaulay_of_krullDimLE_zero [Ring.KrullDimLE 0 R] : IsCohenMacaulay R M := by
  cases subsingleton_or_nontrivial M
  · exact isCohenMacaulay_of_subsingleton
  refine isCohenMacaulay_iff_supportDim_le_depth.2 <|
    (supportDim_le_ringKrullDim R M).trans <| (Ring.krullDimLE_iff.1 ‹_›).trans ?_
  exact_mod_cast zero_le

/-- Over a Noetherian local ring, the quotient by an associated prime of a Cohen–Macaulay module
has the dimension of the support of the module. Stacks, Lemma 10.103.7 (0BUS); H. Matsumura,
*Commutative Ring Theory*, Theorem 17.3 (i). -/
@[stacks 0BUS]
theorem IsCohenMacaulay.ringKrullDim_quotient_eq_supportDim (h : IsCohenMacaulay R M)
    {p : Ideal R} (hp : IsAssociatedPrime p M) : ringKrullDim (R ⧸ p) = supportDim R M := by
  have : Nontrivial M :=
    not_subsingleton_iff_nontrivial.1 fun _ ↦ not_isAssociatedPrime_of_subsingleton hp
  exact le_antisymm hp.ringKrullDim_quotient_le_supportDim
    (h.depth_eq ▸ depth_le_ringKrullDim_quotient_of_isAssociatedPrime hp)

/-- The associated primes of a Cohen–Macaulay module over a Noetherian local ring are the minimal
primes of its support: a Cohen–Macaulay module has no embedded primes. Stacks, Lemma 10.103.7
(0BUS). -/
@[stacks 0BUS]
theorem IsCohenMacaulay.associatedPrimes_eq_minimalPrimes (h : IsCohenMacaulay R M) :
    associatedPrimes R M = (annihilator R M).minimalPrimes := by
  refine Set.Subset.antisymm (fun p hp ↦ ?_)
    (associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M)
  have hp : IsAssociatedPrime p M := AssociatedPrimes.mem_iff.1 hp
  have : Nontrivial M :=
    not_subsingleton_iff_nontrivial.1 fun _ ↦ not_isAssociatedPrime_of_subsingleton hp
  refine ⟨⟨hp.isPrime, Submodule.annihilator_top (R := R) (M := M) ▸ hp.annihilator_le⟩,
    fun q ⟨hq, hann⟩ hqp ↦ by_contra fun hpq ↦ ?_⟩
  -- A prime `q ⊊ p` of the support would give `dim (R ⧸ p) + 1 ≤ dim (R ⧸ q) ≤ dim Supp M`,
  -- while `dim (R ⧸ p) = dim Supp M` is finite.
  have hle := (TauCeti.ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_not_ge hqp hpq)).trans
    (supportDim_eq_ringKrullDim_quotient_annihilator R M ▸
      ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hann))
  rw [h.ringKrullDim_quotient_eq_supportDim hp] at hle
  obtain ⟨k, hk⟩ := exists_supportDim_eq_natCast (R := R) (M := M)
  rw [hk] at hle
  exact absurd (by exact_mod_cast hle : k + 1 ≤ k) (Nat.not_succ_le_self k)

end Module

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]

/-- A Noetherian local domain of dimension at most one is Cohen–Macaulay over itself. -/
theorem isCohenMacaulay_self_of_isDomain_of_krullDimLE_one [Ring.KrullDimLE 1 R] :
    IsCohenMacaulay R R := by
  rw [isCohenMacaulay_iff_supportDim_le_depth, supportDim_self_eq_ringKrullDim]
  by_cases hm : maximalIdeal R = ⊥
  · rw [ringKrullDim_eq_zero_of_isField ((isField_iff_maximalIdeal_eq).2 hm)]
    exact_mod_cast zero_le
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  rw [← depth_quotSMulTop_succ_eq_depth (IsSMulRegular.of_ne_zero hx0) hx]
  refine (Ring.krullDimLE_iff.1 ‹_›).trans ?_
  exact_mod_cast le_add_self

example (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V] [Module.Finite K V] :
    IsCohenMacaulay K V :=
  isCohenMacaulay_of_krullDimLE_zero

example (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] : IsCohenMacaulay A A :=
  isCohenMacaulay_self_of_isDomain_of_krullDimLE_one

end Module
end
end TAF_LiteralSource_0598

section TAF_LiteralSource_0599
/- Original module: TauCeti.RingTheory.KrullDimension.Regular -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Krull dimension of a principal quotient

For a Noetherian ring, quotienting by an element in the Jacobson radical that lies outside every
minimal prime gives `dim (R ⧸ (x)) + 1 = dim R`. This is the ring form of Mathlib's
`Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson`. Applied to a
two-dimensional Noetherian local ring, it says that dividing out a non-zero-divisor of `𝔪`
leaves a curve, a ring of dimension one, and in a local domain, where the only minimal prime is
`0`, that applies to every nonzero element of `𝔪`. Conversely, in a local ring an element with
`dim (R ⧸ (x)) + 1 = dim R` lies in `𝔪`.

Over a Noetherian ring, each element of the Jacobson radical of the annihilator of a finite
module lowers the dimension of its support by at most one, so `dim M ≤ dim M ⧸ (r₁, …, rₙ) M + n`
for such `r₁, …, rₙ` (`Module.supportDim_le_supportDim_quotient_add_length_of_mem_jacobson`), in
particular for `r₁, …, rₙ ∈ 𝔪` over a local ring
(`Module.supportDim_le_supportDim_quotient_add_length`). This is the inequality
that the regular case `Module.supportDim_add_length_eq_supportDim_of_isRegular` turns into an
equality.
-/

public section

namespace TauCeti

open Ideal Pointwise _root_.IsLocalRing

/-- In a Noetherian ring, for `x` in the Jacobson radical outside every minimal prime,
`dim R ⧸ (x) + 1 = dim R`. -/
@[stacks 0B52 "the equality case"]
theorem
  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_notMem_minimalPrimes_of_mem_jacobson
    {R : Type*} [CommRing R] [IsNoetherianRing R] {x : R}
    (hmin : ∀ p ∈ minimalPrimes R, x ∉ p) (hx : x ∈ Ring.jacobson R) :
    ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R := by
  have h : span {x} = x • (⊤ : Ideal R) := by simp [← Submodule.ideal_span_singleton_smul]
  have hann : Module.annihilator R R = ⊥ :=
    Module.annihilator_eq_bot.mpr ((faithfulSMul_iff_algebraMap_injective R R).mpr fun _ _ h ↦ h)
  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R h).toRingEquiv,
    ← Module.supportDim_quotient_eq_ringKrullDim, ← Module.supportDim_self_eq_ringKrullDim]
  exact Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson
    (by rwa [hann]) ((Module.annihilator R R).ringJacobson_le_jacobson hx)

/-- **A general hyperplane section of a two-dimensional local ring is a curve of dimension one.**
In a Noetherian local ring `(R, 𝔪)` of Krull dimension two, the quotient by an element
`f ∈ 𝔪` that is a non-zero-divisor has dimension one:
`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim` drops the dimension by one along such
an `f`. A nonzero element of a local domain is a non-zero-divisor, so in a local domain a nonzero
`f ∈ 𝔪` does so; in particular a parameter `f ∈ 𝔪 \ 𝔪²` of a regular local ring, which is nonzero,
does so, and for a regular local ring this is the local form of the fact that a Cartier divisor on
a regular surface is cut out by a single equation. -/
theorem ringKrullDim_quotient_span_singleton_eq_one {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (hd : ringKrullDim R = 2) {f : R} (hf : f ∈ maximalIdeal R)
    (hfnd : f ∈ nonZeroDivisors R) : ringKrullDim (R ⧸ span {f}) = 1 := by
  -- a nonzero divisor lowers the dimension by one, `hf` placing it in the maximal ideal of the
  -- local ring `R`
  have hkey : ringKrullDim (R ⧸ span {f}) + 1 = ringKrullDim R :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
      (Module.Flat.isSMulRegular_of_nonZeroDivisors hfnd) hf
  rw [hd, ← Nat.cast_two, Nat.cast_succ, ENat.WithBot.add_one_cancel] at hkey
  exact hkey

/-- In a local ring, an element `x` with `dim R ⧸ (x) + 1 = dim R` lies in the maximal ideal:
otherwise `R ⧸ (x)` is the zero ring, of dimension `⊥`. -/
theorem mem_maximalIdeal_of_ringKrullDim_quotient_span_singleton_add_one_eq {R : Type*}
    [CommRing R] [IsLocalRing R] {x : R} (hx : ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R) :
    x ∈ maximalIdeal R := by
  by_contra hxm
  have : Subsingleton (R ⧸ span {x}) :=
    Ideal.Quotient.subsingleton_iff.mpr (span_singleton_eq_top.mpr (by simpa using hxm))
  rw [ringKrullDim_eq_bot_of_subsingleton, WithBot.bot_add] at hx
  exact not_subsingleton R (ringKrullDim_eq_bot_iff_subsingleton.mp hx.symm)

end TauCeti

namespace Module

open Ideal Pointwise _root_.IsLocalRing

/-- Over a Noetherian ring, dividing a finite module `M` by elements `r₁, …, rₙ` of the Jacobson
radical of its annihilator lowers the dimension of its support by at most `n`:
`dim M ≤ dim M ⧸ (r₁, …, rₙ) M + n`. -/
@[stacks 0B52 "the second inequality, iterated"]
theorem supportDim_le_supportDim_quotient_add_length_of_mem_jacobson {R M : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R) (hrs : ∀ r ∈ rs, r ∈ (annihilator R M).jacobson) :
    supportDim R M ≤ supportDim R (M ⧸ ofList rs • (⊤ : Submodule R M)) + rs.length := by
  induction rs generalizing M with
  | nil =>
    rw [ofList_nil, Submodule.bot_smul]
    simpa using (supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot ⊥ rfl)).ge
  | cons x rs ih =>
    rw [supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs),
      List.length_cons, Nat.cast_add_one, ← add_assoc]
    refine (supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson
      (hrs x List.mem_cons_self)).trans ?_
    gcongr
    -- The annihilator only grows on passing to the quotient `M ⧸ x M`.
    have hann : annihilator R M ≤ annihilator R (QuotSMulTop x M) :=
      LinearMap.annihilator_le_of_surjective _ (Submodule.mkQ_surjective _)
    exact ih fun r hr ↦ jacobson_mono hann (hrs r (List.mem_cons_of_mem x hr))

/-- Over a Noetherian local ring, dividing a finite module by `r₁, …, rₙ ∈ 𝔪` lowers the dimension
of its support by at most `n`: `dim M ≤ dim M ⧸ (r₁, …, rₙ) M + n`. -/
@[stacks 0B52 "the second inequality, iterated"]
theorem supportDim_le_supportDim_quotient_add_length {R M : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R) (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    supportDim R M ≤ supportDim R (M ⧸ ofList rs • (⊤ : Submodule R M)) + rs.length :=
  supportDim_le_supportDim_quotient_add_length_of_mem_jacobson rs
    fun r hr ↦ maximalIdeal_le_jacobson _ (hrs r hr)

end Module
end
end TAF_LiteralSource_0599

section TAF_LiteralSource_0600
/- Original module: TauCeti.Data.ENat.Monoid -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Strict inequalities from successors in `WithBot ℕ∞`

Krull dimensions take values in `WithBot ℕ∞`, and a dimension formula often has the shape
`c + 1 = k` for a natural number `k`. In `WithBot ℕ∞` the inequality `c < c + 1` fails for
`c = ⊤`, but a successor equal to a natural number rules that case out, so `c < k`.

## Main results

* `ENat.WithBot.lt_natCast_of_add_one_eq`: if `c + 1 = k` with `k : ℕ`, then `c < k`.
-/

public section

namespace ENat.WithBot

/-- In `WithBot ℕ∞`, an element whose successor is a natural number is smaller than it. -/
theorem lt_natCast_of_add_one_eq {c : WithBot ℕ∞} {k : ℕ} (h : c + 1 = k) : c < k :=
  (le_add_of_nonneg_right zero_le_one).trans_eq h |>.lt_of_ne (by rintro rfl; norm_cast at h; omega)

end ENat.WithBot
end
end TAF_LiteralSource_0600

section TAF_LiteralSource_0601
/- Original module: TauCeti.RingTheory.LocalRing.MaximalIdeal.Generator -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Local rings whose maximal ideal is generated by one or two elements

Let `R` be a local ring whose maximal ideal is generated by `ϖ`, for instance a valuation ring
with a uniformizer. Then divisibility by `ϖ` describes the maximal ideal and the units, and if
`R` is Noetherian, it has dimension at most one.

Consequently, if `R` is a two-dimensional Noetherian local ring whose maximal ideal is generated by
`x, y`, then neither element generates it alone, and by Nakayama's lemma each lies outside the
square of the maximal ideal.

## Main results

* `TauCeti.IsLocalRing.mem_maximalIdeal_iff_dvd`: the maximal ideal consists of the multiples of
  `ϖ`.
* `TauCeti.IsLocalRing.isUnit_iff_not_dvd`: the units are the elements not divisible by `ϖ`.
* `TauCeti.IsLocalRing.isUnit_add_of_dvd`: a unit plus a multiple of `ϖ` is a unit.
* `IsLocalRing.ringKrullDim_le_one_of_isPrincipal_maximalIdeal`: a Noetherian local ring with
  principal maximal ideal has dimension at most one.
* `TauCeti.IsLocalRing.notMem_sq_of_span_pair_eq_maximalIdeal`: in a two-dimensional Noetherian
  local ring, each element of a pair generating the maximal ideal lies outside its square.
-/

public section

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing

/-- In a local ring whose maximal ideal is generated by `ϖ`, membership in the maximal ideal is
divisibility by `ϖ`. -/
theorem mem_maximalIdeal_iff_dvd {R : Type*} [CommSemiring R] [IsLocalRing R] {ϖ : R}
    (hϖ : maximalIdeal R = Ideal.span {ϖ}) {z : R} : z ∈ maximalIdeal R ↔ ϖ ∣ z := by
  rw [hϖ, Ideal.mem_span_singleton]

/-- In a local ring whose maximal ideal is generated by `ϖ`, an element is a unit exactly when it
is not divisible by `ϖ`. -/
theorem isUnit_iff_not_dvd {R : Type*} [CommSemiring R] [IsLocalRing R] {ϖ : R}
    (hϖ : maximalIdeal R = Ideal.span {ϖ}) {z : R} : IsUnit z ↔ ¬ ϖ ∣ z := by
  rw [← mem_maximalIdeal_iff_dvd hϖ, mem_maximalIdeal, mem_nonunits_iff, not_not]

/-- In a local ring whose maximal ideal is generated by `ϖ`, a unit plus a multiple of `ϖ` is a
unit. -/
theorem isUnit_add_of_dvd {R : Type*} [CommRing R] [IsLocalRing R] {ϖ : R}
    (hϖ : maximalIdeal R = Ideal.span {ϖ}) {a b : R} (ha : IsUnit a) (hb : ϖ ∣ b) :
    IsUnit (a + b) := by
  rw [isUnit_iff_not_dvd hϖ] at ha ⊢
  exact fun hd ↦ ha (by simpa using dvd_sub hd hb)

end TauCeti.IsLocalRing

namespace IsLocalRing

/-- A Noetherian local ring whose maximal ideal is principal has dimension at most one. -/
theorem ringKrullDim_le_one_of_isPrincipal_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : (maximalIdeal R).IsPrincipal) : ringKrullDim R ≤ 1 := by
  obtain ⟨u, hu⟩ := h
  refine (ringKrullDim_le_spanFinrank_maximalIdeal R).trans ?_
  rw [hu]
  exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton u)).trans
    (Set.ncard_singleton u).le

end IsLocalRing

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing Ideal

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The first element of a pair generating the maximal ideal lies in the maximal ideal. -/
theorem mem_maximalIdeal_of_span_pair_eq_maximalIdeal {x y : R}
    (hxy : span {x, y} = maximalIdeal R) : x ∈ maximalIdeal R :=
  hxy ▸ subset_span (Set.mem_insert x {y})

variable [IsNoetherianRing R]

/-- In a two-dimensional Noetherian local ring, neither element of a pair generating the maximal
ideal generates it alone. -/
theorem notMem_span_singleton_of_span_pair_eq_maximalIdeal (hdim : ringKrullDim R = 2)
    {x y : R} (hxy : span {x, y} = maximalIdeal R) : y ∉ span {x} := fun hy ↦ by
  have hm : maximalIdeal R = span {x} := by
    rw [← hxy, span_insert, sup_eq_left]
    exact (span_singleton_le_iff_mem _).mpr hy
  have := ringKrullDim_le_one_of_isPrincipal_maximalIdeal ⟨x, hm⟩
  rw [hdim] at this
  exact absurd this (by decide)

/-- In a two-dimensional Noetherian local ring, each element of a pair generating the maximal
ideal is a regular parameter: it does not lie in the square of the maximal ideal. -/
theorem notMem_sq_of_span_pair_eq_maximalIdeal (hdim : ringKrullDim R = 2) {x y : R}
    (hxy : span {x, y} = maximalIdeal R) : x ∉ maximalIdeal R ^ 2 := fun hx ↦ by
  -- By Nakayama's lemma `y` alone would generate the maximal ideal.
  have hle : maximalIdeal R ≤ span {y} := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (maximalIdeal R).fg_of_isNoetherianRing
      (maximalIdeal_le_jacobson _) ?_
    rw [smul_eq_mul, ← pow_two]
    calc maximalIdeal R = span {x} ⊔ span {y} := by rw [← span_insert, hxy]
      _ ≤ maximalIdeal R ^ 2 ⊔ span {y} :=
        sup_le_sup_right ((span_singleton_le_iff_mem _).mpr hx) _
      _ = span {y} ⊔ maximalIdeal R ^ 2 := sup_comm _ _
  have hyx : span {y, x} = maximalIdeal R := by rw [Set.pair_comm, hxy]
  exact notMem_span_singleton_of_span_pair_eq_maximalIdeal hdim hyx
    (hle (mem_maximalIdeal_of_span_pair_eq_maximalIdeal hxy))

/-- In a two-dimensional Noetherian local ring, each element of a pair generating the maximal
ideal is nonzero. -/
theorem ne_zero_of_span_pair_eq_maximalIdeal (hdim : ringKrullDim R = 2) {x y : R}
    (hxy : span {x, y} = maximalIdeal R) : x ≠ 0 := fun h ↦
  notMem_sq_of_span_pair_eq_maximalIdeal hdim hxy (h ▸ zero_mem _)

end TauCeti.IsLocalRing
end
end TAF_LiteralSource_0601

section TAF_LiteralSource_0602
/- Original module: TauCeti.RingTheory.Ideal.Quotient.Colon -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Annihilators of residue classes

For an ideal `I` of a commutative ring `R` and `c : R`, the annihilator of the class of `c` in
`R ⧸ I`, written as the colon ideal `(⊥ : Submodule R (R ⧸ I)).colon {Ideal.Quotient.mk I c}`, is
the ideal quotient `(I : c) = {r | r * c ∈ I}`. This is the form in which associated primes of
`R ⧸ I` appear (`isAssociatedPrime_iff`).

## Main results

* `TauCeti.Ideal.Quotient.mem_colon_singleton_mk`: `r` annihilates the class of `c` in
  `R ⧸ I` exactly when `r * c ∈ I`.
-/

public section

open Ideal.Quotient

namespace TauCeti.Ideal.Quotient

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- An element `r` annihilates the class of `c` in `R ⧸ I` exactly when `r * c ∈ I`. -/
theorem mem_colon_singleton_mk {c r : R} :
    r ∈ (⊥ : Submodule R (R ⧸ I)).colon {mk I c} ↔ r * c ∈ I := by
  rw [Submodule.mem_colon_singleton, Algebra.smul_def, algebraMap_eq, ← map_mul, Submodule.mem_bot,
    eq_zero_iff_mem]

end TauCeti.Ideal.Quotient
end
end TAF_LiteralSource_0602

