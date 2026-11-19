module

public import PaperVerification.GradedInjectiveQuotient
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Recovering the dimension of a finite graded module from its Hilbert series

A finite module has finitely many nonzero internal graded pieces. Its Hilbert
series is therefore the image of a polynomial whose value at one is the actual
module dimension. Cancelling the common factors `1-X` before evaluating at one
then proves the usual degree-product formula, without a formal evaluation of an
infinite power series or an analytic limiting argument.
-/

@[expose] public section
noncomputable section
open scoped BigOperators PowerSeries

namespace PaperVerification.FiniteGradedDimension

open GradedInjectiveQuotient

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  (G : TauCeti.InternalGrading K M ℕ) [FiniteDimensional K M]

/-- The finite support consists precisely of the nonzero graded submodules. -/
def support : Finset ℕ := G.finite_piece_ne_bot.toFinset

@[simp] theorem mem_support (d : ℕ) : d ∈ support G ↔ G.piece d ≠ ⊥ :=
  Set.Finite.mem_toFinset _

/-- The Hilbert polynomial here is the finite Hilbert series, not an eventual
Hilbert function polynomial. -/
def finiteHilbertPolynomial : Polynomial ℤ :=
  ∑ d ∈ support G, Polynomial.monomial d (Module.finrank K (G.piece d) : ℤ)

@[simp] theorem coeff_finiteHilbertPolynomial (d : ℕ) :
    (finiteHilbertPolynomial G).coeff d = (Module.finrank K (G.piece d) : ℤ) := by
  classical
  rw [finiteHilbertPolynomial, Polynomial.finsetSum_coeff, Finset.sum_eq_single d]
  · exact Polynomial.coeff_monomial_same _ _
  · intro b hb hbd
    exact Polynomial.coeff_monomial_of_ne _ hbd.symm
  · intro hd
    have hz : G.piece d=⊥ := by simpa only [mem_support, not_not] using hd
    rw [Polynomial.coeff_monomial_same, hz, finrank_bot, Nat.cast_zero]

theorem coe_finiteHilbertPolynomial :
    (finiteHilbertPolynomial G : ℤ⟦X⟧) = hilbertSeries G := by
  apply PowerSeries.ext
  intro d
  simp only [Polynomial.coeff_coe, coeff_finiteHilbertPolynomial,
    hilbertSeries, PowerSeries.coeff_mk]

/-- Actual dimension is the sum of the dimensions of all nonzero pieces. -/
theorem finrank_eq_sum_support :
    Module.finrank K M = ∑ d ∈ support G, Module.finrank K (G.piece d) := by
  classical
  letI : Fintype {d : ℕ // G.piece d ≠ ⊥} := G.finite_piece_ne_bot.fintype
  have hI : DirectSum.IsInternal (fun d : {d : ℕ // G.piece d ≠ ⊥} => G.piece d) :=
    DirectSum.isInternal_ne_bot_iff.mpr G.isInternal
  let E := LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (fun d : {d : ℕ // G.piece d ≠ ⊥} => G.piece d)) hI
  rw [← E.finrank_eq, Module.finrank_directSum]
  exact (Finset.sum_subtype (support G) (mem_support G)
    (fun d => Module.finrank K (G.piece d))).symm

@[simp] theorem eval_one_finiteHilbertPolynomial :
    (finiteHilbertPolynomial G).eval 1 = (Module.finrank K M : ℤ) := by
  classical
  simp only [finiteHilbertPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, one_pow, mul_one]
  exact_mod_cast (finrank_eq_sum_support G).symm

/-- A polynomial geometric sum, valid also at exponent zero. -/
def geometricPolynomial (n : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range n, Polynomial.X^j

@[simp] theorem eval_one_geometricPolynomial (n : ℕ) :
    (geometricPolynomial n).eval 1 = (n : ℤ) := by
  simp [geometricPolynomial]

theorem geometricPolynomial_mul_one_sub_X (n : ℕ) :
    geometricPolynomial n * (1-Polynomial.X) = 1-Polynomial.X^n :=
  geom_sum_mul_neg _ n

/-- Cancel the equal-order vanishing factors before evaluating at one. -/
theorem eval_one_mul_product_degrees {ι : Type*} [Fintype ι]
    (P : Polynomial ℤ) (a b : ι → ℕ)
    (h : P * (∏ i, (1-Polynomial.X^(a i))) =
      ∏ i, (1-Polynomial.X^(b i))) :
    P.eval 1 * (∏ i, (a i : ℤ)) = ∏ i, (b i : ℤ) := by
  classical
  have hnonzero : ((1-Polynomial.X : Polynomial ℤ)^Fintype.card ι) ≠ 0 := by
    apply pow_ne_zero
    intro hz
    have hc := congrArg (fun p : Polynomial ℤ => p.coeff 0) hz
    simp at hc
  have hg (v : ι → ℕ) :
      (∏ i, geometricPolynomial (v i)) * (1-Polynomial.X)^Fintype.card ι =
        ∏ i, (1-Polynomial.X^(v i)) := by
    calc
      _ = ∏ i, (geometricPolynomial (v i)*(1-Polynomial.X)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      _ = _ := by simp only [geometricPolynomial_mul_one_sub_X]
  have hc : P * (∏ i, geometricPolynomial (a i)) =
      ∏ i, geometricPolynomial (b i) := by
    apply mul_right_cancel₀ hnonzero
    rw [mul_assoc, hg, hg]
    exact h
  have he := congrArg (Polynomial.eval 1) hc
  simpa only [Polynomial.eval_mul, Polynomial.eval_prod,
    eval_one_geometricPolynomial] using he

/-- Finite-dimensional degree-product formula, deduced from the literal
power-series identity for this graded module. -/
theorem finrank_mul_product_degrees {ι : Type*} [Fintype ι]
    (a b : ι → ℕ)
    (h : hilbertSeries G * (∏ i, (1-PowerSeries.X^(a i))) =
      ∏ i, (1-PowerSeries.X^(b i))) :
    (Module.finrank K M : ℤ) * (∏ i, (a i : ℤ)) = ∏ i, (b i : ℤ) := by
  have hp : finiteHilbertPolynomial G * (∏ i, (1-Polynomial.X^(a i))) =
      ∏ i, (1-Polynomial.X^(b i)) := by
    apply Polynomial.coe_injective ℤ
    have hprod (f : ι → Polynomial ℤ) :
        ((∏ i, f i : Polynomial ℤ) : ℤ⟦X⟧) = ∏ i, (f i : ℤ⟦X⟧) :=
      map_prod Polynomial.coeToPowerSeries.ringHom f Finset.univ
    simpa only [Polynomial.coe_mul, hprod, Polynomial.coe_sub,
      Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X,
      coe_finiteHilbertPolynomial] using h
  simpa only [eval_one_finiteHilbertPolynomial] using
    eval_one_mul_product_degrees (finiteHilbertPolynomial G) a b hp

/-- Consecutive relation degrees and variable weights `1,...,s` give the
binomial coefficient in Section 4. -/
theorem finrank_eq_choose_of_hilbert_identity (s w : ℕ)
    (h : hilbertSeries G *
        (∏ i : Fin s, (1-PowerSeries.X^(i.val+1))) =
      ∏ i : Fin s, (1-PowerSeries.X^(w+i.val))) :
    Module.finrank K M = (w+s-1).choose s := by
  have hd := finrank_mul_product_degrees G (fun i : Fin s => i.val+1)
    (fun i : Fin s => w+i.val) h
  have hdn : Module.finrank K M * s.factorial = w.ascFactorial s := by
    rw [Nat.factorial_eq_prod_range_add_one, Nat.ascFactorial_eq_prod_range]
    have hnat : Module.finrank K M * (∏ i : Fin s, (i.val+1)) =
        ∏ i : Fin s, (w+i.val) := by exact_mod_cast hd
    rw [← Finset.prod_range (fun i : ℕ => i+1),
      ← Finset.prod_range (fun i : ℕ => w+i)] at hnat
    exact hnat
  rw [Nat.ascFactorial_eq_factorial_mul_choose'] at hdn
  exact Nat.eq_of_mul_eq_mul_right s.factorial_pos (by simpa only [mul_comm] using hdn)

end PaperVerification.FiniteGradedDimension
