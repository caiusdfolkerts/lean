module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic

/-!
# Leading terms of polynomial additive-group orbits

The projective fixed-point argument for a one-parameter unipotent group has an
elementary polynomial core. The highest nonzero coefficient of a polynomial
orbit is fixed by every group element. Every homogeneous equation vanishing
on the orbit also vanishes on this coefficient. These statements concern
actual matrices, polynomial evaluation and homogeneous equations; no
fixed-point or smoothness theorem is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.PolynomialOrbitFixedPoint

open scoped BigOperators Matrix
open Polynomial

variable {K ι : Type*} [Field K]

/-- The coefficient at the sum of upper degree bounds is multiplicative. -/
theorem coeff_prod_sum_bounds {α : Type*} (s : Finset α)
    (p : α → Polynomial K) (d : α → ℕ)
    (hd : ∀ i ∈ s, (p i).natDegree  ≤  d i) :
    (∏ i ∈ s, p i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (p i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      Polynomial.coeff_mul_add_eq_of_natDegree_le (hd i (Finset.mem_insert_self _ _))]
    · rw [ih (fun j hj => hd j (Finset.mem_insert_of_mem hj))]
    · exact (Polynomial.natDegree_prod_le s p).trans
        (Finset.sum_le_sum fun j hj => hd j (Finset.mem_insert_of_mem hj))

/-- A homogeneous polynomial evaluated on polynomial coordinates has its
top possible coefficient obtained by evaluating on the top coefficients. -/
theorem homogeneous_substitution_top_coefficient
    (p : ι → Polynomial K) (d : ℕ) (hd : ∀ i, (p i).natDegree  ≤  d)
    (f : MvPolynomial ι K) (e : ℕ) (hf : f.IsHomogeneous e) :
    (MvPolynomial.aeval p f).coeff (d*e) =
      MvPolynomial.aeval (fun i => (p i).coeff d) f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hdegree : a.degree = e := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (MvPolynomial.mem_support_iff.mp ha)
  simp only [MvPolynomial.aeval_monomial,
    Polynomial.algebraMap_eq, Algebra.algebraMap_self, RingHom.id_apply,
    Polynomial.coeff_C_mul]
  congr 1
  have hsum : (∑ i ∈ a.support, a i*d) = d*e := by
    rw [← Finset.sum_mul, ← Finsupp.degree_apply, hdegree, Nat.mul_comm]
  rw [Finsupp.prod, ← hsum, coeff_prod_sum_bounds]
  · apply Finset.prod_congr rfl
    intro i hi
    exact Polynomial.coeff_pow_of_natDegree_le (hd i)
  · intro i hi
    exact Polynomial.natDegree_pow_le_of_le _ (hd i)

/-- Substituting into a multivariate polynomial commutes with evaluation of
the orbit parameter. -/
theorem eval_substitution (p : ι → Polynomial K) (f : MvPolynomial ι K) (u : K) :
    (MvPolynomial.aeval p f).eval u =
      MvPolynomial.aeval (fun i => (p i).eval u) f := by
  have h : (Polynomial.aeval u).comp (MvPolynomial.aeval p) =
      MvPolynomial.aeval (fun i => (p i).eval u) := by
    ext i
    simp
  exact DFunLike.congr_fun h f

/-- Homogeneous equations persist at the leading point of a polynomial
orbit. Infinitude is used only to turn vanishing at all parameters into a
polynomial identity. -/
theorem homogeneous_vanishes_on_top_coefficient [Infinite K]
    (p : ι → Polynomial K) (d : ℕ) (hd : ∀ i, (p i).natDegree  ≤  d)
    (f : MvPolynomial ι K) (e : ℕ) (hf : f.IsHomogeneous e)
    (hvanish : ∀ u : K, MvPolynomial.aeval (fun i => (p i).eval u) f = 0) :
    MvPolynomial.aeval (fun i => (p i).coeff d) f = 0 := by
  have hz : MvPolynomial.aeval p f = 0 :=
    Polynomial.zero_of_eval_zero _ (fun u => by rw [eval_substitution]; exact hvanish u)
  rw [← homogeneous_substitution_top_coefficient p d hd f e hf, hz]
  simp

/-- Translation preserves the coefficient at any common upper degree
bound, including the case when that coefficient is zero. -/
theorem coeff_taylor_of_degree_le (p : Polynomial K) (u : K) (d : ℕ)
    (hd : p.natDegree  ≤  d) : (Polynomial.taylor u p).coeff d = p.coeff d := by
  obtain h | h := lt_or_eq_of_le hd
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (by simpa only [Polynomial.natDegree_taylor] using h),
      Polynomial.coeff_eq_zero_of_natDegree_lt h]
  · subst d
    exact Polynomial.coeff_taylor_natDegree u p

/-- Every matrix fixing the polynomial orbit by translation fixes its
leading coefficient vector. -/
theorem top_coefficient_fixed [Fintype ι] [Infinite K]
    (A : K → Matrix ι ι K) (p : ι → Polynomial K) (d : ℕ)
    (hd : ∀ i, (p i).natDegree  ≤  d)
    (horbit : ∀ u t : K, A u *ᵥ (fun i => (p i).eval t) =
      fun i => (p i).eval (u+t)) (u : K) :
    A u *ᵥ (fun i => (p i).coeff d) = fun i => (p i).coeff d := by
  classical
  funext i
  have hpoly : (∑ j, Polynomial.C (A u i j) * p j) = Polynomial.taylor u (p i) := by
    apply Polynomial.funext
    intro t
    simpa only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.taylor_apply, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      add_comm t u, Matrix.mulVec, dotProduct] using congrFun (horbit u t) i
  have hcoeff := congrArg (fun q : Polynomial K => q.coeff d) hpoly
  simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    coeff_taylor_of_degree_le (p i) u d (hd i), Matrix.mulVec, dotProduct] using hcoeff

/-- A nonzero polynomial vector has a common degree bound with a nonzero
coefficient vector at that bound. -/
theorem exists_nonzero_top_coefficient [Fintype ι]
    (p : ι → Polynomial K) (hp : ∃ i, p i ≠ 0) :
    ∃ d : ℕ, (∀ i, (p i).natDegree  ≤  d) ∧ (fun i => (p i).coeff d) ≠ 0 := by
  classical
  let s : Finset ι := Finset.univ.filter (fun i => p i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i,hi⟩ := hp
    exact ⟨i,by simp [s,hi]⟩
  obtain ⟨i,hi,hmax⟩ := Finset.exists_mem_eq_sup s hs (fun i => (p i).natDegree)
  refine ⟨s.sup (fun i => (p i).natDegree), ?_, ?_⟩
  · intro j
    by_cases hj : p j = 0
    · simp [hj]
    · exact Finset.le_sup (f := fun i => (p i).natDegree) (by simp [s,hj])
  · intro hzero
    have hpi : p i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hcoeff := congrFun hzero i
    rw [hmax, Polynomial.coeff_natDegree] at hcoeff
    exact (Polynomial.leadingCoeff_ne_zero.mpr hpi) hcoeff

/-- The algebraic fixed-point conclusion needed for a homogeneous closed
subset of projective space containing a nonempty polynomial orbit. -/
theorem exists_nonzero_fixed_common_zero [Fintype ι] [Infinite K]
    (A : K → Matrix ι ι K) (p : ι → Polynomial K) (hp : ∃ i, p i ≠ 0)
    (horbit : ∀ u t : K, A u *ᵥ (fun i => (p i).eval t) =
      fun i => (p i).eval (u+t))
    (equations : Set (MvPolynomial ι K))
    (hhom : ∀ f ∈ equations, ∃ e, f.IsHomogeneous e)
    (hvanish : ∀ u : K, ∀ f ∈ equations,
      MvPolynomial.aeval (fun i => (p i).eval u) f = 0) :
    ∃ v : ι → K, v ≠ 0 ∧ (∀ u : K, A u *ᵥ v = v) ∧
      ∀ f ∈ equations, MvPolynomial.aeval v f = 0 := by
  obtain ⟨d,hd,hne⟩ := exists_nonzero_top_coefficient p hp
  refine ⟨fun i => (p i).coeff d, hne, ?_, ?_⟩
  · exact top_coefficient_fixed A p d hd horbit
  · intro f hf
    obtain ⟨e,he⟩ := hhom f hf
    exact homogeneous_vanishes_on_top_coefficient p d hd f e he
      (fun u => hvanish u f hf)

end PaperVerification.PolynomialOrbitFixedPoint
