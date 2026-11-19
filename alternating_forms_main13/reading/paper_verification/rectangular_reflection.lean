module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Tactic

/-!
# Rectangular reversal and the coefficient pairing

The reversal of a polynomial supported in an exponent box `0 ≤ a ≤ d`
sends `X^a` to `X^(d-a)`.  Unlike inversion in a rational function field,
this is an actual linear map on multivariate polynomials.  The top
coefficient of the product with its reversal is the sum of squares of
its coefficients.  This supplies an elementary positivity argument for
the Chern pairing in Section 4 of the paper.

No cohomology or Chow group is defined in this file.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace PaperVerification.RectangularReflection

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- Every monomial of `p` lies in the exponent box bounded by `d`. -/
def BoundedBy (d : σ →₀ ℕ) (p : MvPolynomial σ R) : Prop :=
  ∀ a ∈ p.support, a ≤ d

/-- Reflect exponents in the upper corner of a box.  Outside the box
the truncated subtraction still defines a linear map; its reflection
properties are used only with the explicitly stated support bound. -/
def reflect (d : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  AddMonoidAlgebra.mapDomainLinearMap R R (fun a => d - a)

@[simp] theorem reflect_monomial (d a : σ →₀ ℕ) (r : R) :
    reflect d (monomial a r) = monomial (d-a) r := by
  exact AddMonoidAlgebra.mapDomainLinearMap_single _ _ _

theorem reflect_apply (d : σ →₀ ℕ) (p : MvPolynomial σ R) :
    reflect d p = ∑ a ∈ p.support, monomial (d-a) (p.coeff a) := by
  classical
  conv_lhs => rw [← support_sum_monomial_coeff p]
  simp only [map_sum, reflect_monomial]

theorem boundedBy_reflect (d : σ →₀ ℕ) (p : MvPolynomial σ R) :
    BoundedBy d (reflect d p) := by
  classical
  intro a ha
  rw [reflect_apply] at ha
  obtain ⟨b,hb,hab⟩ := Finset.mem_biUnion.mp (support_sum ha)
  have heq : a = d-b := by
    simpa only [Finset.mem_singleton] using support_monomial_subset hab
  rw [heq]
  exact tsub_le_self

theorem boundedBy_mul {d e : σ →₀ ℕ} {p q : MvPolynomial σ R}
    (hp : BoundedBy d p) (hq : BoundedBy e q) :
    BoundedBy (d+e) (p*q) := by
  classical
  intro a ha
  obtain ⟨b,hb,c,hc,rfl⟩ := Finset.mem_add.mp (support_mul p q ha)
  exact add_le_add (hp b hb) (hq c hc)

theorem reflect_reflect {d : σ →₀ ℕ} {p : MvPolynomial σ R}
    (hp : BoundedBy d p) : reflect d (reflect d p) = p := by
  classical
  rw [reflect_apply d p]
  simp only [map_sum, reflect_monomial]
  calc
    _ = ∑ a ∈ p.support, monomial a (p.coeff a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [tsub_tsub_cancel_of_le (hp a ha)]
    _ = p := support_sum_monomial_coeff p

theorem reflect_mul {d e : σ →₀ ℕ} {p q : MvPolynomial σ R}
    (hp : BoundedBy d p) (hq : BoundedBy e q) :
    reflect (d+e) (p*q) = reflect d p * reflect e q := by
  classical
  calc
    _ = ∑ a ∈ p.support, ∑ b ∈ q.support,
        monomial ((d+e)-(a+b)) (p.coeff a*q.coeff b) := by
      conv_lhs => rw [← support_sum_monomial_coeff p, ← support_sum_monomial_coeff q]
      simp only [Finset.sum_mul, Finset.mul_sum, map_sum, monomial_mul_monomial,
        reflect_monomial]
      exact Finset.sum_comm
    _ = ∑ a ∈ p.support, ∑ b ∈ q.support,
        monomial ((d-a)+(e-b)) (p.coeff a*q.coeff b) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have h : (d+e)-(a+b) = (d-a)+(e-b) := by
        ext i
        have h₁ := hp a ha i
        have h₂ := hq b hb i
        simp only [Finsupp.add_apply, Finsupp.tsub_apply]
        omega
      rw [h]
    _ = reflect d p * reflect e q := by
      rw [reflect_apply, reflect_apply]
      simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial]
      exact Finset.sum_comm

/-- Top coefficient against the reversal is the coefficient dot product. -/
theorem coeff_mul_reflect {d : σ →₀ ℕ} (p q : MvPolynomial σ R)
    (hq : BoundedBy d q) :
    (p * reflect d q).coeff d = ∑ a ∈ q.support, p.coeff a*q.coeff a := by
  classical
  rw [reflect_apply, Finset.mul_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [coeff_mul_monomial', ite_eq_left (tsub_le_self),
    tsub_tsub_cancel_of_le (hq a ha)]

theorem coeff_self_mul_reflect {d : σ →₀ ℕ} (p : MvPolynomial σ R)
    (hp : BoundedBy d p) :
    (p * reflect d p).coeff d = ∑ a ∈ p.support, (p.coeff a)^2 := by
  rw [coeff_mul_reflect p p hp]
  simp only [pow_two]

section Uniform

variable [Fintype σ]

/-- The exponent assigning the same bound to every variable. -/
def uniformExponent (c : ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun _ => c

@[simp] theorem uniformExponent_apply (c : ℕ) (i : σ) :
    uniformExponent (σ := σ) c i = c := rfl

theorem uniformExponent_add (c d : ℕ) :
    uniformExponent (σ := σ) (c+d) = uniformExponent c + uniformExponent d := by
  ext i
  rfl

theorem mapDomain_uniformExponent (e : Equiv.Perm σ) (c : ℕ) :
    (uniformExponent (σ := σ) c).mapDomain e = uniformExponent c := by
  ext i
  obtain ⟨j,rfl⟩ := e.surjective i
  rw [Finsupp.mapDomain_apply_of_injective e.injective]
  rfl

theorem rename_reflect (e : Equiv.Perm σ) (c : ℕ) (p : MvPolynomial σ R) :
    rename e (reflect (uniformExponent c) p) =
      reflect (uniformExponent c) (rename e p) := by
  classical
  conv_lhs => rw [← support_sum_monomial_coeff p]
  conv_rhs => rw [← support_sum_monomial_coeff p]
  simp only [map_sum, reflect_monomial, rename_monomial]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finsupp.mapDomain_tsub e.injective, mapDomain_uniformExponent]

theorem reflect_isSymmetric {p : MvPolynomial σ R} (hp : p.IsSymmetric) (c : ℕ) :
    (reflect (uniformExponent c) p).IsSymmetric := by
  intro e
  rw [rename_reflect, hp e]

end Uniform

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Positivity is a proof over an ordered field, not a numerical test. -/
theorem coeff_self_mul_reflect_pos {d : σ →₀ ℕ} {p : MvPolynomial σ K}
    (hp : BoundedBy d p) (hne : p ≠ 0) :
    0 < (p * reflect d p).coeff d := by
  classical
  rw [coeff_self_mul_reflect p hp]
  have hsupport : p.support.Nonempty := by
    by_contra hn
    have hz : p.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    exact hne (by ext a; exact notMem_support_iff.mp (by simp [hz]))
  obtain ⟨a,ha⟩ := hsupport
  exact Finset.sum_pos' (fun b _ => sq_nonneg (p.coeff b))
    ⟨a,ha,sq_pos_of_ne_zero (mem_support_iff.mp ha)⟩

end Ordered

end PaperVerification.RectangularReflection
