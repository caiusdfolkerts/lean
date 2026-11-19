module
public import Papers.RationalityTenMultiaffine
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section
noncomputable section

/-!
# Rational approximation through algebraic charts

The finite chart certificates use rational maps with polynomial numerators
and denominators. This file supplies their topological semantics. A certificate
must still prove its identities, its nonzero denominators, and its inverse at
every allowed real point; none of those obligations is inferred from a
successful symbolic computation.
-/

namespace Papers.RationalityTen.AlgebraicChartDensity

open Set Filter Topology MvPolynomial
open MultiaffineDensity
open scoped BigOperators

def ZeroSet {ι : Type*} (E : Set (MvPolynomial ι ℚ)) : Set (ι → ℝ) :=
  {x | ∀ p ∈ E, evalRat p x = 0}

def NonzeroSet {ι : Type*} (N : Finset (MvPolynomial ι ℚ)) : Set (ι → ℝ) :=
  {x | ∀ p ∈ N, evalRat p x ≠ 0}

theorem isOpen_nonzeroSet {ι : Type*} (N : Finset (MvPolynomial ι ℚ)) :
    IsOpen (NonzeroSet N) := by
  classical
  have h : NonzeroSet N = ⋂ p ∈ N, {x | evalRat p x ≠ 0} := by
    ext x
    simp only [NonzeroSet, mem_setOf_eq, mem_iInter]
  rw [h]
  exact isOpen_biInter_finset fun p _ =>
    isOpen_ne.preimage (evalRat_continuous p)

theorem restrict_closure_to_open {X : Type*} [TopologicalSpace X]
    {x : X} {S U : Set X} (hx : x ∈ closure S)
    (hU : IsOpen U) (hxU : x ∈ U) : x ∈ closure (S ∩ U) := by
  rw [mem_closure_iff_frequently] at hx ⊢
  exact hx.and_eventually (hU.mem_nhds hxU)

/-- A dense rational parameter set and a continuous rational reconstruction
give density at the original point. The domain is an actual open set, so
nonzero denominators and strict inequalities are retained. -/
theorem density_from_local_chart {ι κ : Type*}
    (F : (ι → ℝ) → (κ → ℝ)) (x : ι → ℝ)
    (S : Set (ι → ℝ)) (T : Set (κ → ℝ)) (U : Set (ι → ℝ))
    (hx : x ∈ closure {q | RationalVector q ∧ q ∈ S})
    (hU : IsOpen U) (hxU : x ∈ U) (hF : ContinuousAt F x)
    (hrational : ∀ q ∈ U, RationalVector q → RationalVector (F q))
    (himage : ∀ q ∈ S ∩ U, F q ∈ T) :
    F x ∈ closure {q | RationalVector q ∧ q ∈ T} := by
  have hnear := restrict_closure_to_open hx hU hxU
  have hcl := mem_closure_image hF hnear
  apply closure_mono ?_ hcl
  rintro _ ⟨q, ⟨hq, hqU⟩, rfl⟩
  exact ⟨hrational q hqU hq.1, himage q ⟨hq.2, hqU⟩⟩

/-- Coordinates of a rational map are literal quotients of polynomials. -/
structure RationalChart (ι κ : Type*) where
  numerator : κ → MvPolynomial ι ℚ
  denominator : κ → MvPolynomial ι ℚ

def RationalChart.eval {ι κ : Type*} (F : RationalChart ι κ)
    (x : ι → ℝ) : κ → ℝ :=
  fun i => evalRat (F.numerator i) x / evalRat (F.denominator i) x

def RationalChart.domain {ι κ : Type*} (F : RationalChart ι κ) : Set (ι → ℝ) :=
  {x | ∀ i, evalRat (F.denominator i) x ≠ 0}

theorem RationalChart.continuousAt_eval {ι κ : Type*} (F : RationalChart ι κ)
    {x : ι → ℝ} (hx : x ∈ F.domain) : ContinuousAt F.eval x := by
  apply continuousAt_pi.mpr
  intro i
  exact (evalRat_continuous (F.numerator i)).continuousAt.div
    (evalRat_continuous (F.denominator i)).continuousAt (hx i)

theorem RationalChart.isOpen_domain {ι κ : Type*} [Finite κ]
    (F : RationalChart ι κ) : IsOpen F.domain := by
  have h : F.domain = ⋂ i, {x | evalRat (F.denominator i) x ≠ 0} := by
    ext x
    simp only [RationalChart.domain, mem_setOf_eq, mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_ne.preimage (evalRat_continuous (F.denominator i))

theorem RationalChart.rational_eval {ι κ : Type*} (F : RationalChart ι κ)
    {x : ι → ℝ} (hx : RationalVector x) : RationalVector (F.eval x) := by
  intro i
  obtain ⟨a, ha⟩ := evalRat_rational (F.numerator i) x hx
  obtain ⟨b, hb⟩ := evalRat_rational (F.denominator i) x hx
  exact ⟨a / b, by simp only [Rat.cast_div, ha, hb]; rfl⟩

/-- A certificate for a chart must show that its output satisfies every
equation. Rationality of the chart alone never establishes that claim. -/
theorem RationalChart.dense_image {ι κ : Type*} [Finite κ]
    (F : RationalChart ι κ) (x : ι → ℝ) (S : Set (ι → ℝ))
    (E : Set (MvPolynomial κ ℚ))
    (hx : x ∈ closure {q | RationalVector q ∧ q ∈ S})
    (hden : x ∈ F.domain)
    (hequations : ∀ q ∈ S ∩ F.domain, F.eval q ∈ ZeroSet E) :
    F.eval x ∈ closure {q | RationalVector q ∧ q ∈ ZeroSet E} :=
  density_from_local_chart F.eval x S (ZeroSet E) F.domain hx
    F.isOpen_domain hden (F.continuousAt_eval hden)
    (fun _ _ hq => F.rational_eval hq) hequations

/-- Nonzero minors are an open condition. This is the final step which
preserves all required nonzero minors, including their local signs. -/
theorem density_preserves_nonzero_polynomials {ι : Type*}
    (x : ι → ℝ) (E : Set (MvPolynomial ι ℚ))
    (N : Finset (MvPolynomial ι ℚ))
    (hx : x ∈ closure {q | RationalVector q ∧ q ∈ ZeroSet E})
    (hN : x ∈ NonzeroSet N) :
    x ∈ closure {q | RationalVector q ∧ q ∈ ZeroSet E ∧ q ∈ NonzeroSet N} := by
  have h := restrict_closure_to_open hx (isOpen_nonzeroSet N) hN
  apply closure_mono ?_ h
  rintro q ⟨⟨hr, he⟩, hn⟩
  exact ⟨hr, he, hn⟩

/-- A finite evaluation identity certifies that an entire specialized fiber
is nonzero. This lets a producer supply polynomial Bezout identities,
without trusting its factorization or irreducibility assertions. -/
theorem specialized_fiber_ne_zero_of_evaluation_sum {n k : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℚ) (z : ℝ)
    (samples : Fin k → Fin n → ℝ) (coefficients : Fin k → ℝ)
    (hnonzero : (∑ j, coefficients j *
      evalRat p (Option.elim' z (samples j))) ≠ 0) :
    specializeParameter p z ≠ 0 := by
  intro hzero
  have hz (j : Fin k) : evalRat p (Option.elim' z (samples j)) = 0 := by
    rw [← specializeParameter_eval p z (samples j), hzero, map_zero]
  apply hnonzero
  simp only [hz, mul_zero, Finset.sum_const_zero]

theorem specialized_fiber_ne_zero_of_bezout {n k : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℚ) (z : ℝ)
    (samples : Fin k → Fin n → ℝ) (coefficients : Fin k → ℝ)
    (hidentity : (∑ j, coefficients j *
      evalRat p (Option.elim' z (samples j))) = 1) :
    specializeParameter p z ≠ 0 := by
  apply specialized_fiber_ne_zero_of_evaluation_sum p z samples coefficients
  rw [hidentity]
  exact one_ne_zero

/-- Literal evaluation certificates discharge the fiber hypothesis in
Lemma 12 at singular points as well as regular ones. -/
theorem multiaffine_density_of_bezout {n k : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℚ)
    (hdegree : ∀ i : Fin n, p.degreeOf (some i) ≤ 1)
    (x : Option (Fin n) → ℝ) (hzero : evalRat p x = 0)
    (samples : Fin k → Fin n → ℝ) (coefficients : Fin k → ℝ)
    (hidentity : (∑ j, coefficients j *
      evalRat p (Option.elim' (x none) (samples j))) = 1) :
    x ∈ closure {q | RationalVector q ∧ evalRat p q = 0} :=
  multiaffine_rational_zeros_dense p hdegree x hzero
    (specialized_fiber_ne_zero_of_bezout p (x none) samples coefficients hidentity)

/-- The same criterion with a directly proved affine identity in each
coordinate. This avoids a separate degree computation for literal charts. -/
theorem multiaffine_density_of_affine_bezout {n k : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℚ)
    (haffine : ∀ i : Fin n, AffineIn (evalRat p) (some i))
    (x : Option (Fin n) → ℝ) (hzero : evalRat p x = 0)
    (samples : Fin k → Fin n → ℝ) (coefficients : Fin k → ℝ)
    (hidentity : (∑ j, coefficients j *
      evalRat p (Option.elim' (x none) (samples j))) = 1) :
    x ∈ closure {q | RationalVector q ∧ evalRat p q = 0} := by
  apply rational_zeros_dense_of_multiaffine_fiber (evalRat p)
    (evalRat_continuous p) (evalRat_rational p) haffine x hzero
    (specializeParameter p (x none))
    (specialized_fiber_ne_zero_of_bezout p (x none) samples coefficients hidentity)
  exact specializeParameter_eval p (x none)

/-- An equation which is a product is treated as the union of its actual
zero sets. In particular no factor is cancelled without a nonzero proof. -/
theorem rational_zero_density_mul {ι : Type*}
    (p q : MvPolynomial ι ℚ) (x : ι → ℝ)
    (hp : evalRat p x = 0 →
      x ∈ closure {y | RationalVector y ∧ evalRat p y = 0})
    (hq : evalRat q x = 0 →
      x ∈ closure {y | RationalVector y ∧ evalRat q y = 0})
    (hzero : evalRat (p * q) x = 0) :
    x ∈ closure {y | RationalVector y ∧ evalRat (p * q) y = 0} := by
  have heval (y : ι → ℝ) : evalRat (p * q) y = evalRat p y * evalRat q y := by
    simp only [evalRat, eval₂_mul]
  rw [heval] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · apply closure_mono (s := {y | RationalVector y ∧ evalRat p y = 0}) ?_ (hp h)
    rintro y ⟨hr, hy⟩
    exact ⟨hr, by rw [heval, hy, zero_mul]⟩
  · apply closure_mono (s := {y | RationalVector y ∧ evalRat q y = 0}) ?_ (hq h)
    rintro y ⟨hr, hy⟩
    exact ⟨hr, by rw [heval, hy, mul_zero]⟩

end Papers.RationalityTen.AlgebraicChartDensity
