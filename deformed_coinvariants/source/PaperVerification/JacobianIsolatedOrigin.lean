module

public import PaperVerification.HomogeneousNullstellensatz
public import PaperVerification.JacobianDivergence
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Topology.Algebra.Monoid

/-!
# Isolated weighted homogeneous critical points give regular gradients

The hypothesis is a genuine neighbourhood condition in complex affine space.
Weighted scaling turns any nonzero critical point into arbitrarily small nonzero
critical points. Thus isolation at the origin gives the global zero-set statement
needed by the Nullstellensatz, and hence global regularity of the gradient.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Filter Topology

namespace PaperVerification.JacobianDivergence

variable {K ι : Type*} [CommRing K]

/-- Weighted scaling, proved by monomial induction. The proof follows
TauCeti's `IsWeightedHomogeneous.aeval_pow_mul` at the recorded source pin;
it is included here so this elementary bridge is checked with the project. -/
theorem weighted_eval_scaling (F : MvPolynomial ι K) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) (c : K) (x : ι → K) :
    MvPolynomial.aeval (fun i => c ^ w i * x i) F =
      c ^ h * MvPolynomial.aeval x F := by
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ ihp ihq => rw [map_add, map_add, ihp, ihq, mul_add]
  | monomial d r hr =>
    rw [aeval_monomial, aeval_monomial, ← hr]
    simp only [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, mul_pow,
      Finset.prod_mul_distrib, ← pow_mul', Finset.prod_pow_eq_pow_sum, smul_eq_mul]
    ring

/-- Differentiation above the polynomial's weight gives zero, including in
positive characteristic. -/
theorem pderiv_zero_of_weight_lt (F : MvPolynomial ι K) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) (i : ι) (hi : h < w i) : pderiv i F = 0 := by
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => exact map_zero _
  | add p q hp hq ihp ihq => rw [map_add, ihp, ihq, add_zero]
  | monomial a c ha =>
    have hai : a i = 0 := by
      by_contra hne
      have hw := Finsupp.le_weight_of_ne_zero' w hne
      rw [ha] at hw
      exact hi.not_ge hw
    simp [pderiv_monomial, hai]

/-- The usual truncated natural degree is valid even when the derivative is zero. -/
theorem gradient_weightedHomogeneous (F : MvPolynomial ι K) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) (i : ι) :
    (pderiv i F).IsWeightedHomogeneous w (h - w i) := by
  by_cases hi : w i ≤ h
  · exact hF.pderiv (Nat.sub_add_cancel hi)
  · rw [pderiv_zero_of_weight_lt F w h hF i (lt_of_not_ge hi)]
    exact isWeightedHomogeneous_zero K w _

variable {n : ℕ}
local notation "P" => MvPolynomial (Fin n) ℂ

/-- The ordinary analytic meaning of an isolated critical point at the origin. -/
def IsolatedCriticalPointAtOrigin (F : P) : Prop :=
  (∀ i, aeval (0 : Fin n → ℂ) (pderiv i F) = 0) ∧
  ∃ U : Set (Fin n → ℂ), U ∈ 𝓝 0 ∧
    ∀ x ∈ U, (∀ i, aeval x (pderiv i F) = 0) → x = 0

/-- Positive weighted scaling excludes any other global critical point. -/
theorem critical_zero_of_isolated (F : P) (w : Fin n → ℕ) (h : ℕ)
    (hw : ∀ i, 0 < w i) (hF : F.IsWeightedHomogeneous w h)
    (hiso : IsolatedCriticalPointAtOrigin F)
    (x : Fin n → ℂ) (hx : ∀ i, aeval x (pderiv i F) = 0) : x = 0 := by
  obtain ⟨_, U, hU, hcrit⟩ := hiso
  let scale : ℂ → Fin n → ℂ := fun c i => c ^ w i * x i
  have hcont : Continuous scale :=
    continuous_pi (fun i => (continuous_pow (w i)).mul_const (x i))
  have hscale0 : scale 0 = 0 := by
    ext i
    simp only [scale, zero_pow (Nat.ne_of_gt (hw i)), zero_mul, Pi.zero_apply]
  have ht : Tendsto scale (𝓝 0) (𝓝 0) := by
    simpa only [hscale0] using (hcont.continuousAt (x := 0)).tendsto
  have hnear : ∀ᶠ c : ℂ in 𝓝[≠] 0, scale c ∈ U :=
    (ht.eventually_mem hU).filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ c : ℂ in 𝓝[≠] 0, c ≠ 0 := self_mem_nhdsWithin
  obtain ⟨c, hcU, hc⟩ := (hnear.and hne).exists
  have hscaled : scale c = 0 := by
    apply hcrit _ hcU
    intro i
    rw [weighted_eval_scaling (pderiv i F) w (h - w i)
      (gradient_weightedHomogeneous F w h hF i) c x, hx i, mul_zero]
  ext i
  have he := congrFun hscaled i
  change c ^ w i * x i = 0 at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hc)

/-- The regularity assumption used by the algebraic Brieskorn proof follows
from the paper's analytic isolated-critical-point hypothesis. -/
theorem gradient_regular_of_isolated (F : P) (w : Fin n → ℕ) (h : ℕ)
    (hw : ∀ i, 0 < w i) (hF : F.IsWeightedHomogeneous w h)
    (hiso : IsolatedCriticalPointAtOrigin F) :
    RingTheory.Sequence.IsWeaklyRegular P (List.ofFn (gradient F)) := by
  apply HomogeneousLocalization.homogeneous_family_regular_of_common_zero w
    (fun i => Nat.ne_of_gt (hw i)) (gradient F)
  · exact fun i => ⟨h - w i, gradient_weightedHomogeneous F w h hF i⟩
  · intro i
    simpa only [gradient, aeval_zero, Algebra.algebraMap_self, RingHom.id_apply] using hiso.1 i
  · exact critical_zero_of_isolated F w h hw hF hiso

end PaperVerification.JacobianDivergence
