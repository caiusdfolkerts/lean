module

public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Push

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory

namespace RankThreeProjection.QuantileStability

/-- At every point of a quasiconcave density, at least one entire tail is
bounded above by the density at that point. No choice of a maximizer or
regularity at the endpoints is needed. -/
theorem quasiconcave_one_sided_bound (f : ℝ → ℝ) {l s r : ℝ}
    (hf : QuasiconcaveOn ℝ (Icc l r) f) (hs : s ∈ Icc l r) :
    (∀ x ∈ Icc l s, f x ≤ f s) ∨ (∀ x ∈ Icc s r, f x ≤ f s) := by
  by_cases hleft : ∀ x ∈ Icc l s, f x ≤ f s
  · exact Or.inl hleft
  · right
    push_neg at hleft
    obtain ⟨x, hx, hfx⟩ := hleft
    intro y hy
    by_contra hfy
    have hy' : f s < f y := lt_of_not_ge hfy
    have hmid := (hf.convex_gt (f s)).ordConnected.out
      ⟨⟨hx.1, hx.2.trans hs.2⟩, hfx⟩
      ⟨⟨hs.1.trans hy.1, hy.2⟩, hy'⟩ ⟨hx.2, hy.1⟩
    exact (lt_irrefl (f s)) hmid.2

/-- The smaller cumulative mass divided by the local density is at most
the width of the support interval. This elementary bound controls the tails
of convex-body height quantiles uniformly. -/
theorem quasiconcave_tail_integral_bound (f : ℝ → ℝ) {l s r : ℝ}
    (hf : QuasiconcaveOn ℝ (Icc l r) f) (hs : s ∈ Icc l r)
    (hfs : 0 ≤ f s)
    (hleft : IntervalIntegrable f volume l s)
    (hright : IntervalIntegrable f volume s r) :
    min (∫ x in l..s, f x) (∫ x in s..r, f x) ≤ (r - l) * f s := by
  rcases quasiconcave_one_sided_bound f hf hs with h | h
  · have hI := intervalIntegral.integral_mono_on hs.1 hleft
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f s) volume l s) h
    rw [intervalIntegral.integral_const, smul_eq_mul] at hI
    exact (min_le_left _ _).trans (hI.trans
      (mul_le_mul_of_nonneg_right (sub_le_sub_right hs.2 l) hfs))
  · have hI := intervalIntegral.integral_mono_on hs.2 hright
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f s) volume s r) h
    rw [intervalIntegral.integral_const, smul_eq_mul] at hI
    exact (min_le_right _ _).trans (hI.trans
      (mul_le_mul_of_nonneg_right (sub_le_sub_left hs.1 r) hfs))

/-- In probability coordinates, the preceding bound says
`min(τ,1−τ) * z'(τ) ≤ width`, where `z' = totalMass / density`. -/
theorem quasiconcave_inverse_density_bound (f : ℝ → ℝ) {l s r V τ : ℝ}
    (hf : QuasiconcaveOn ℝ (Icc l r) f) (hs : s ∈ Icc l r)
    (hfs : 0 < f s) (hV : 0 ≤ V)
    (hleft : IntervalIntegrable f volume l s)
    (hright : IntervalIntegrable f volume s r)
    (hF : (∫ x in l..s, f x) = τ * V)
    (hG : (∫ x in s..r, f x) = (1 - τ) * V) :
    min τ (1 - τ) * (V / f s) ≤ r - l := by
  have h := quasiconcave_tail_integral_bound f hf hs hfs.le hleft hright
  rw [hF, hG, ← min_mul_of_nonneg _ _ hV] at h
  rw [← mul_div_assoc, div_le_iff₀ hfs]
  exact h

/-- A weighted derivative bound gives a uniform modulus for multiplicative
changes of small probability levels. Unlike a global derivative bound, this
remains useful arbitrarily close to the endpoint `τ = 0`. -/
theorem quantile_multiplicative_increment
    (q v : ℝ → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt q (v t) t)
    (hv : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ v t)
    (hweighted : ∀ t ∈ Ioo (0 : ℝ) 1, min t (1 - t) * v t ≤ W)
    {t Λ r : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (hΛ1 : 1 ≤ Λ) (hΛ2 : Λ ≤ 3 / 2) (hr : r ∈ Icc (t / Λ) (Λ * t)) :
    |q r - q t| ≤ 2 * W * (Λ - 1) := by
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ1
  have hsub : Icc (t / Λ) (Λ * t) ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨(div_pos ht hΛ).trans_le hx.1, by nlinarith [hx.2]⟩
  have htmem : t ∈ Icc (t / Λ) (Λ * t) := by
    constructor
    · exact (div_le_iff₀ hΛ).mpr (by nlinarith)
    · nlinarith
  have hbound (x : ℝ) (hx : x ∈ Icc (t / Λ) (Λ * t)) :
      ‖v x‖ ≤ 2 * W / t := by
    have hxI := hsub hx
    have hx0 := hv x hxI
    have hxmin : t / 2 ≤ min x (1 - x) := by
      have hxΛ : t ≤ x * Λ := (div_le_iff₀ hΛ).mp hx.1
      apply le_min
      · nlinarith [hxI.1]
      · nlinarith [hx.2]
    have hw := (mul_le_mul_of_nonneg_right hxmin hx0).trans (hweighted x hxI)
    rw [Real.norm_eq_abs, abs_of_nonneg hx0, le_div_iff₀ ht]
    nlinarith
  have hLip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hderiv x (hsub hx)).hasDerivWithinAt) hbound (convex_Icc _ _) htmem hr
  have hlow : t * (2 - Λ) ≤ t / Λ := by
    apply (le_div_iff₀ hΛ).mpr
    nlinarith [mul_nonneg ht.le (sq_nonneg (Λ - 1))]
  have hdist : |r - t| ≤ t * (Λ - 1) := by
    rw [abs_le]
    constructor
    · nlinarith [hlow.trans hr.1]
    · nlinarith [hr.2]
  have hC : 0 ≤ 2 * W / t := div_nonneg (mul_nonneg zero_le_two hW) ht.le
  have h := hLip.trans (mul_le_mul_of_nonneg_left hdist hC)
  have he : (2 * W / t) * (t * (Λ - 1)) = 2 * W * (Λ - 1) := by
    calc
      _ = (2 * W * (Λ - 1)) * (t / t) := by ring
      _ = _ := by rw [div_self ht.ne', mul_one]
  simpa only [Real.norm_eq_abs, he] using h

end RankThreeProjection.QuantileStability
