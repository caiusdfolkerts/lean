module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The one-crossing comparison in the sharp second-moment inequality

This file proves the scalar comparison used in the level-set proof of
Berwald's inequality. The geometric superlevel-set concavity and layer-cake
identifications must be proved separately before applying these lemmas to
fibers of convex bodies.
-/

open Set MeasureTheory Filter

namespace VolumePolynomials.BerwaldComparison

/-- If a function can change sign only from positive to negative, a crossing
point makes its product with the centered coordinate nonpositive everywhere. -/
theorem exists_crossing_point {a : ℝ} (ha : 0 ≤ a) (g : ℝ → ℝ)
    (hcross : ∀ x ∈ Icc 0 a, ∀ y ∈ Icc 0 a, x < y → g x < 0 → g y ≤ 0) :
    ∃ τ ∈ Icc 0 a, ∀ t ∈ Icc 0 a, (t - τ) * g t ≤ 0 := by
  first
  | classical
    let S : Set ℝ := {t | t ∈ Icc 0 a ∧ 0 < g t}
    by_cases hS : S.Nonempty
    · have hbounded : BddAbove S := ⟨a, fun t ht => ht.1.2⟩
      have hτa : sSup S ≤ a := csSup_le hS (fun t ht => ht.1.2)
      obtain ⟨t₀, ht₀⟩ := hS
      have hτ0 : 0 ≤ sSup S := ht₀.1.1.trans (le_csSup hbounded ht₀)
      refine ⟨sSup S, ⟨hτ0, hτa⟩, ?_⟩
      intro t ht
      rcases lt_trichotomy t (sSup S) with hlt | heq | hgt
      · have hgt0 : 0 ≤ g t := by
          first
          | by_contra h
            obtain ⟨u, hu, htu⟩ := exists_lt_of_lt_csSup ⟨t₀, ht₀⟩ hlt
            exact (not_lt_of_ge (hcross t ht u hu.1 htu (lt_of_not_ge h))) hu.2
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hlt.le) hgt0
      · simp only [heq, sub_self, zero_mul, le_refl]
      · have hgt0 : g t ≤ 0 := by
          first
          | by_contra h
            have hm : t ∈ S := ⟨ht, lt_of_not_ge h⟩
            exact (not_le_of_gt hgt) (le_csSup hbounded hm)
        exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hgt.le) hgt0
    · refine ⟨0, ⟨le_rfl, ha⟩, ?_⟩
      intro t ht
      have hg : g t ≤ 0 := by
        first
        | by_contra h
          exact hS ⟨t, ht, lt_of_not_ge h⟩
      simpa only [sub_zero] using mul_nonpos_of_nonneg_of_nonpos ht.1 hg

theorem first_moment_nonpos {a : ℝ} (ha : 0 ≤ a) (g : ℝ → ℝ)
    (hg : IntegrableOn g (Icc 0 a))
    (hxg : IntegrableOn (fun t => t * g t) (Icc 0 a))
    (hzero : (∫ t in Icc 0 a, g t) = 0)
    (hcross : ∀ x ∈ Icc 0 a, ∀ y ∈ Icc 0 a, x < y → g x < 0 → g y ≤ 0) :
    (∫ t in Icc 0 a, t * g t) ≤ 0 := by
  first
  | obtain ⟨τ, _, hτ⟩ := exists_crossing_point ha g hcross
    have hnonpos : (∫ t in Icc 0 a, (t - τ) * g t) ≤ 0 :=
      integral_nonpos_of_ae ((ae_restrict_mem measurableSet_Icc).mono fun t ht => hτ t ht)
    have heq : (∫ t in Icc 0 a, (t - τ) * g t) = ∫ t in Icc 0 a, t * g t := by
      first
      | calc
          (∫ t in Icc 0 a, (t - τ) * g t) =
              ∫ t in Icc 0 a, t * g t - τ * g t := by
            apply integral_congr_ae
            exact Eventually.of_forall (fun t => by ring)
          _ = (∫ t in Icc 0 a, t * g t) - τ * ∫ t in Icc 0 a, g t := by
            rw [integral_sub hxg (hg.const_mul τ), integral_const_mul]
          _ = ∫ t in Icc 0 a, t * g t := by rw [hzero, mul_zero, sub_zero]
    rwa [heq] at hnonpos

/-- Equal masses and one crossing imply the required comparison of first
moments of the survival functions. -/
theorem first_moment_le {a : ℝ} (ha : 0 ≤ a) (v w : ℝ → ℝ)
    (hv : IntegrableOn v (Icc 0 a)) (hw : IntegrableOn w (Icc 0 a))
    (hxv : IntegrableOn (fun t => t * v t) (Icc 0 a))
    (hxw : IntegrableOn (fun t => t * w t) (Icc 0 a))
    (hmass : (∫ t in Icc 0 a, v t) = ∫ t in Icc 0 a, w t)
    (hcross : ∀ x ∈ Icc 0 a, ∀ y ∈ Icc 0 a, x < y → v x < w x → v y ≤ w y) :
    (∫ t in Icc 0 a, t * v t) ≤ ∫ t in Icc 0 a, t * w t := by
  first
  | have hg : IntegrableOn (fun t => v t - w t) (Icc 0 a) := hv.sub hw
    have hxg : IntegrableOn (fun t => t * (v t - w t)) (Icc 0 a) := by
      first
      | convert hxv.sub hxw using 1
        ext t
        simp only [Pi.sub_apply]
        ring
    have hzero : (∫ t in Icc 0 a, v t - w t) = 0 := by
      first
      | rw [integral_sub hv hw, hmass, sub_self]
    have hn := first_moment_nonpos ha (fun t => v t - w t) hg hxg hzero
      (fun x hx y hy hxy h => sub_nonpos.mpr (hcross x hx y hy hxy (sub_neg.mp h)))
    have heq : (∫ t in Icc 0 a, t * (v t - w t)) =
        (∫ t in Icc 0 a, t * v t) - ∫ t in Icc 0 a, t * w t := by
      first
      | simp_rw [mul_sub]
        exact integral_sub hxv hxw
    rw [heq] at hn
    exact sub_nonpos.mp hn

/-- The reference survival function has exactly the mass required in the
Berwald comparison. -/
theorem reference_integral (k : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ t in Icc 0 a, (1 - t / a) ^ k) = a / (k + 1) := by
  first
  | rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.le]
    have h := intervalIntegral.integral_comp_sub_div (fun u : ℝ => u ^ k) ha.ne' 1
      (a := (0 : ℝ)) (b := a)
    rw [div_self ha.ne', sub_self, zero_div, sub_zero,
      integral_pow] at h
    simpa only [one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero,
      smul_eq_mul, mul_one_div] using h

/-- The first moment of the reference survival function gives the sharp
constant `2*(k+1)/(k+2)` after layer-cake integration. -/
theorem reference_first_moment (k : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ t in Icc 0 a, t * (1 - t / a) ^ k) =
      a ^ 2 / ((k + 1) * (k + 2)) := by
  first
  | have hidentity (t : ℝ) : t * (1 - t / a) ^ k =
        a * ((1 - t / a) ^ k - (1 - t / a) ^ (k + 1)) := by
      first
      | rw [pow_succ]
        field_simp
        ring
    have hk : IntegrableOn (fun t : ℝ => (1 - t / a) ^ k) (Icc 0 a) :=
      ((continuous_const.sub (continuous_id.div_const a)).pow k).integrableOn_Icc
    have hk1 : IntegrableOn (fun t : ℝ => (1 - t / a) ^ (k + 1)) (Icc 0 a) :=
      ((continuous_const.sub (continuous_id.div_const a)).pow (k + 1)).integrableOn_Icc
    simp_rw [hidentity]
    rw [integral_const_mul, integral_sub hk hk1,
      reference_integral k ha, reference_integral (k + 1) ha]
    push_cast
    field_simp
    ring

/-- A concave graph starting at height one can cross an affine graph
starting at the same point only once, from above to below. -/
theorem concave_below_line_persists {M a : ℝ} {u : ℝ → ℝ}
    (hu : ConcaveOn ℝ (Ico 0 M) u) (hM : 0 < M) (hu0 : u 0 = 1)
    {x y : ℝ} (hx : x ∈ Ico 0 M) (hy : y ∈ Ico 0 M)
    (hxy : x < y) (hux : u x < 1 - x / a) : u y < 1 - y / a := by
  first
  | have hxpos : 0 < x := by
      first
      | by_contra h
        have hx0 : x = 0 := le_antisymm (le_of_not_gt h) hx.1
        simpa only [hx0, hu0, zero_div, sub_zero, lt_self_iff_false] using hux
    have hypos : 0 < y := hxpos.trans hxy
    have hweight : 0 ≤ 1 - x / y :=
      sub_nonneg.mpr ((div_le_one hypos).mpr hxy.le)
    have hpoint : (1 - x / y) * 0 + (x / y) * y = x := by
      first
      | rw [mul_zero, zero_add, div_mul_cancel₀ x hypos.ne']
    have hconc : 1 - x / y + x / y * u y ≤ u x := by
      first
      | simpa only [smul_eq_mul, hu0, mul_one, hpoint] using
          hu.2 (show (0 : ℝ) ∈ Ico 0 M from ⟨le_rfl, hM⟩) hy
            hweight (div_nonneg hx.1 hypos.le) (by ring : (1 - x / y) + x / y = 1)
    have hscaled := mul_le_mul_of_nonneg_left hconc hypos.le
    have hidentity : y * (1 - x / y + x / y * u y) = y - x + x * u y := by
      first
      | field_simp [hypos.ne'] <;> ring
    rw [hidentity] at hscaled
    have hsmall := mul_lt_mul_of_pos_left hux hypos
    have hprod : x * u y < x * (1 - y / a) := by
      first
      | calc
          x * u y ≤ y * u x - y + x := by linarith
          _ < y * (1 - x / a) - y + x := by linarith
          _ = x * (1 - y / a) := by ring
    by_contra h
    exact (not_le_of_gt hprod)
      (mul_le_mul_of_nonneg_left (le_of_not_gt h) hxpos.le)

/-- The dimension-root concavity of a survival function implies the exact
one-crossing condition for the polynomial reference survival function. -/
theorem root_concavity_one_crossing {k : ℕ} (hk : 0 < k)
    {M a : ℝ} (hM : 0 < M) (ha : 0 < a)
    (u v : ℝ → ℝ) (hu : ConcaveOn ℝ (Ico 0 M) u) (hu0 : u 0 = 1)
    (hunonneg : ∀ t ∈ Ico 0 M, 0 ≤ u t)
    (hv : ∀ t ∈ Ico 0 M, v t = (u t) ^ k)
    (hvzero : ∀ t, M ≤ t → v t = 0) :
    ∀ x ∈ Icc 0 a, ∀ y ∈ Icc 0 a, x < y →
      v x < (1 - x / a) ^ k → v y ≤ (1 - y / a) ^ k := by
  first
  | intro x hx y hy hxy hsmall
    have hbase (t : ℝ) (ht : t ∈ Icc 0 a) : 0 ≤ 1 - t / a :=
      sub_nonneg.mpr ((div_le_one ha).mpr ht.2)
    by_cases hyM : M ≤ y
    · rw [hvzero y hyM]
      exact pow_nonneg (hbase y hy) k
    · have hy' : y ∈ Ico 0 M := ⟨hy.1, lt_of_not_ge hyM⟩
      have hx' : x ∈ Ico 0 M := ⟨hx.1, hxy.trans hy'.2⟩
      rw [hv x hx'] at hsmall
      have hxroot : u x < 1 - x / a :=
        (pow_lt_pow_iff_left₀ (hunonneg x hx') (hbase x hx) hk.ne').mp hsmall
      have hyroot := concave_below_line_persists hu hM hu0 hx' hy' hxy hxroot
      rw [hv y hy']
      exact pow_le_pow_left₀ (hunonneg y hy') hyroot.le k

/-- Concavity and nonnegativity force the chord joining `(0,1)` to the
limiting endpoint `(M,0)` to lie below the graph. No endpoint continuity
at `M` is required. -/
theorem concave_reference_lower_bound {M : ℝ} (hM : 0 < M) {u : ℝ → ℝ}
    (hu : ConcaveOn ℝ (Ico 0 M) u) (hu0 : u 0 = 1)
    (hn : ∀ t ∈ Ico 0 M, 0 ≤ u t) {t : ℝ} (ht : t ∈ Ico 0 M) :
    1 - t / M ≤ u t := by
  first
  | have hclosed : IsClosed {b : ℝ | b - t ≤ b * u t} :=
      isClosed_le (continuous_id.sub continuous_const)
        (continuous_id.mul continuous_const)
    have hsubset : Ioo t M ⊆ {b : ℝ | b - t ≤ b * u t} := by
      first
      | intro b hb
        have hb0 : 0 < b := ht.1.trans_lt hb.1
        have hwt : 0 ≤ 1 - t / b :=
          sub_nonneg.mpr ((div_le_one hb0).mpr hb.1.le)
        have hpoint : (1 - t / b) * 0 + (t / b) * b = t := by
          rw [mul_zero, zero_add, div_mul_cancel₀ t hb0.ne']
        have hc := hu.2 (show (0 : ℝ) ∈ Ico 0 M from ⟨le_rfl, hM⟩)
          (show b ∈ Ico 0 M from ⟨hb0.le, hb.2⟩) hwt
          (div_nonneg ht.1 hb0.le) (by ring : 1 - t / b + t / b = 1)
        simp only [smul_eq_mul, hu0, mul_one, hpoint] at hc
        have hterm : 0 ≤ t / b * u b :=
          mul_nonneg (div_nonneg ht.1 hb0.le) (hn b ⟨hb0.le, hb.2⟩)
        have hlow : 1 - t / b ≤ u t := by linarith
        have hh := mul_le_mul_of_nonneg_left hlow hb0.le
        have hid : b * (1 - t / b) = b - t := by
          field_simp [hb0.ne']
        change b - t ≤ b * u t
        simpa only [hid] using hh
    have hMc : M ∈ closure (Ioo t M) := by
      first
      | rw [closure_Ioo ht.2.ne]
        exact ⟨ht.2.le, le_rfl⟩
    have hlim : M - t ≤ M * u t := closure_minimal hsubset hclosed hMc
    have hid : 1 - t / M = (M - t) / M := by field_simp <;> ring
    rw [hid]
    exact (div_le_iff₀ hM).mpr (by simpa only [mul_comm] using hlim)

/-- The complete scalar comparison, with no assumed upper bound on the
support in terms of its first moment. That bound is a conclusion of
concavity, and fixes the comparison interval. -/
theorem sharp_moment_bound {k : ℕ} (hk : 0 < k) {M : ℝ} (hM : 0 < M)
    (u v : ℝ → ℝ) (hu : ConcaveOn ℝ (Ico 0 M) u) (hu0 : u 0 = 1)
    (hun : ∀ t ∈ Ico 0 M, 0 ≤ u t)
    (hvp : ∀ t ∈ Ico 0 M, v t = u t ^ k)
    (hvz : ∀ t, M ≤ t → v t = 0)
    (hvint : ∀ a : ℝ, 0 ≤ a → IntegrableOn v (Icc 0 a))
    (hxvint : ∀ a : ℝ, 0 ≤ a → IntegrableOn (fun t => t * v t) (Icc 0 a)) :
    2 * (∫ t in Icc 0 M, t * v t) ≤
      (2 * (k + 1 : ℝ) / (k + 2 : ℝ)) * (∫ t in Icc 0 M, v t) ^ 2 := by
  first
  | let m : ℝ := ∫ t in Icc 0 M, v t
    have hk1 : 0 < (k + 1 : ℝ) := by positivity
    have hmasslow : M / (k + 1 : ℝ) ≤ m := by
      first
      | rw [← reference_integral k hM]
        apply integral_mono_ae
          (((continuous_const.sub (continuous_id.div_const M)).pow k).integrableOn_Icc)
          (hvint M hM.le)
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        change (1 - t / M) ^ k ≤ v t
        by_cases hlt : t < M
        · rw [hvp t ⟨ht.1, hlt⟩]
          exact pow_le_pow_left₀
            (sub_nonneg.mpr ((div_le_one hM).mpr ht.2))
            (concave_reference_lower_bound hM hu hu0 hun ⟨ht.1, hlt⟩) k
        · have heq : t = M := le_antisymm ht.2 (le_of_not_gt hlt)
          subst t
          simp only [hvz M le_rfl, div_self hM.ne', sub_self, zero_pow hk.ne', le_refl]
    have hm : 0 < m := (div_pos hM hk1).trans_le hmasslow
    let a : ℝ := (k + 1 : ℝ) * m
    have ha : 0 < a := mul_pos hk1 hm
    have hMa : M ≤ a := by
      first
      | exact (div_le_iff₀ hk1).mp hmasslow |>.trans_eq (mul_comm _ _)
    have hvmass : (∫ t in Icc 0 a, v t) = m := by
      first
      | apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_Icc
          (Icc_subset_Icc_right hMa)
        exact Eventually.of_forall fun t ht => by
          have hMt : M < t := by
            have ht0 := ht.1.1
            by_contra h
            exact ht.2 ⟨ht0, le_of_not_gt h⟩
          exact hvz t hMt.le
    have hxveq : (∫ t in Icc 0 a, t * v t) = ∫ t in Icc 0 M, t * v t := by
      first
      | apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_Icc
          (Icc_subset_Icc_right hMa)
        exact Eventually.of_forall fun t ht => by
          have hMt : M < t := by
            have ht0 := ht.1.1
            by_contra h
            exact ht.2 ⟨ht0, le_of_not_gt h⟩
          rw [hvz t hMt.le, mul_zero]
    have hrefint : IntegrableOn (fun t : ℝ => (1 - t / a) ^ k) (Icc 0 a) :=
      ((continuous_const.sub (continuous_id.div_const a)).pow k).integrableOn_Icc
    have hrefxint : IntegrableOn (fun t : ℝ => t * (1 - t / a) ^ k) (Icc 0 a) :=
      (continuous_id.mul ((continuous_const.sub (continuous_id.div_const a)).pow k)).integrableOn_Icc
    have hmass : (∫ t in Icc 0 a, v t) = ∫ t in Icc 0 a, (1 - t / a) ^ k := by
      first
      | rw [hvmass, reference_integral k ha]
        dsimp only [a]
        field_simp
    have hcmp := first_moment_le ha.le v (fun t => (1 - t / a) ^ k)
      (hvint a ha.le) hrefint (hxvint a ha.le) hrefxint hmass
      (root_concavity_one_crossing hk hM ha u v hu hu0 hun hvp hvz)
    rw [hxveq, reference_first_moment k ha] at hcmp
    have htwice := mul_le_mul_of_nonneg_left hcmp (by norm_num : (0 : ℝ) ≤ 2)
    have hconstant : 2 * (a ^ 2 / ((k + 1 : ℝ) * (k + 2 : ℝ))) =
        (2 * (k + 1 : ℝ) / (k + 2 : ℝ)) * m ^ 2 := by
      first
      | dsimp only [a]
        field_simp <;> ring
    simpa only [hconstant, m] using htwice

end VolumePolynomials.BerwaldComparison
