module
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
@[expose] public section
/-! # A rigorous support-localization calculus lemma

A function whose second derivative is a positive multiple of a strictly convex
function has at most two global minima. This supplies the sign-shape argument
used in Lemma 4.1 without assuming that the zero set of the second derivative
has already been classified. Endpoints are included; differentiability is
required only in the interior.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Set

/-- Equal minimal endpoint values force a point of negative normalized curvature.
Strict convexity rules out the only alternative, a constant function on the interval. -/
theorem exists_negative_normalized_curvature
    {f h w : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b))
    (hf'' : DifferentiableOn ℝ (deriv f) (Ioo a b))
    (hw : ∀ x ∈ Ioo a b, 0 < w x)
    (heq : ∀ x ∈ Ioo a b, deriv (deriv f) x = w x * h x)
    (hh : StrictConvexOn ℝ (Ioo a b) h)
    (hmin : ∀ x ∈ Icc a b, f a ≤ f x) (hend : f b = f a) :
    ∃ x ∈ Ioo a b, h x < 0 := by
  by_contra hn
  have hnonneg : ∀ x ∈ Ioo a b, 0 ≤ h x := by
    intro x hx
    exact le_of_not_gt (fun hneg => hn ⟨x, hx, hneg⟩)
  have hconv : ConvexOn ℝ (Icc a b) f := by
    apply convexOn_of_deriv2_nonneg (convex_Icc a b) hf
    · simpa only [interior_Icc] using hf'
    · simpa only [interior_Icc] using hf''
    · intro x hx
      rw [interior_Icc] at hx
      change 0 ≤ deriv (deriv f) x
      rw [heq x hx]
      exact mul_nonneg (hw x hx).le (hnonneg x hx)
  have hconst : (Ioo a b).EqOn f (fun _ => f a) := by
    intro x hx
    apply le_antisymm
    · have hxseg : x ∈ segment ℝ a b := by
        rw [segment_eq_Icc hab.le]
        exact ⟨hx.1.le, hx.2.le⟩
      have hu := hconv.le_on_segment (left_mem_Icc.mpr hab.le)
        (right_mem_Icc.mpr hab.le) hxseg
      simpa only [hend, max_self] using hu
    · exact hmin x ⟨hx.1.le, hx.2.le⟩
  have hzero : ∀ x ∈ Ioo a b, h x = 0 := by
    intro x hx
    have hd := ((hconst.deriv isOpen_Ioo).deriv isOpen_Ioo) hx
    simp only [deriv_const', deriv_const] at hd
    rw [heq x hx] at hd
    exact (mul_eq_zero.mp hd).resolve_left (hw x hx).ne'
  let u : ℝ := (3 * a + b) / 4
  let v : ℝ := (a + 3 * b) / 4
  have hu : u ∈ Ioo a b := by dsimp [u]; constructor <;> linarith
  have hv : v ∈ Ioo a b := by dsimp [v]; constructor <;> linarith
  have huv : u ≠ v := by dsimp [u, v]; linarith
  have hm : (1 / 2 : ℝ) * u + (1 / 2 : ℝ) * v ∈ Ioo a b := by
    dsimp [u, v]
    constructor <;> linarith
  have hs := hh.2 hu hv huv (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at hs
  rw [hzero u hu, hzero v hv, hzero _ hm] at hs
  norm_num at hs

/-- There cannot be three ordered global minima. This version allows the outer
minima to be endpoints, which is essential for measures charging 0 or R. -/
theorem no_three_global_minima_of_strictConvex_normalized_curvature
    {f h w : ℝ → ℝ} {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hf : ContinuousOn f (Icc a c))
    (hf' : DifferentiableOn ℝ f (Ioo a c))
    (hf'' : DifferentiableOn ℝ (deriv f) (Ioo a c))
    (hw : ∀ x ∈ Ioo a c, 0 < w x)
    (heq : ∀ x ∈ Ioo a c, deriv (deriv f) x = w x * h x)
    (hh : StrictConvexOn ℝ (Ioo a c) h)
    (hmin : ∀ x ∈ Icc a c, f a ≤ f x)
    (hb : f b = f a) (hc : f c = f a) : False := by
  have hsub₁ : Ioo a b ⊆ Ioo a c := by
    intro x hx
    exact ⟨hx.1, hx.2.trans hbc⟩
  have hsub₂ : Ioo b c ⊆ Ioo a c := by
    intro x hx
    exact ⟨hab.trans hx.1, hx.2⟩
  obtain ⟨u, hu, hune⟩ := exists_negative_normalized_curvature hab
    (hf.mono (by intro x hx; exact ⟨hx.1, hx.2.trans hbc.le⟩))
    (hf'.mono hsub₁) (hf''.mono hsub₁)
    (fun x hx => hw x (hsub₁ hx)) (fun x hx => heq x (hsub₁ hx))
    (hh.subset hsub₁ (convex_Ioo a b))
    (fun x hx => hmin x ⟨hx.1, hx.2.trans hbc.le⟩) hb
  obtain ⟨v, hv, hvne⟩ := exists_negative_normalized_curvature hbc
    (hf.mono (by intro x hx; exact ⟨hab.le.trans hx.1, hx.2⟩))
    (hf'.mono hsub₂) (hf''.mono hsub₂)
    (fun x hx => hw x (hsub₂ hx)) (fun x hx => heq x (hsub₂ hx))
    (hh.subset hsub₂ (convex_Ioo b c))
    (fun x hx => by rw [hb]; exact hmin x ⟨hab.le.trans hx.1, hx.2⟩)
    (hc.trans hb.symm)
  have huv : u < v := hu.2.trans hv.1
  have huac : u ∈ Ioo a c := hsub₁ hu
  have hvac : v ∈ Ioo a c := hsub₂ hv
  have hsub : Icc u v ⊆ Icc a c := by
    intro x hx
    exact ⟨huac.1.le.trans hx.1, hx.2.trans hvac.2.le⟩
  have hnegative : ∀ x ∈ Ioo u v, h x < 0 := by
    intro x hx
    have hxseg : x ∈ segment ℝ u v := by
      rw [segment_eq_Icc huv.le]
      exact ⟨hx.1.le, hx.2.le⟩
    exact (hh.convexOn.le_on_segment huac hvac hxseg).trans_lt (max_lt hune hvne)
  have hconc : StrictConcaveOn ℝ (Icc u v) f := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc u v) (hf.mono hsub)
    intro x hx
    rw [interior_Icc] at hx
    have hxall : x ∈ Ioo a c := ⟨huac.1.trans hx.1, hx.2.trans hvac.2⟩
    change deriv (deriv f) x < 0
    rw [heq x hxall]
    exact mul_neg_of_pos_of_neg (hw x hxall) (hnegative x hx)
  have hbseg : b ∈ openSegment ℝ u v := by
    rw [openSegment_eq_Ioo huv]
    exact ⟨hu.2, hv.1⟩
  have hstrict := hconc.lt_on_openSegment (left_mem_Icc.mpr huv.le)
    (right_mem_Icc.mpr huv.le) huv.ne hbseg
  have hbu : f b ≤ f u := by rw [hb]; exact hmin u ⟨huac.1.le, huac.2.le⟩
  have hbv : f b ≤ f v := by rw [hb]; exact hmin v ⟨hvac.1.le, hvac.2.le⟩
  exact (not_lt_of_ge (le_min hbu hbv)) hstrict

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.no_three_global_minima_of_strictConvex_normalized_curvature
