module

public import Projection.Basic
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set Metric
open scoped Pointwise NNReal

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Unit functionals; in Euclidean space these are the usual unit normal vectors
under the Riesz isometry. Using the dual avoids a choice of coordinates. -/
abbrev NormalSphere (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {f : E →L[ℝ] ℝ // ‖f‖ = 1}

namespace Support
open BodySupport

@[simp] theorem point_zero (f : E →L[ℝ] ℝ) :
    support (pointBody (0 : E)) f = 0 := by
  apply le_antisymm
  · apply support_le
    intro x hx
    have hx' : x = 0 := hx
    simp [hx']
  · simpa using le_support (pointBody (0 : E)) f (show (0 : E) ∈ pointBody 0 from rfl)

theorem add (A B : ConvexBody E) (f : E →L[ℝ] ℝ) :
    support (A + B) f = support A f + support B f := by
  apply le_antisymm
  · apply support_le
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [map_add]
    exact add_le_add (le_support A f hx) (le_support B f hy)
  · obtain ⟨x, hx, hfx⟩ := exists_support A f
    obtain ⟨y, hy, hfy⟩ := exists_support B f
    simpa only [map_add, hfx, hfy] using
      le_support (A + B) f (Set.add_mem_add hx hy)

theorem smul_body (A : ConvexBody E) (f : E →L[ℝ] ℝ)
    {r : ℝ} (hr : 0 ≤ r) : support (r • A) f = r * support A f := by
  apply le_antisymm
  · apply support_le
    rintro _ ⟨x, hx, rfl⟩
    simpa only [map_smul, smul_eq_mul] using
      mul_le_mul_of_nonneg_left (le_support A f hx) hr
  · obtain ⟨x, hx, hfx⟩ := exists_support A f
    simpa only [map_smul, smul_eq_mul, hfx] using
      le_support (r • A) f (smul_mem_smul_set hx)

theorem smul_functional (A : ConvexBody E) (f : E →L[ℝ] ℝ)
    {r : ℝ} (hr : 0 ≤ r) : support A (r • f) = r * support A f := by
  apply le_antisymm
  · apply support_le
    intro x hx
    exact mul_le_mul_of_nonneg_left (le_support A f hx) hr
  · obtain ⟨x, hx, hfx⟩ := exists_support A f
    simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul, hfx] using
      le_support A (r • f) hx

theorem sub_le (A : ConvexBody E) (f g : E →L[ℝ] ℝ) :
    support A f - support A g ≤ support A (f - g) := by
  obtain ⟨x, hx, hfx⟩ := exists_support A f
  have hg := le_support A g hx
  have hfg := le_support A (f - g) hx
  simp only [ContinuousLinearMap.sub_apply] at hfg
  rw [← hfx]
  linarith

theorem dist_bound (A : ConvexBody E) (f g : E →L[ℝ] ℝ) :
    dist (support A f) (support A g) ≤ dist A (pointBody 0) * dist f g := by
  have hfg := (sub_le A f g).trans
    (support_le_add_norm_mul_dist A (pointBody 0) (f - g))
  have hgf := (sub_le A g f).trans
    (support_le_add_norm_mul_dist A (pointBody 0) (g - f))
  simp only [point_zero, zero_add] at hfg hgf
  rw [norm_sub_rev g f] at hgf
  rw [Real.dist_eq, dist_eq_norm, abs_le]
  constructor <;> nlinarith

theorem continuous_in_functional (A : ConvexBody E) :
    Continuous (fun f : E →L[ℝ] ℝ => support A f) := by
  apply LipschitzWith.continuous (K := ⟨dist A (pointBody 0), dist_nonneg⟩)
  exact LipschitzWith.of_dist_le_mul (dist_bound A)

end Support

/-- The support function of an actual body, restricted to unit functionals. -/
def supportContinuous (A : ConvexBody E) : C(NormalSphere E, ℝ) where
  toFun u := BodySupport.support A u.val
  continuous_toFun := (Support.continuous_in_functional A).comp continuous_subtype_val

@[simp] theorem supportContinuous_apply (A : ConvexBody E) (u : NormalSphere E) :
    supportContinuous A u = BodySupport.support A u.val := rfl

@[simp] theorem supportContinuous_zero :
    supportContinuous (0 : ConvexBody E) = 0 := by
  ext u
  exact Support.point_zero u.val

@[simp] theorem supportContinuous_add (A B : ConvexBody E) :
    supportContinuous (A + B) = supportContinuous A + supportContinuous B := by
  ext u
  exact Support.add A B u.val

@[simp] theorem supportContinuous_smul (r : ℝ≥0) (A : ConvexBody E) :
    supportContinuous (r • A) = r • supportContinuous A := by
  ext u
  exact Support.smul_body A u.val r.property

/-- Support functions preserve addition and nonnegative homogeneity. -/
def supportLinear : ConvexBody E →ₗ[ℝ≥0] C(NormalSphere E, ℝ) where
  toFun := supportContinuous
  map_add' := supportContinuous_add
  map_smul' := supportContinuous_smul

theorem supportContinuous_mono {A B : ConvexBody E} (hAB : A ≤ B) :
    supportContinuous A ≤ supportContinuous B := by
  intro u
  exact BodySupport.support_le A u.val
    (fun x hx => BodySupport.le_support B u.val (hAB hx))

/-- Unit normal values retain the entire body, including degenerate bodies. -/
theorem le_of_supportContinuous_le {A B : ConvexBody E}
    (hAB : supportContinuous A ≤ supportContinuous B) : A ≤ B := by
  intro x hx
  apply BodySupport.mem_iff_le_support B |>.mpr
  intro f
  by_cases hf : f = 0
  · subst f
    have hzero : BodySupport.support B (0 : E →L[ℝ] ℝ) = 0 := by
      apply le_antisymm
      · exact BodySupport.support_le B 0 (fun _ _ => le_rfl)
      · obtain ⟨y, hy⟩ := B.nonempty
        exact BodySupport.le_support B 0 hy
    simp [hzero]
  · have hnorm : 0 < ‖f‖ := norm_pos_iff.mpr hf
    let u : NormalSphere E := ⟨‖f‖⁻¹ • f, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
      exact inv_mul_cancel₀ hnorm.ne'⟩
    have hu : ‖f‖ • u.val = f := by
      simp only [u, smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
    have hs := (BodySupport.le_support A u.val hx).trans (hAB u)
    have hs' := mul_le_mul_of_nonneg_left hs hnorm.le
    change ‖f‖ * u.val x ≤ ‖f‖ * BodySupport.support B u.val at hs'
    calc
      f x = ‖f‖ * u.val x := by
        simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using
          (congrArg (fun g : E →L[ℝ] ℝ => g x) hu).symm
      _ ≤ ‖f‖ * BodySupport.support B u.val := hs'
      _ = BodySupport.support B f := by
        rw [← Support.smul_functional B u.val hnorm.le, hu]

theorem supportContinuous_injective :
    Function.Injective (supportContinuous (E := E)) := by
  intro A B h
  exact le_antisymm (le_of_supportContinuous_le h.le)
    (le_of_supportContinuous_le h.symm.le)

section FiniteDimension
variable [FiniteDimensional ℝ E]

instance normalSphereCompact : CompactSpace (NormalSphere E) := by
  have heq : {f : E →L[ℝ] ℝ | ‖f‖ = 1} = Metric.sphere 0 1 := by
    ext f
    simp [Metric.mem_sphere, dist_zero_right]
  exact isCompact_iff_compactSpace.mp (heq ▸ isCompact_sphere (0 : E →L[ℝ] ℝ) 1)

/-- The actual closed unit ball, as a compact convex body. -/
def unitBall : ConvexBody E where
  carrier := closedBall 0 1
  convex' := convex_closedBall (0 : E) 1
  isCompact' := isCompact_closedBall 0 1
  nonempty' := ⟨0, by simp⟩

set_option backward.isDefEq.respectTransparency false in
theorem supportContinuous_unitBall :
    supportContinuous (unitBall (E := E)) = 1 := by
  ext u
  simp only [supportContinuous_apply, ContinuousMap.one_apply]
  apply le_antisymm
  · apply BodySupport.support_le
    intro x hx
    change x ∈ closedBall (0 : E) 1 at hx
    have hx' : ‖x‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    calc
      u.val x ≤ ‖u.val x‖ := le_abs_self _
      _ ≤ ‖u.val‖ * ‖x‖ := u.val.le_opNorm x
      _ ≤ 1 := by simpa only [u.property, one_mul] using hx'
  · have hm := BodySupport.support_margin_of_closedBall_subset
      (unitBall (E := E)) zero_lt_one (Subset.rfl) u.val
    simpa only [map_zero, zero_add, one_mul, u.property] using hm

end FiniteDimension
end RankThreeProjection
