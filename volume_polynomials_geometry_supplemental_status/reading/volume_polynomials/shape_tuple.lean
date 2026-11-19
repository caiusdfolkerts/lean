module

public import VolumePolynomials.BodyFrames
public import VolumePolynomials.ShapeConditions
public import VolumePolynomials.ProjectionCoordinates

@[expose] public section
noncomputable section

open Set
open scoped Pointwise

namespace VolumePolynomials.Holonomy

def axis (i : Fin 3) : ThreeSpace := Pi.single i 1

def calibratedDirection : Fin 6 → ThreeSpace :=
  ![axis 0, axis 1, axis 2, directionV, directionW, directionZ]

/-- A centered segment of the specified full generating vector. -/
def centeredBody (v : ThreeSpace) : Body 3 :=
  segmentBody (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v)

theorem centeredBody_carrier (v : ThreeSpace) :
    (centeredBody v : Set ThreeSpace) =
      (fun t : ℝ => t • v) '' Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  first
  | have h := image_segment ℝ (LinearMap.toSpanSingleton ℝ ThreeSpace v).toAffineMap
      (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
    rw [segment_eq_Icc (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)] at h
    exact h.symm

theorem zero_mem_centeredBody (v : ThreeSpace) : (0 : ThreeSpace) ∈ centeredBody v := by
  first
  | change (0 : ThreeSpace) ∈ (centeredBody v : Set ThreeSpace)
    rw [centeredBody_carrier]
    exact ⟨0, ⟨by norm_num, by norm_num⟩, zero_smul ℝ v⟩

theorem centeredBody_eq_translate (v : ThreeSpace) :
    centeredBody v = translateBody (-(1 / 2 : ℝ) • v) (segmentBody 0 v) := by
  first
  | rw [translate_segmentBody, add_zero]
    have heq : -(1 / 2 : ℝ) • v + v = (1 / 2 : ℝ) • v := by
      calc
        _ = (-(1 / 2 : ℝ) + 1) • v := by rw [add_smul, one_smul]
        _ = _ := by norm_num
    rw [heq]
    rfl

@[simp] theorem centeredBody_zero : centeredBody (0 : ThreeSpace) = 0 := by
  first
  | apply ConvexBody.ext
    change segment ℝ (-(1 / 2 : ℝ) • (0 : ThreeSpace))
      ((1 / 2 : ℝ) • (0 : ThreeSpace)) = ({0} : Set ThreeSpace)
    simp

theorem centeredBody_smul_sign (s : ℝ) (hs : |s| = 1) (v : ThreeSpace) :
    centeredBody (s • v) = centeredBody v := by
  first
  | rcases eq_or_eq_neg_of_abs_eq hs with rfl | rfl
    · simp
    · apply ConvexBody.ext
      simp only [centeredBody, coe_segmentBody, neg_one_smul, smul_neg, neg_smul, neg_neg,
        one_smul]
      simpa only [neg_smul] using
        (segment_symm ℝ ((1 / 2 : ℝ) • v) (-(1 / 2 : ℝ) • v))

@[simp] theorem map_centeredBody (g : ThreeSpace →L[ℝ] ThreeSpace) (v : ThreeSpace) :
    mapBody g (centeredBody v) = centeredBody (g v) := by
  first
  | simp only [centeredBody, map_segmentBody, map_smul]

/-- The coordinate-normalized geometry needed by the projected comparison
argument.  The last three bodies remain arbitrary compact convex sets. -/
structure IsCalibratedTuple (K : Fin 9 → Body 3) : Prop where
  segments : ∀ i : Fin 6,
    K (ShapeConditions.segmentIndex i) = centeredBody (calibratedDirection i)
  zeroA : (0 : ThreeSpace) ∈ K ShapeConditions.bodyA
  zeroB : (0 : ThreeSpace) ∈ K ShapeConditions.bodyB
  zeroC : (0 : ThreeSpace) ∈ K ShapeConditions.bodyC
  planeA : ∀ x ∈ K ShapeConditions.bodyA, x 2 = 0
  planeB : ∀ x ∈ K ShapeConditions.bodyB, x 1 = 0
  planeC : ∀ x ∈ K ShapeConditions.bodyC, x 0 = 0

/-- Provenance of a normalized tuple: one common volume-preserving linear
equivalence and independent translations of the original bodies. -/
def AffinelyNormalized (K K' : Fin 9 → Body 3) : Prop :=
  ∃ g : ThreeSpace ≃L[ℝ] ThreeSpace,
    |LinearMap.det g.toLinearMap| = 1 ∧
    ∃ t : Fin 9 → ThreeSpace, ∀ i,
      K' i = mapBody g.toContinuousLinearMap (translateBody (t i) (K i))

namespace AffinelyNormalized

theorem refl (K : Fin 9 → Body 3) : AffinelyNormalized K K := by
  first
  | refine ⟨ContinuousLinearEquiv.refl ℝ ThreeSpace, ?_, fun _ => 0, ?_⟩
    · change |LinearMap.det (LinearMap.id : ThreeSpace →ₗ[ℝ] ThreeSpace)| = 1
      rw [LinearMap.det_id, abs_one]
    · intro i
      rw [translateBody_zero]
      apply ConvexBody.ext
      exact (Set.image_id' (K i : Set ThreeSpace)).symm

theorem of_translate (K : Fin 9 → Body 3) (t : Fin 9 → ThreeSpace) :
    AffinelyNormalized K (fun i => translateBody (t i) (K i)) := by
  first
  | refine ⟨ContinuousLinearEquiv.refl ℝ ThreeSpace, ?_, t, ?_⟩
    · change |LinearMap.det (LinearMap.id : ThreeSpace →ₗ[ℝ] ThreeSpace)| = 1
      rw [LinearMap.det_id, abs_one]
    · intro i
      apply ConvexBody.ext
      exact (Set.image_id' (translateBody (t i) (K i) : Set ThreeSpace)).symm

theorem of_map (K : Fin 9 → Body 3) (g : ThreeSpace ≃L[ℝ] ThreeSpace)
    (hg : |LinearMap.det g.toLinearMap| = 1) :
    AffinelyNormalized K (fun i => mapBody g.toContinuousLinearMap (K i)) := by
  first
  | exact ⟨g, hg, fun _ => 0, fun i => by rw [translateBody_zero]⟩

theorem trans {K L M : Fin 9 → Body 3}
    (hKL : AffinelyNormalized K L) (hLM : AffinelyNormalized L M) :
    AffinelyNormalized K M := by
  first
  | obtain ⟨g, hg, t, ht⟩ := hKL
    obtain ⟨h, hh, u, hu⟩ := hLM
    refine ⟨g.trans h, ?_, fun i => t i + g.symm (u i), ?_⟩
    · change |LinearMap.det (h.toLinearMap.comp g.toLinearMap)| = 1
      rw [LinearMap.det_comp, abs_mul, hh, hg, mul_one]
    · intro i
      rw [hu i, ht i]
      change mapBody h.toContinuousLinearMap
        (translateBody (u i) (mapBody g.toContinuousLinearMap
          (translateBody (t i) (K i)))) =
        mapBody (h.toContinuousLinearMap.comp g.toContinuousLinearMap)
          (translateBody (t i + g.symm (u i)) (K i))
      rw [← mapBody_comp]
      simp only [mapBody_translate, translateBody_translate, map_add,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, add_comm]

theorem preservesRealizes {K L : Fin 9 → Body 3} {c : Coefficients 9 3}
    (hKL : AffinelyNormalized K L) (hK : Realizes K c) : Realizes L c := by
  first
  | obtain ⟨g, hg, t, ht⟩ := hKL
    have h := (hK.translate t).map_of_abs_det_one g.toContinuousLinearMap hg
    have heq : L = fun i => mapBody g.toContinuousLinearMap
        (translateBody (t i) (K i)) := funext ht
    rw [heq]
    exact h

theorem volumeFunction_eq {K L : Fin 9 → Body 3}
    (hKL : AffinelyNormalized K L) : volumeFunction L = volumeFunction K := by
  first
  | obtain ⟨g, hg, t, ht⟩ := hKL
    have heq : L = fun i => mapBody g.toContinuousLinearMap
        (translateBody (t i) (K i)) := funext ht
    funext w
    rw [heq, volumeFunction_map]
    change |LinearMap.det g.toLinearMap| *
      volumeFunction (fun i => translateBody (t i) (K i)) w = volumeFunction K w
    rw [hg, one_mul, volumeFunction_translate]

end AffinelyNormalized

end VolumePolynomials.Holonomy
