module

public import VolumePolynomials.BodySpan
public import VolumePolynomials.FiberGrowth
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! Coordinates adapted to the actual linear hull of a convex body.
The coordinate factors are finite real coordinate spaces with their actual
Lebesgue measures. Complement and basis choices construct an equivalence;
they are not geometric hypotheses added to a realization theorem. -/

open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.SubspaceCoordinates

open FiberGrowth FiberVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def frame (H U : Submodule ℝ E) (hHU : IsCompl H U) :
    E ≃L[ℝ] (Space (finrank ℝ H) × Space (finrank ℝ U)) :=
  ((H.prodEquivOfIsCompl U hHU).symm.trans
    ((Module.finBasis ℝ H).equivFun.prodCongr (Module.finBasis ℝ U).equivFun)).toContinuousLinearEquiv

theorem frame_on_left (H U : Submodule ℝ E) (hHU : IsCompl H U) (x : H) :
    frame H U hHU (x : E) = ((Module.finBasis ℝ H).equivFun x, 0) := by
  first
  | change ((Module.finBasis ℝ H).equivFun ((H.prodEquivOfIsCompl U hHU).symm (x : E)).1,
      (Module.finBasis ℝ U).equivFun ((H.prodEquivOfIsCompl U hHU).symm (x : E)).2) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp only [map_zero]

theorem frame_on_right (H U : Submodule ℝ E) (hHU : IsCompl H U) (x : U) :
    frame H U hHU (x : E) = (0, (Module.finBasis ℝ U).equivFun x) := by
  first
  | change ((Module.finBasis ℝ H).equivFun ((H.prodEquivOfIsCompl U hHU).symm (x : E)).1,
      (Module.finBasis ℝ U).equivFun ((H.prodEquivOfIsCompl U hHU).symm (x : E)).2) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
    simp only [map_zero]

def coordinateBody (H U : Submodule ℝ E) (hHU : IsCompl H U) (K : ConvexBody E) :
    Body (finrank ℝ H) :=
  mapBody (ContinuousLinearMap.fst ℝ (Space (finrank ℝ H)) (Space (finrank ℝ U)))
    (mapBody (frame H U hHU).toContinuousLinearMap K)

theorem frame_body_eq_embed (H U : Submodule ℝ E) (hHU : IsCompl H U)
    (K : ConvexBody E) (hKH : (K : Set E) ⊆ H) :
    mapBody (frame H U hHU).toContinuousLinearMap K = embedBody (coordinateBody H U hHU K) := by
  first
  | have hz (x : E) (hx : x ∈ K) : (frame H U hHU x).2 = 0 := by
      first
      | have h := frame_on_left H U hHU ⟨x, hKH hx⟩
        exact congrArg Prod.snd h
    apply ConvexBody.ext
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(frame H U hHU x).1, ⟨frame H U hHU x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
      exact Prod.ext rfl (hz x hx).symm
    · rintro ⟨y, ⟨_, ⟨x, hx, rfl⟩, hxy⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      exact Prod.ext hxy (hz x hx)

theorem linearHull_mapBody {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) (K : ConvexBody E) :
    linearHull (mapBody f K) = (linearHull K).map f.toLinearMap :=
  (Submodule.map_span f.toLinearMap (K : Set E)).symm

theorem linearHull_map_eq_top {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) (hf : Function.Surjective f) (K : ConvexBody E)
    (hK : linearHull K = ⊤) : linearHull (mapBody f K) = ⊤ := by
  first
  | rw [linearHull_mapBody, hK, Submodule.map_top, LinearMap.range_eq_top.mpr hf]

theorem coordinateBody_span_top (H U : Submodule ℝ E) (hHU : IsCompl H U)
    (K : ConvexBody E) (hKH : linearHull K = H) :
    linearHull (coordinateBody H U hHU K) = ⊤ := by
  first
  | rw [coordinateBody, linearHull_mapBody, linearHull_mapBody, ← Submodule.map_comp, hKH]
    apply top_unique
    intro y _
    let x : H := (Module.finBasis ℝ H).equivFun.symm y
    refine ⟨(x : E), x.property, ?_⟩
    change (frame H U hHU (x : E)).1 = y
    rw [frame_on_left]
    exact (Module.finBasis ℝ H).equivFun.apply_symm_apply y

theorem zero_mem_coordinateBody (H U : Submodule ℝ E) (hHU : IsCompl H U)
    (K : ConvexBody E) (hK : (0 : E) ∈ K) :
    (0 : Space (finrank ℝ H)) ∈ coordinateBody H U hHU K := by
  first
  | refine ⟨0, ⟨0, hK, map_zero _⟩, map_zero _⟩

theorem coordinateBody_volume_pos (H U : Submodule ℝ E) (hHU : IsCompl H U)
    (K : ConvexBody E) (hK : (0 : E) ∈ K) (hKH : linearHull K = H) :
    0 < bodyVolume (coordinateBody H U hHU K) :=
  Iff.mpr (bodyVolume_pos_iff_linearHull_eq_top (zero_mem_coordinateBody H U hHU K hK))
    (coordinateBody_span_top H U hHU K hKH)

theorem projection_span_top (H U : Submodule ℝ E) (hHU : IsCompl H U)
    (K L : ConvexBody E) (hKH : (K : Set E) ⊆ H)
    (hfull : linearHull (K + L) = ⊤) :
    linearHull (projectionBody (mapBody (frame H U hHU).toContinuousLinearMap L)) = ⊤ := by
  first
  | let T := (frame H U hHU).toContinuousLinearMap
    let snd := ContinuousLinearMap.snd ℝ (Space (finrank ℝ H)) (Space (finrank ℝ U))
    have hfullT := linearHull_map_eq_top T (frame H U hHU).surjective (K + L) hfull
    have hsnd : Function.Surjective snd := fun y => ⟨(0, y), rfl⟩
    have hfullP := linearHull_map_eq_top snd hsnd (mapBody T (K + L)) hfullT
    have heq : mapBody snd (mapBody T (K + L)) = projectionBody (mapBody T L) := by
      first
      | rw [mapBody_add, mapBody_add]
        have hK := frame_body_eq_embed H U hHU K hKH
        change mapBody snd (mapBody (frame H U hHU).toContinuousLinearMap K) + _ = _
        rw [hK, map_snd_embedBody, zero_add]
        rfl
    rwa [heq] at hfullP

theorem projection_volume_pos (H U : Submodule ℝ E) (hHU : IsCompl H U)
    (K L : ConvexBody E) (hKH : (K : Set E) ⊆ H) (hL : (0 : E) ∈ L)
    (hfull : linearHull (K + L) = ⊤) :
    0 < bodyVolume (projectionBody (mapBody (frame H U hHU).toContinuousLinearMap L)) := by
  first
  | apply Iff.mpr (bodyVolume_pos_iff_linearHull_eq_top _)
      (projection_span_top H U hHU K L hKH hfull)
    exact ⟨0, ⟨0, hL, map_zero _⟩, map_zero _⟩

end VolumePolynomials.SubspaceCoordinates
