module

public import Projection.Extrusion
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Module Filter
open scoped Pointwise Topology

namespace RankThreeProjection
open VolumePolynomials

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Simultaneous continuity in the linear map and the compact convex body. -/
theorem continuous_mapBody_joint :
    Continuous (fun p : (E →L[ℝ] F) × ConvexBody E => mapBody p.1 p.2) := by
  apply isometry_bodyToNonemptyCompacts.comp_continuous_iff.mp
  change Continuous (fun p : (E →L[ℝ] F) × ConvexBody E =>
    (bodyToNonemptyCompacts p.2).map p.1 p.1.continuous)
  apply Continuous.nonemptyCompacts_map'
    (continuous_bodyToNonemptyCompacts.comp continuous_snd)
  fun_prop

theorem continuous_mapBody_fixed (L : E →L[ℝ] F) : Continuous (mapBody L) :=
  continuous_mapBody_joint.comp (continuous_const.prodMk continuous_id)

theorem continuous_originSegment : Continuous (originSegment (E := E)) := by
  let L : E →L[ℝ] (ℝ →L[ℝ] E) :=
    ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)
  have he (v : E) : mapBody (L v) (segmentBody (0 : ℝ) 1) = originSegment v := by
    rw [map_segmentBody]
    simp [L, originSegment]
  have hc : Continuous (fun v : E => mapBody (L v) (segmentBody (0 : ℝ) 1)) := by
    simpa only [Function.comp_def] using
      continuous_mapBody_joint.comp
        (L.continuous.prodMk
          (continuous_const : Continuous (fun _ : E => segmentBody (0 : ℝ) 1)))
  simpa only [he] using hc

theorem continuous_centeredSegment : Continuous (centeredSegment (E := E)) := by
  have he (v : E) : mapBody
      (ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ) v)
      (segmentBody (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) = centeredSegment v := by
    rw [map_segmentBody]
    rfl
  have hc : Continuous (fun v : E => mapBody
      (ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ) v)
      (segmentBody (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) := by
    simpa only [Function.comp_def] using
      continuous_mapBody_joint.comp
        ((ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)).continuous.prodMk
          (continuous_const : Continuous
            (fun _ : E => segmentBody (-(1 / 2 : ℝ)) (1 / 2 : ℝ))))
  simpa only [he] using hc

theorem continuous_coordinateVolume {n : ℕ} (I : Finset (Fin n)) :
    Continuous (coordinateVolume I) :=
  (continuous_convexBody_realMeasure volume).comp (continuous_mapBody_fixed (deleteCoordinates I))

theorem continuous_projectionArray {n : ℕ} : Continuous (projectionArray (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : i = j
  · simpa only [projectionArray, if_pos hij] using (continuous_const : Continuous (fun _ : Body n => (0 : ℝ)))
  · simpa only [projectionArray, if_neg hij] using continuous_coordinateVolume {i, j}

/-- Exactly the subsets of coordinates deleted in a projection of codimension k. -/
abbrev Deleted (n k : ℕ) := {I : Finset (Fin n) // I.card = k}

def allProjectionArray {n k : ℕ} (K : Body n) : Deleted n k → ℝ :=
  fun I => coordinateVolume I.val K

def allProjectionLocus (n k : ℕ) : Set (Deleted n k → ℝ) :=
  Set.range (allProjectionArray (n := n) (k := k))

/-- The repeated body and exactly k marked centered segments. The chosen order
is the increasing order on the deleted coordinate set. -/
def markedTuple {n k : ℕ} (K : Body n) (U : Fin n → Space n) (I : Deleted n k) :
    Fin (n - k + k) → Body n :=
  Fin.append (fun _ : Fin (n - k) => K)
    (fun j : Fin k => centeredSegment (U (I.val.orderEmbOfFin I.property j)))

def allMarkedArray {n k : ℕ} (K : Body n) (U : Fin n → Space n) : Deleted n k → ℝ :=
  fun I => (n.factorial : ℝ) / ((n - k).factorial : ℝ) *
    mixedVolume volume (markedTuple K U I)

/-- Affine dimension, taken from the actual affine span of the body. -/
def bodyDimension {n : ℕ} (K : Body n) : ℕ :=
  finrank ℝ (affineSpan ℝ (K : Set (Space n))).direction

theorem continuous_allProjectionArray {n k : ℕ} :
    Continuous (allProjectionArray (n := n) (k := k)) := by
  exact continuous_pi (fun I => continuous_coordinateVolume I.val)

theorem continuous_allMarkedArray {n k : ℕ} :
    Continuous (fun p : Body n × (Fin n → Space n) => allMarkedArray (k := k) p.1 p.2) := by
  apply continuous_pi
  intro I
  apply Continuous.const_mul
  apply (continuous_mixedVolume volume (n - k + k)).comp
  apply continuous_pi
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [markedTuple, Fin.append_left] using
      (continuous_fst : Continuous (fun p : Body n × (Fin n → Space n) => p.1))
  · intro j
    simpa only [markedTuple, Fin.append_right, Function.comp_def] using
      continuous_centeredSegment.comp ((continuous_apply _).comp continuous_snd)

end RankThreeProjection
