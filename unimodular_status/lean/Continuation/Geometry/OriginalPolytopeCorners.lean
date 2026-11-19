module

public import Continuation.Geometry.OriginalPolytopeEdges

/-!
# Original unit corners and deep monotonicity

The unit corner is the Minkowski sum of the unit segments in every actual
primitive inward edge direction, translated to the original vertex. Its
coordinate comparison is an equality of whole real sets. Deep monotonicity
is therefore independent of every integral coordinate choice.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open TauCeti.Toric PaperVerification.OriginalLatticeCharts
open scoped Classical BigOperators

universe u v

namespace Unimodular.OriginalSmoothReflexivePresentation

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} {ι : N →+ V} (P : OriginalSmoothReflexivePresentation n ι)

/-- The actual unit parallelepiped at the original vertex. The coefficient
function is constrained on all primitive inward edge directions. -/
def geometricUnitCorner (v : {v // v ∈ P.vertices}) : Set V :=
  {x | ∃ c : N → ℝ,
    (∀ d ∈ P.primitiveEdgeFinset v, 0 ≤ c d ∧ c d ≤ 1) ∧
    ι v.val + ∑ d ∈ P.primitiveEdgeFinset v, c d • ι d = x}

/-- Deep monotonicity is containment of the actual geometric unit corner
at every original vertex. No coordinate presentation occurs in this definition. -/
def DeeplyMonotone : Prop :=
  ∀ v : {v // v ∈ P.vertices}, P.geometricUnitCorner v ⊆ P.carrier

variable (b : Module.Basis (Fin n) ℤ N)

theorem coordinate_edge_sum (v : {v // v ∈ P.vertices}) (c : N → ℝ) :
    P.ambientCoordinates b (∑ d ∈ P.primitiveEdgeFinset v, c d • ι d) =
      ∑ w ∈ (P.coordinatePresentation b).primitiveEdgeFinset (P.mappedVertex b v),
        c (b.equivFun.symm w) • embed w := by
  rw [← P.primitiveEdgeFinset_coordinate_image b v, Finset.sum_image]
  · simp only [map_sum, map_smul, realCoordinates_lattice, LinearEquiv.symm_apply_apply]
    rfl
  · exact fun i _ j _ hij => b.equivFun.injective hij

/-- Unit-corner membership transports in both directions, with every real
coefficient in the closed interval retained. -/
theorem mem_coordinate_geometricUnitCorner (v : {v // v ∈ P.vertices}) (x : V) :
    P.ambientCoordinates b x ∈
        (P.coordinatePresentation b).geometricUnitCorner (P.mappedVertex b v) ↔
      x ∈ P.geometricUnitCorner v := by
  constructor
  · rintro ⟨c, hc, he⟩
    refine ⟨fun d => c (b.equivFun d), ?_, ?_⟩
    · intro d hd
      apply hc
      rw [← P.primitiveEdgeFinset_coordinate_image b v]
      exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
    · apply (P.ambientCoordinates b).injective
      rw [map_add, realCoordinates_lattice, P.coordinate_edge_sum]
      simp only [LinearEquiv.apply_symm_apply]
      exact he
  · rintro ⟨c, hc, he⟩
    refine ⟨fun w => c (b.equivFun.symm w), ?_, ?_⟩
    · intro w hw
      rw [← P.primitiveEdgeFinset_coordinate_image b v] at hw
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hw
      simpa only [LinearEquiv.symm_apply_apply] using hc d hd
    · have h := congrArg (P.ambientCoordinates b) he
      rw [map_add, realCoordinates_lattice, P.coordinate_edge_sum] at h
      exact h

/-- Equality of the whole real unit corners, not just their vertices. -/
theorem geometricUnitCorner_coordinate_image (v : {v // v ∈ P.vertices}) :
    P.ambientCoordinates b '' P.geometricUnitCorner v =
      (P.coordinatePresentation b).geometricUnitCorner (P.mappedVertex b v) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (P.mem_coordinate_geometricUnitCorner b v x).mpr hx
  · intro hy
    refine ⟨(P.ambientCoordinates b).symm y, ?_,
      (P.ambientCoordinates b).apply_symm_apply y⟩
    apply (P.mem_coordinate_geometricUnitCorner b v _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hy

/-- The intrinsic and coordinate notions of deep monotonicity agree. -/
theorem coordinate_deeplyMonotone_iff :
    (P.coordinatePresentation b).DeeplyMonotone ↔ P.DeeplyMonotone := by
  constructor
  · intro h v x hx
    have hcorner := (P.mem_coordinate_geometricUnitCorner b v x).mpr hx
    have hcarrier := h (P.mappedVertex b v) hcorner
    exact (P.mem_coordinatePresentation_carrier b x).mp hcarrier
  · intro h v y hy
    let v₀ := P.originalVertex b v
    have hx : (P.ambientCoordinates b).symm y ∈ P.geometricUnitCorner v₀ := by
      apply (P.mem_coordinate_geometricUnitCorner b v₀ _).mp
      simp only [LinearEquiv.apply_symm_apply]
      dsimp only [v₀]
      erw [P.mappedVertex_originalVertex]
      exact hy
    have hcarrier := (P.mem_coordinatePresentation_carrier b _).mpr (h v₀ hx)
    simpa only [LinearEquiv.apply_symm_apply] using hcarrier

/-- Changing the integral basis cannot change the geometric property. -/
theorem coordinate_deeplyMonotone_basis_independent
    (c : Module.Basis (Fin n) ℤ N) :
    (P.coordinatePresentation b).DeeplyMonotone ↔
      (P.coordinatePresentation c).DeeplyMonotone :=
  (P.coordinate_deeplyMonotone_iff b).trans (P.coordinate_deeplyMonotone_iff c).symm

/-- The coordinate cube criterion used by the fan proof is derived from
actual original unit corners, in either direction. -/
theorem deeplyMonotone_iff_coordinate_unitCornersContained :
    P.DeeplyMonotone ↔ (P.coordinatePresentation b).UnitCornersContained :=
  (P.coordinate_deeplyMonotone_iff b).symm.trans
    (P.coordinatePresentation b).deeplyMonotone_iff_unitCornersContained

end Unimodular.OriginalSmoothReflexivePresentation
