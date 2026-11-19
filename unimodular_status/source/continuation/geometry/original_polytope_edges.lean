module

public import Continuation.Geometry.OriginalPolytopeFaces

/-! # Every original primitive edge direction and its integral coordinate image -/

@[expose] public section
noncomputable section
set_option autoImplicit false

open TauCeti.Toric PaperVerification.OriginalLatticeCharts
open Unimodular.OriginalPolytopeTransport
open scoped Classical

universe u v

namespace Unimodular.OriginalSmoothReflexivePresentation

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} {ι : N →+ V} (P : OriginalSmoothReflexivePresentation n ι)

/-- The definition refers only to original lattice vectors, actual extreme
faces, their real affine dimension, and positive feasible edge segments. -/
def primitiveEdgeDirections (v : {v // v ∈ P.vertices}) : Set N :=
  {d | IsPrimitiveEdgeDirection ι P.carrier v.val d}

variable (b : Module.Basis (Fin n) ℤ N)

/-- Every primitive edge witness transports in both directions. -/
theorem primitiveEdge_coordinate_iff (v : {v // v ∈ P.vertices}) (d : N) :
    b.equivFun d ∈ (P.coordinatePresentation b).primitiveEdgeDirections
        (P.mappedVertex b v) ↔ d ∈ P.primitiveEdgeDirections v := by
  simp only [SmoothReflexivePresentation.primitiveEdgeDirections,
    primitiveEdgeDirections, Set.mem_setOf_eq, primitiveLatticeVector_iff_isPrimitive]
  change IsPrimitiveEdgeDirection (FanBridge.standardEmbedding n)
    (P.coordinatePresentation b).carrier (b.equivFun v.val) (b.equivFun d) ↔
      IsPrimitiveEdgeDirection ι P.carrier v.val d
  rw [P.coordinatePresentation_carrier]
  exact primitiveEdge_image_iff b.equivFun (P.ambientCoordinates b)
    (realCoordinates_lattice b P.lattice) P.carrier v.val d

/-- Equality of the complete direction sets, with no chosen edge subset. -/
theorem primitiveEdgeDirections_coordinate_image (v : {v // v ∈ P.vertices}) :
    b.equivFun '' P.primitiveEdgeDirections v =
      (P.coordinatePresentation b).primitiveEdgeDirections (P.mappedVertex b v) := by
  ext d
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact (P.primitiveEdge_coordinate_iff b v d).mpr hd
  · intro hd
    refine ⟨b.equivFun.symm d, ?_, b.equivFun.apply_symm_apply d⟩
    apply (P.primitiveEdge_coordinate_iff b v _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hd

/-- Finiteness follows from the proved complete geometric-edge comparison;
it is not an assumption or a finite edge sample. -/
theorem primitiveEdgeDirections_finite (v : {v // v ∈ P.vertices}) :
    (P.primitiveEdgeDirections v).Finite := by
  let b := P.coordinateBasis
  have h : (b.equivFun '' P.primitiveEdgeDirections v).Finite := by
    rw [P.primitiveEdgeDirections_coordinate_image b v]
    exact (P.coordinatePresentation b).primitiveEdgeDirections_finite (P.mappedVertex b v)
  exact h.of_finite_image b.equivFun.injective.injOn

/-- The finite set consists of all actual primitive inward edges. -/
def primitiveEdgeFinset (v : {v // v ∈ P.vertices}) : Finset N :=
  (P.primitiveEdgeDirections_finite v).toFinset

@[simp] theorem mem_primitiveEdgeFinset (v : {v // v ∈ P.vertices}) (d : N) :
    d ∈ P.primitiveEdgeFinset v ↔ d ∈ P.primitiveEdgeDirections v :=
  (P.primitiveEdgeDirections_finite v).mem_toFinset

theorem primitiveEdgeFinset_coordinate_image (v : {v // v ∈ P.vertices}) :
    (P.primitiveEdgeFinset v).image b.equivFun =
      (P.coordinatePresentation b).primitiveEdgeFinset (P.mappedVertex b v) := by
  apply Finset.coe_injective
  rw [Finset.coe_image]
  simpa only [primitiveEdgeFinset, SmoothReflexivePresentation.primitiveEdgeFinset,
    Set.Finite.coe_toFinset] using P.primitiveEdgeDirections_coordinate_image b v

/-- The actual original edge directions form a basis-sized set, because
the standard geometric theorem exhausts them and the lattice map is injective. -/
theorem primitiveEdgeDirections_eq_inverse_range (v : {v // v ∈ P.vertices}) :
    P.primitiveEdgeDirections v =
      b.equivFun.symm '' Set.range
        (inwardBasisDirection ((P.coordinatePresentation b).basis (P.mappedVertex b v))) := by
  erw [← (P.coordinatePresentation b).primitiveEdgeDirections_eq_range,
    ← P.primitiveEdgeDirections_coordinate_image b v]
  exact b.equivFun.toEquiv.symm_image_image _ |>.symm

end Unimodular.OriginalSmoothReflexivePresentation
