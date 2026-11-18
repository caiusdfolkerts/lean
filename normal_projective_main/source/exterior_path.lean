module

public import cycle_barrier
public import boundary_corners
public import falling_paths

/-! Positive paths lead to the exterior of the negative Jordan polygon. -/

@[expose] public section

namespace NormalProjective.Planar

open Set Finset Relation

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace GraphCycle

variable {T : Triangulation V} (C : GraphCycle T.graph)

theorem edge_same_component {a b : V} (hab : T.graph.Adj a b)
    (ha : a ∉ C.vertices) (hb : b ∉ C.vertices) :
    T.point b ∈ connectedComponentIn C.curveᶜ (T.point a) := by
  have hdis := C.disjoint_edge_curve hab ha hb
  apply (convex_segment (𝕜 := ℝ) _ _).isPreconnected.subset_connectedComponentIn
    (left_mem_segment ℝ _ _) _ (right_mem_segment ℝ _ _)
  exact fun z hz => Set.disjoint_left.mp hdis hz

theorem increasingPath_same_component (x : V → ℝ)
    (hC : ∀ v ∈ C.vertices, x v ≤ 0) {a b : V} (ha : 0 < x a)
    (hab : ReflTransGen (Dirichlet.IncreasingEdge T.graph x) a b) :
    T.point b ∈ connectedComponentIn C.curveᶜ (T.point a) := by
  have haC : a ∉ C.vertices := fun h => (not_le_of_gt ha) (hC a h)
  induction hab with
  | refl => exact mem_connectedComponentIn (fun h => haC ((C.point_mem_curve_iff a).mp h))
  | @tail u v hau huv ih =>
    have hup : 0 < x u := lt_of_lt_of_le ha (Dirichlet.increasingPath_le T.graph x hau)
    have hvp : 0 < x v := hup.trans huv.2
    have huC : u ∉ C.vertices := fun h => (not_le_of_gt hup) (hC u h)
    have hvC : v ∉ C.vertices := fun h => (not_le_of_gt hvp) (hC v h)
    have hcomp := C.edge_same_component huv.1 huC hvC
    rw [connectedComponentIn_eq ih]
    exact hcomp

end GraphCycle

namespace TriangularDisk

variable (D : TriangularDisk V) (C : GraphCycle D.toTriangulation.graph)

theorem corner_not_in_filledHull (j : Fin 3) (hj : D.corner j ∉ C.vertices) :
    D.point (D.corner j) ∉ TauCeti.filledHull C.curve := by
  intro hfilled
  have hsub : simplex D.point C.vertexFinset ⊆
      {z | coordinateLinear j z < coordinateThreshold j + 1} := by
    apply convexHull_min
    · rintro _ ⟨v,hv,rfl⟩
      have hvj : v ≠ D.corner j := by
        intro h
        exact hj (h ▸ (C.mem_vertexFinset v).mp hv)
      have hlt := D.coordinate_lt_one_of_ne_corner j v hvj
      rw [coordinate_eq_linear] at hlt
      change coordinateLinear j (D.point v) < coordinateThreshold j + 1
      linarith
    · exact convex_halfSpace_lt (coordinateLinear j).toLinearMap.isLinear _
  have hlt := hsub (C.filledHull_subset_vertexHull hfilled)
  change coordinateLinear j (D.point (D.corner j)) < coordinateThreshold j + 1 at hlt
  have heq : triangleCoordinate j (D.point (D.corner j)) = 1 := by
    simp [D.corner_point,coordinate_basePoint]
  rw [coordinate_eq_linear] at heq
  linarith

/-- A positive vertex adjacent to a lower vertex lies outside a cycle whose
vertices have nonpositive height. The rising path ends at an actual extreme
corner of the triangular domain; the corner is outside the cycle's convex
hull, hence outside its filled hull. -/
theorem positive_vertex_outside_cycle
    (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
    (hoff : ∀ i j, ¬ D.toTriangulation.graph.Adj i j → w i j = 0)
    (h : V → ℝ) (hh : ∀ i, i ∉ D.boundary → Dirichlet.Harmonic w h i)
    (hC : ∀ v ∈ C.vertices, h v ≤ 0)
    {a v : V} (hva : D.toTriangulation.graph.Adj v a)
    (hav : h a < h v) (hv : 0 < h v) :
    D.point v ∉ TauCeti.filledHull C.curve := by
  obtain ⟨b,hbB,hvb,hvbheight⟩ := Dirichlet.exists_rising_path_to_boundary
    D.toTriangulation.graph D.boundary w hw he hoff h hh hva hav
  obtain ⟨j,rfl⟩ := hbB
  have hjC : D.corner j ∉ C.vertices := by
    intro hjC
    have h := hC _ hjC
    linarith
  have hcomp := C.increasingPath_same_component h hC hv hvb
  intro hvfilled
  exact D.corner_not_in_filledHull C j hjC (C.component_subset_filledHull hvfilled hcomp)

end TriangularDisk

end NormalProjective.Planar
