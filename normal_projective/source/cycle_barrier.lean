module

public import graph_polygon
public import triangular_disk
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Strict harmonic barrier inside an actual graph polygon

A complementary region is not postulated to be a triangulation. Its exterior
graph neighbours lie on the actual Jordan polygon by `graph_polygon`; the
finite-region maximum principle therefore applies. Strictness uses a positive
source half-plane, whose graph connectivity was proved from convex geometry.
-/

@[expose] public section

namespace NormalProjective.Planar

open Set Finset

theorem baseTriangle_isClosed : IsClosed baseTriangle := by
  have heq : baseTriangle = ⋂ j : Fin 3, {z | 0 ≤ triangleCoordinate j z} := by
    ext z
    simp [baseTriangle]
  rw [heq]
  exact isClosed_iInter (fun j => isClosed_le continuous_const (coordinate_continuous j))

theorem basePoint_not_interior (j : Fin 3) : basePoint j ∉ interior baseTriangle := by
  intro hj
  have hre : 0 < (basePoint j).re := by
    have hsub : baseTriangle ⊆ {z : ℂ | 0 ≤ z.re} := fun z hz => hz 1
    have h := interior_mono hsub hj
    simpa only [Complex.interior_setOfPred_le_re,mem_setOf_eq] using h
  have him : 0 < (basePoint j).im := by
    have hsub : baseTriangle ⊆ {z : ℂ | 0 ≤ z.im} := fun z hz => hz 2
    have h := interior_mono hsub hj
    simpa only [Complex.interior_setOfPred_le_im,mem_setOf_eq] using h
  fin_cases j <;> simp_all [basePoint]

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace GraphCycle

variable {T : Triangulation V} (C : GraphCycle T.graph)

noncomputable def vertexFinset : Finset V := Finset.univ.image C.vertex

theorem mem_vertexFinset (v : V) : v ∈ C.vertexFinset ↔ v ∈ C.vertices := by
  simp [vertexFinset,vertices]

theorem curve_subset_vertexHull : C.curve ⊆ simplex T.point C.vertexFinset := by
  intro z hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  rw [C.edgeSet_eq] at hi
  apply (convex_convexHull ℝ _).segment_subset _ _ hi
  · exact point_mem_simplex T.point C.vertexFinset
      ((C.mem_vertexFinset _).mpr ⟨i,rfl⟩)
  · exact point_mem_simplex T.point C.vertexFinset
      ((C.mem_vertexFinset _).mpr ⟨finRotate C.length i,rfl⟩)

theorem filledHull_subset_vertexHull :
    TauCeti.filledHull C.curve ⊆ simplex T.point C.vertexFinset := by
  apply (TauCeti.filledHull_subset_closedConvexHull C.curve_nonempty).trans
  exact closedConvexHull_min C.curve_subset_vertexHull (convex_convexHull ℝ _)
    (simplex_isCompact T.point C.vertexFinset).isClosed

theorem component_subset_filledHull {q : ℂ} (hq : q ∈ TauCeti.filledHull C.curve) :
    connectedComponentIn C.curveᶜ q ⊆ TauCeti.filledHull C.curve := by
  intro z hz
  rw [TauCeti.mem_filledHull_iff,← connectedComponentIn_eq hz]
  exact TauCeti.mem_filledHull_iff.mp hq

end GraphCycle

namespace TriangularDisk

variable (D : TriangularDisk V) (C : GraphCycle D.toTriangulation.graph)

theorem filledHull_curve_subset_triangle : TauCeti.filledHull C.curve ⊆ baseTriangle := by
  apply (TauCeti.filledHull_subset_closedConvexHull C.curve_nonempty).trans
  apply closedConvexHull_min _ baseTriangle_convex baseTriangle_isClosed
  exact C.curve_subset_domain.trans (D.domain_eq ▸ Subset.rfl)

theorem component_disjoint_boundary {q : ℂ} (hq : q ∈ TauCeti.filledHull C.curve) :
    Disjoint {v | D.point v ∈ connectedComponentIn C.curveᶜ q} D.boundary := by
  rw [Set.disjoint_left]
  intro v hv hvB
  obtain ⟨j,rfl⟩ := hvB
  have hopen : IsOpen (connectedComponentIn C.curveᶜ q) :=
    C.curve_isClosed.isOpen_compl.connectedComponentIn
  have hsub : connectedComponentIn C.curveᶜ q ⊆ baseTriangle :=
    (C.component_subset_filledHull hq).trans (D.filledHull_curve_subset_triangle C)
  have hint := interior_maximal hsub hopen hv
  rw [D.corner_point] at hint
  exact basePoint_not_interior j hint

/-- The exact strict barrier needed in Floater's adjacent-face argument.
`l > c` selects a genuine source half-plane containing the enclosed vertex and
avoiding any exceptional cycle vertices where the harmonic value is zero. -/
theorem strict_cycle_barrier
    (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
    (hoff : ∀ i j, ¬ D.toTriangulation.graph.Adj i j → w i j = 0)
    (h : V → ℝ) (hh : ∀ i, i ∉ D.boundary → Dirichlet.Harmonic w h i)
    (hC : ∀ v ∈ C.vertices, h v ≤ 0)
    (l : ℂ →L[ℝ] ℝ) (c : ℝ)
    (hCstrict : ∀ v ∈ C.vertices, c < l (D.point v) → h v < 0)
    (i : V) (hi : D.point i ∈ TauCeti.filledHull C.curve \ C.curve)
    (hil : c < l (D.point i)) : h i < 0 := by
  let S : Set V := {v | D.point v ∈ connectedComponentIn C.curveᶜ (D.point i)}
  let A : Set V := {v | c < l (D.point v)}
  have hiS : i ∈ S := mem_connectedComponentIn hi.2
  have hSB := D.component_disjoint_boundary C hi.1
  have hfront : Dirichlet.vertexFrontier D.toTriangulation.graph S ⊆ C.vertices :=
    C.frontier_component_subset_vertices (D.point i)
  have hix : D.point i ∈ simplex D.point C.vertexFinset :=
    C.filledHull_subset_vertexHull hi.1
  obtain ⟨b,hb,hbl⟩ := D.toTriangulation.exists_positive_vertex l c C.vertexFinset hix hil
  have hbC : b ∈ C.vertices := (C.mem_vertexFinset b).mp hb
  have hbS : b ∉ S := by
    intro hbS
    exact connectedComponentIn_subset _ _ hbS ((C.point_mem_curve_iff b).mpr hbC)
  have hconvex : Convex ℝ D.toTriangulation.domain := D.domain_eq ▸ baseTriangle_convex
  have hconn := D.toTriangulation.positive_induce_connected hconvex l c ⟨i,hil⟩
  exact Dirichlet.strict_maximum_on_region_along_path D.toTriangulation.graph D.graph_connected
    S A w hw he hoff h
    (fun v hv => hh v (fun hvB => Set.disjoint_left.mp hSB hv hvB))
    0 (fun v hv => hC v (hfront hv))
    (fun v hvA hv => hCstrict v (hfront hv) hvA)
    i b hiS hil hbS hbl (hconn ⟨i,hil⟩ ⟨b,hbl⟩)

end TriangularDisk

end NormalProjective.Planar
