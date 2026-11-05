module

public import subfaces
public import region_barrier
public import tau_ceti.geometry.polygon.simple
public import tau_ceti.analysis.complex.plane_separation.local_separation

/-!
# A graph cycle in a geometric triangulation is an actual Jordan polygon

Only the cyclic vertex list and its graph edges are bundled. Simplicity and
the Jordan property are conclusions proved from the geometric triangulation.
-/

@[expose] public section

namespace NormalProjective.Planar

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

structure GraphCycle (G : SimpleGraph V) where
  length : ℕ
  length_ge_three : 3 ≤ length
  vertex : Fin length ↪ V
  edge : ∀ i, G.Adj (vertex i) (vertex (finRotate length i))

namespace GraphCycle

variable {T : Triangulation V} (C : GraphCycle T.graph)

instance : NeZero C.length := ⟨by have := C.length_ge_three; omega⟩

def polygon : Polygon ℂ C.length := ⟨fun i => T.point (C.vertex i)⟩

def curve : Set ℂ := C.polygon.boundary ℝ

def vertices : Set V := range C.vertex

theorem rotate_ne (i : Fin C.length) : finRotate C.length i ≠ i := by
  have h := (C.edge i).1
  exact fun e => h (congrArg C.vertex e.symm)

theorem rotate_rotate_ne (i : Fin C.length) :
    finRotate C.length (finRotate C.length i) ≠ i := by
  intro h
  simp only [finRotate_apply] at h
  have hz : (1 : Fin C.length) + 1 = 0 := by
    apply add_left_cancel (a := i)
    simpa only [← add_assoc,add_zero] using h
  have hv := congrArg Fin.val hz
  have := C.length_ge_three
  norm_num [Fin.val_add,Nat.mod_eq_of_lt (show 1 < C.length by omega),
    Nat.mod_eq_of_lt (show 2 < C.length by omega)] at hv

theorem edgeSet_eq (i : Fin C.length) :
    C.polygon.edgeSet ℝ i =
      segment ℝ (T.point (C.vertex i)) (T.point (C.vertex (finRotate C.length i))) := by
  simp [polygon,Polygon.edgeSet,affineSegment_eq_segment]

theorem polygon_isSimple : C.polygon.IsSimple ℝ := by
  classical
  refine ⟨?_,?_⟩
  · intro i h
    apply (C.edge i).1
    exact T.point_injective h
  · intro i j z hij hzi hzj
    rw [C.edgeSet_eq] at hzi hzj
    have hz : z ∈ simplex T.point
        ({C.vertex i,C.vertex (finRotate C.length i)} ∩
          {C.vertex j,C.vertex (finRotate C.length j)}) := by
      rw [← T.edge_intersection (C.edge i) (C.edge j)]
      exact ⟨hzi,hzj⟩
    have hijv : C.vertex i ≠ C.vertex j := C.vertex.injective.ne hij
    have hrr : C.vertex (finRotate C.length i) ≠ C.vertex (finRotate C.length j) :=
      C.vertex.injective.ne ((finRotate C.length).injective.ne hij)
    by_cases hj : j = finRotate C.length i
    · have hir : i ≠ finRotate C.length j := by
        rw [hj]
        exact (C.rotate_rotate_ne i).symm
      have hirv : C.vertex i ≠ C.vertex (finRotate C.length j) := C.vertex.injective.ne hir
      have heq : ({C.vertex i,C.vertex (finRotate C.length i)} ∩
          {C.vertex j,C.vertex (finRotate C.length j)} : Finset V) = {C.vertex j} := by
        ext v
        simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
        rw [← hj]
        aesop
      rw [heq] at hz
      have heqz : z = T.point (C.vertex j) := by simpa [simplex] using hz
      exact Or.inl ⟨hj,heqz⟩
    · by_cases hi : i = finRotate C.length j
      · have hjrv : C.vertex j ≠ C.vertex (finRotate C.length i) := C.vertex.injective.ne hj
        have heq : ({C.vertex i,C.vertex (finRotate C.length i)} ∩
            {C.vertex j,C.vertex (finRotate C.length j)} : Finset V) = {C.vertex i} := by
          ext v
          simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
          rw [← hi]
          aesop
        rw [heq] at hz
        have heqz : z = T.point (C.vertex i) := by simpa [simplex] using hz
        exact Or.inr ⟨hi,heqz⟩
      · have hjrv : C.vertex j ≠ C.vertex (finRotate C.length i) := C.vertex.injective.ne hj
        have hirv : C.vertex i ≠ C.vertex (finRotate C.length j) := C.vertex.injective.ne hi
        have heq : ({C.vertex i,C.vertex (finRotate C.length i)} ∩
            {C.vertex j,C.vertex (finRotate C.length j)} : Finset V) = ∅ := by
          ext v
          simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton,
            Finset.notMem_empty,iff_false]
          aesop
        rw [heq] at hz
        simpa [simplex] using hz

theorem isJordanCurve : TauCeti.IsJordanCurve C.curve := C.polygon_isSimple.isJordanCurve_boundary

theorem curve_isClosed : IsClosed C.curve := C.isJordanCurve.isClosed

theorem point_mem_curve_iff (v : V) : T.point v ∈ C.curve ↔ v ∈ C.vertices := by
  change (T.point v ∈ ⋃ i, C.polygon.edgeSet ℝ i) ↔ _
  constructor
  · intro hv
    obtain ⟨i,hi⟩ := mem_iUnion.mp hv
    rw [C.edgeSet_eq,T.point_mem_edge_iff (C.edge i)] at hi
    rcases hi with rfl | rfl
    · exact ⟨i,rfl⟩
    · exact ⟨finRotate C.length i,rfl⟩
  · rintro ⟨i,rfl⟩
    apply mem_iUnion.mpr
    refine ⟨i,?_⟩
    rw [C.edgeSet_eq]
    exact left_mem_segment ℝ _ _

theorem curve_nonempty : C.curve.Nonempty := by
  have hn : 0 < C.length := by have := C.length_ge_three; omega
  let i : Fin C.length := ⟨0,hn⟩
  exact ⟨T.point (C.vertex i),(C.point_mem_curve_iff _).mpr ⟨i,rfl⟩⟩

theorem curve_subset_domain : C.curve ⊆ T.domain := by
  intro z hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  rw [C.edgeSet_eq,← T.simplex_pair] at hi
  obtain ⟨_,s,hs,ha,hb⟩ := C.edge i
  exact mem_iUnion.mpr ⟨⟨s,hs⟩,convexHull_mono
    (image_mono (show (({C.vertex i,C.vertex (finRotate C.length i)} : Finset V) : Set V) ⊆ s by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ha
      · exact (Finset.mem_singleton.mp hv) ▸ hb)) hi⟩

theorem disjoint_edge_curve {a b : V} (hab : T.graph.Adj a b)
    (ha : a ∉ C.vertices) (hb : b ∉ C.vertices) :
    Disjoint (segment ℝ (T.point a) (T.point b)) C.curve := by
  classical
  rw [Set.disjoint_left]
  intro z hz hzC
  obtain ⟨i,hi⟩ := mem_iUnion.mp hzC
  rw [C.edgeSet_eq] at hi
  have hint : ({a,b} ∩ {C.vertex i,C.vertex (finRotate C.length i)} : Finset V) = ∅ := by
    ext v
    simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,iff_false]
    rintro ⟨rfl | rfl,h | h⟩
    · exact ha ⟨i,h.symm⟩
    · exact ha ⟨finRotate C.length i,h.symm⟩
    · exact hb ⟨i,h.symm⟩
    · exact hb ⟨finRotate C.length i,h.symm⟩
  have hzx : z ∈ simplex T.point
      ({a,b} ∩ {C.vertex i,C.vertex (finRotate C.length i)}) := by
    rw [← T.edge_intersection hab (C.edge i)]
    exact ⟨hz,hi⟩
  rw [hint] at hzx
  simpa [simplex] using hzx

/-- The vertices in a complementary component have graph boundary on the
cycle. A crossing of an edge with the cycle can only occur at a common vertex,
by the proved subface intersections. -/
theorem frontier_component_subset_vertices (q : ℂ) :
    Dirichlet.vertexFrontier T.graph
      {v | T.point v ∈ connectedComponentIn C.curveᶜ q} ⊆ C.vertices := by
  intro v hv
  obtain ⟨hvout,u,hu,huv⟩ := hv
  by_contra hvC
  have huC : u ∉ C.vertices := by
    intro huC
    exact connectedComponentIn_subset _ _ hu ((C.point_mem_curve_iff _).mpr huC)
  have hdis := C.disjoint_edge_curve huv huC hvC
  have hsub : segment ℝ (T.point u) (T.point v) ⊆ C.curveᶜ :=
    fun z hz => Set.disjoint_left.mp hdis hz
  have hvu : T.point v ∈ connectedComponentIn C.curveᶜ (T.point u) :=
    (convex_segment (𝕜 := ℝ) _ _).isPreconnected.subset_connectedComponentIn
      (left_mem_segment ℝ _ _) hsub (right_mem_segment ℝ _ _)
  apply hvout
  rw [connectedComponentIn_eq hu]
  exact hvu

end GraphCycle

end NormalProjective.Planar
