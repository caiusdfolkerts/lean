module

public import graph_polygon
public import triangle_sides

/-! Local straight-edge geometry of the actual Jordan polygon. -/

@[expose] public section

namespace NormalProjective.Planar

open Set Finset Metric
open scoped Topology

theorem openSegment_endpoint_ne {a b z : ℂ} (hab : a ≠ b)
    (hz : z ∈ openSegment ℝ a b) : z ≠ a ∧ z ≠ b := by
  obtain ⟨r,s,hr,hs,hrs,rfl⟩ := hz
  have hr' : r = 1-s := by linarith
  have hs' : s = 1-r := by linarith
  constructor
  · intro h
    have hz : s • (b-a) = (0 : ℂ) := by
      have heq : s • (b-a) + a = 0 + a := by
        calc
          s • (b-a) + a = r • a + s • b := by rw [hr']; module
          _ = 0 + a := by simpa using h
      exact add_right_cancel heq
    exact hab.symm (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (ne_of_gt hs)))
  · intro h
    have hz : r • (a-b) = (0 : ℂ) := by
      have heq : r • (a-b) + b = 0 + b := by
        calc
          r • (a-b) + b = r • a + s • b := by rw [hs']; module
          _ = 0 + b := by simpa using h
      exact add_right_cancel heq
    exact hab (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (ne_of_gt hr)))

theorem mem_openSegment_of_mem_segment_of_ne {a b z : ℂ}
    (hz : z ∈ segment ℝ a b) (ha : z ≠ a) (hb : z ≠ b) :
    z ∈ openSegment ℝ a b := by
  obtain ⟨r,s,hr,hs,hrs,rfl⟩ := hz
  have hr0 : r ≠ 0 := by
    intro h
    have hs1 : s = 1 := by linarith
    simp [h,hs1] at hb
  have hs0 : s ≠ 0 := by
    intro h
    have hr1 : r = 1 := by linarith
    simp [h,hr1] at ha
  exact ⟨r,s,lt_of_le_of_ne hr (Ne.symm hr0),lt_of_le_of_ne hs (Ne.symm hs0),hrs,rfl⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace GraphCycle

variable {T : Triangulation V} (C : GraphCycle T.graph)

/-- Around an interior point of one edge, the entire polygon agrees with the
supporting line. Other edges and both endpoints are excluded using their
actual compact carriers and the proved polygon simplicity. -/
theorem locally_eq_line_of_openEdge (i : Fin C.length) {w : ℂ}
    (hw : w ∈ openSegment ℝ (T.point (C.vertex i))
      (T.point (C.vertex (finRotate C.length i)))) :
    ∃ r > 0, ∀ z ∈ ball w r,
      (z ∈ C.curve ↔
        (((T.point (C.vertex (finRotate C.length i))-T.point (C.vertex i))⁻¹ * (z-w))).im = 0) := by
  classical
  let a := T.point (C.vertex i)
  let b := T.point (C.vertex (finRotate C.length i))
  have hab : a ≠ b := T.point_injective.ne (C.edge i).ne
  have hwend : w ≠ a ∧ w ≠ b := openSegment_endpoint_ne hab hw
  let bad : Set ℂ := ({a,b} : Set ℂ) ∪
    ⋃ j : {j : Fin C.length // j ≠ i}, C.polygon.edgeSet ℝ j.val
  have hclosed : IsClosed bad := by
    apply (isClosed_singleton.union isClosed_singleton).union
    apply isClosed_iUnion_of_finite
    intro j
    rw [C.edgeSet_eq]
    rw [← T.simplex_pair]
    exact (simplex_isCompact T.point _).isClosed
  have hwbad : w ∉ bad := by
    rintro (hend | hother)
    · simp only [mem_insert_iff,mem_singleton_iff] at hend
      exact hend.elim hwend.1 hwend.2
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hother
      have hwi : w ∈ C.polygon.edgeSet ℝ i := by
        rw [C.edgeSet_eq]
        exact openSegment_subset_segment ℝ _ _ hw
      rcases C.polygon_isSimple.eq_vertex_of_mem_edgeSet j.property.symm hwi hj with
        ⟨hji,hwj⟩ | ⟨hij,hwi⟩
      · exact hwend.2 (by simpa [b,hji,polygon] using hwj)
      · exact hwend.1 (by simpa [a,polygon] using hwi)
  obtain ⟨r₁,hr₁,hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hwbad)
  obtain ⟨r₂,hr₂,hline⟩ := TauCeti.exists_ball_openSegment_eq_line hab hw
  refine ⟨min r₁ r₂,lt_min hr₁ hr₂,?_⟩
  intro z hz
  have hz₁ : z ∈ ball w r₁ := ball_subset_ball (min_le_left _ _) hz
  have hz₂ : z ∈ ball w r₂ := ball_subset_ball (min_le_right _ _) hz
  have hzbad : z ∉ bad := hball hz₁
  rw [← hline z hz₂]
  constructor
  · intro hzC
    obtain ⟨j,hj⟩ := mem_iUnion.mp hzC
    have hji : j = i := by
      by_contra hji
      exact hzbad (Or.inr (mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩))
    subst j
    rw [C.edgeSet_eq] at hj
    apply mem_openSegment_of_mem_segment_of_ne hj
    · intro hza
      exact hzbad (Or.inl (by simp [a,b,hza]))
    · intro hzb
      exact hzbad (Or.inl (by simp [a,b,hzb]))
  · intro hzopen
    apply mem_iUnion.mpr
    refine ⟨i,?_⟩
    rw [C.edgeSet_eq]
    exact openSegment_subset_segment ℝ _ _ hzopen

end GraphCycle

end NormalProjective.Planar
