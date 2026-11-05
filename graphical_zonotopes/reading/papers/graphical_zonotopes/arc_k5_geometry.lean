import Papers.GraphicalZonotopes.ArcK5Definitions
import Papers.GraphicalZonotopes.ArcK5Redrawing
import Papers.GraphicalZonotopes.PlanarCrosscutObstruction

open Set Schoenflies GraphicalZonotopes.PlanarGeometry

namespace Graph
namespace IsArcK5

variable {x : Fin 5 → Plane} {P : Fin 5 → Fin 5 → Set Plane}
variable (h : IsArcK5 x P)
include h

theorem inter_indices {i j k l : Fin 5} (hij : i ≠ j) (hkl : k ≠ l)
    (hne : (i, j) ≠ (k, l)) (hrev : (i, j) ≠ (l, k))
    {z : Plane} (hz : z ∈ P i j) (hz' : z ∈ P k l) :
    ∃ t : Fin 5, z = x t ∧ (t = i ∨ t = j) ∧ (t = k ∨ t = l) := by
  have hm := (h.meet i j k l hij hkl hne hrev ⟨hz, hz'⟩).1
  rcases hm with rfl | rfl
  · exact ⟨i, rfl, Or.inl rfl, h.vertex k l i hkl hz'⟩
  · exact ⟨j, rfl, Or.inr rfl, h.vertex k l j hkl hz'⟩

theorem disjoint_edges {i j k l : Fin 5} (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    Disjoint (P i j) (P k l) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨t, _, ht, ht'⟩ := h.inter_indices hij hkl
    (fun e => hik (congrArg Prod.fst e))
    (fun e => hil (congrArg Prod.fst e)) hz hz'
  rcases ht with rfl | rfl <;> rcases ht' with h' | h'
  exacts [hik h', hil h', hjk h', hjl h']

omit h in
def two (P : Fin 5 → Fin 5 → Set Plane) (i j k : Fin 5) : Set Plane :=
  P i j ∪ P j k

theorem two_arc {i j k : Fin 5} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    IsArcBetween (two P i j k) (x i) (x k) := by
  apply (h.arc i j hij).concatenate (h.arc j k hjk)
  intro z hz hz'
  obtain ⟨t, rfl, ht, ht'⟩ := h.inter_indices hij hjk
    (fun e => hij (congrArg Prod.fst e))
    (fun e => hik (congrArg Prod.fst e)) hz hz'
  rcases ht with rfl | rfl
  · rcases ht' with h' | h'
    · exact (hij h').elim
    · exact (hik h').elim
  · rfl

theorem two_poly (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j))
    {i j k : Fin 5} (hij : i ≠ j) (hjk : j ≠ k) :
    IsPolygonal (two P i j k) :=
  (hpoly i j hij).union (hpoly j k hjk)
    ⟨x j, (h.arc i j hij).right_mem, (h.arc j k hjk).left_mem⟩

theorem vertex_two {i j k t : Fin 5} (hij : i ≠ j) (hjk : j ≠ k)
    (ht : x t ∈ two P i j k) : t = i ∨ t = j ∨ t = k := by
  rcases ht with ht | ht
  · rcases h.vertex i j t hij ht with he | he
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
  · exact Or.inr (h.vertex j k t hjk ht)

omit h in
/-- The four-cycle through the first four branch vertices. -/
def fourCycle (P : Fin 5 → Fin 5 → Set Plane) : Set Plane :=
  two P 0 1 2 ∪ two P 0 3 2

theorem fourCycle_arcs_inter :
    two P 0 1 2 ∩ two P 0 3 2 = ({x 0, x 2} : Set Plane) := by
  apply Set.Subset.antisymm
  · rintro z ⟨hz, hz'⟩
    rcases hz with hz | hz <;> rcases hz' with hz' | hz'
    all_goals
      obtain ⟨t, rfl, ht, ht'⟩ := h.inter_indices
        (by decide) (by decide) (by decide) (by decide) hz hz'
      fin_cases t <;> simp_all
  · rintro z (rfl | rfl)
    · exact ⟨(h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).left_mem,
        (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide)).left_mem⟩
    · exact ⟨(h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).right_mem,
        (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide)).right_mem⟩

theorem fourCycle_sep (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j)) :
    IsSeparating (fourCycle P) := by
  apply Schoenflies.isSeparating_of_isJordanCurve
  · apply Schoenflies.isJordanCurve_union
      (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide))
      (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide))
    intro z hz hz'
    have hm := h.fourCycle_arcs_inter ▸ (show z ∈ two P 0 1 2 ∩ two P 0 3 2 from ⟨hz, hz'⟩)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  · exact (h.two_poly hpoly (i := 0) (j := 1) (k := 2) (by decide) (by decide)).union
      (h.two_poly hpoly (i := 0) (j := 3) (k := 2) (by decide) (by decide))
      ⟨x 0,
        (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).left_mem,
        (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide)).left_mem⟩

theorem fifth_not_fourCycle : x 4 ∉ fourCycle P := by
  rintro (hm | hm)
  · have := h.vertex_two (by decide : (0 : Fin 5) ≠ 1) (by decide : (1 : Fin 5) ≠ 2) hm
    simp at this
  · have := h.vertex_two (by decide : (0 : Fin 5) ≠ 3) (by decide : (3 : Fin 5) ≠ 2) hm
    simp at this

omit h in
abbrev cycleSide (i j : Fin 5) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 2)

theorem inter_fourCycle_pair {i j : Fin 5} (hij : i ≠ j)
    (hne : ∀ a b, cycleSide a b → (i, j) ≠ (a, b) ∧ (i, j) ≠ (b, a)) :
    P i j ∩ fourCycle P ⊆ ({x i, x j} : Set Plane) := by
  rintro z ⟨hz, hzC⟩
  rcases hzC with (hzC | hzC) | (hzC | hzC)
  · exact (h.meet i j 0 1 hij (by decide) (hne 0 1 (by decide)).1
      (hne 0 1 (by decide)).2 ⟨hz, hzC⟩).1
  · exact (h.meet i j 1 2 hij (by decide) (hne 1 2 (by decide)).1
      (hne 1 2 (by decide)).2 ⟨hz, hzC⟩).1
  · exact (h.meet i j 0 3 hij (by decide) (hne 0 3 (by decide)).1
      (hne 0 3 (by decide)).2 ⟨hz, hzC⟩).1
  · exact (h.meet i j 3 2 hij (by decide) (hne 3 2 (by decide)).1
      (hne 3 2 (by decide)).2 ⟨hz, hzC⟩).1

theorem diagonal_inter_fourCycle :
    P 0 2 ∩ fourCycle P = ({x 0, x 2} : Set Plane) := by
  apply Set.Subset.antisymm (h.inter_fourCycle_pair (by decide) (by decide))
  rintro z (rfl | rfl)
  · exact ⟨(h.arc 0 2 (by decide)).left_mem,
      Or.inl (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).left_mem⟩
  · exact ⟨(h.arc 0 2 (by decide)).right_mem,
      Or.inl (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).right_mem⟩

theorem fourCycle_poly (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j)) :
    IsPolygonal (fourCycle P) :=
  (h.two_poly hpoly (i := 0) (j := 1) (k := 2) (by decide) (by decide)).union
    (h.two_poly hpoly (i := 0) (j := 3) (k := 2) (by decide) (by decide))
    ⟨x 0,
      (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).left_mem,
      (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide)).left_mem⟩

theorem diagonal_intersects (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j))
    {Q Ω : Set Plane} (hΩ : IsRegionOf (fourCycle P) Ω)
    (hPΩ : P 0 2 \ {x 0, x 2} ⊆ Ω)
    (hQ : IsArcBetween Q (x 1) (x 3)) (hQΩ : Q \ {x 1, x 3} ⊆ Ω) :
    (Q ∩ P 0 2).Nonempty := by
  apply alternating_arc_inter_nonempty (h.fourCycle_sep hpoly) (h.fourCycle_poly hpoly)
    (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide))
    (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide))
    (h.two_poly hpoly (i := 0) (j := 1) (k := 2) (by decide) (by decide))
    (h.two_poly hpoly (i := 0) (j := 3) (k := 2) (by decide) (by decide))
    rfl h.fourCycle_arcs_inter (h.arc 0 2 (by decide)) (hpoly 0 2 (by decide))
    h.diagonal_inter_fourCycle hΩ hPΩ hQ hQΩ
  · refine ⟨Or.inl (h.arc 0 1 (by decide)).right_mem, ?_⟩
    rintro (he | he) <;> have := h.injective he <;> norm_num at this
  · refine ⟨Or.inl (h.arc 0 3 (by decide)).right_mem, ?_⟩
    rintro (he | he) <;> have := h.injective he <;> norm_num at this

theorem fifth_path_diff_subset_compl :
    two P 1 4 3 \ {x 1, x 3} ⊆ (fourCycle P)ᶜ := by
  rintro z ⟨hz, hzends⟩ hzC
  rcases hz with hz | hz
  · have hm := h.inter_fourCycle_pair (i := 1) (j := 4) (by decide) (by decide) ⟨hz, hzC⟩
    rcases hm with rfl | rfl
    · exact hzends (Or.inl rfl)
    · exact h.fifth_not_fourCycle hzC
  · have hm := h.inter_fourCycle_pair (i := 4) (j := 3) (by decide) (by decide) ⟨hz, hzC⟩
    rcases hm with rfl | rfl
    · exact h.fifth_not_fourCycle hzC
    · exact hzends (Or.inr rfl)

theorem fifth_mem_path_diff : x 4 ∈ two P 1 4 3 \ {x 1, x 3} := by
  refine ⟨Or.inl (h.arc 1 4 (by decide)).right_mem, ?_⟩
  rintro (he | he) <;> have := h.injective he <;> norm_num at this

/-- A region containing the first diagonal cannot also contain the fifth vertex:
the two incident edges through that vertex give an alternating crosscut. -/
theorem diagonal_fifth_false (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j))
    {Ω : Set Plane} (hΩ : IsRegionOf (fourCycle P) Ω)
    (hPΩ : P 0 2 \ {x 0, x 2} ⊆ Ω) (hx4 : x 4 ∈ Ω) : False := by
  have hR := h.two_arc (i := 1) (j := 4) (k := 3) (by decide) (by decide) (by decide)
  have hRΩ : two P 1 4 3 \ {x 1, x 3} ⊆ Ω := by
    have hh := hR.isPreconnected_diff.subset_connectedComponentIn
      h.fifth_mem_path_diff h.fifth_path_diff_subset_compl
    rwa [hΩ.connectedComponentIn_eq (h.fourCycle_sep hpoly) hx4] at hh
  obtain ⟨z, hzR, hzP⟩ := h.diagonal_intersects hpoly hΩ hPΩ hR hRΩ
  rcases hzR with hzR | hzR
  · exact Set.disjoint_left.1 (h.disjoint_edges
      (i := 0) (j := 2) (k := 1) (l := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hzP hzR
  · exact Set.disjoint_left.1 (h.disjoint_edges
      (i := 0) (j := 2) (k := 4) (l := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hzP hzR

theorem relabel (e : Fin 5 ≃ Fin 5) :
    IsArcK5 (fun i => x (e i)) (fun i j => P (e i) (e j)) where
  injective := h.injective.comp e.injective
  arc i j hij := h.arc (e i) (e j) (fun h' => hij (e.injective h'))
  symm i j := h.symm (e i) (e j)
  vertex i j k hij hmem := by
    rcases h.vertex (e i) (e j) (e k) (fun h' => hij (e.injective h')) hmem with he | he
    · exact Or.inl (e.injective he)
    · exact Or.inr (e.injective he)
  meet i j k l hij hkl hne hrev := by
    apply h.meet (e i) (e j) (e k) (e l)
      (fun h' => hij (e.injective h')) (fun h' => hkl (e.injective h'))
    · intro he
      exact hne (Prod.ext (e.injective (congrArg Prod.fst he))
        (e.injective (congrArg Prod.snd he)))
    · intro he
      exact hrev (Prod.ext (e.injective (congrArg Prod.fst he))
        (e.injective (congrArg Prod.snd he)))

omit h in
def alternateOrder : Fin 5 ≃ Fin 5 := (Equiv.swap 0 1).trans (Equiv.swap 2 3)

theorem fourCycle_alternate :
    fourCycle (fun i j => P (alternateOrder i) (alternateOrder j)) = fourCycle P := by
  change (P 1 0 ∪ P 0 3) ∪ (P 1 2 ∪ P 2 3) = (P 0 1 ∪ P 1 2) ∪ (P 0 3 ∪ P 3 2)
  rw [h.symm 1 0, h.symm 2 3]
  ext z
  simp only [Set.mem_union]
  tauto

omit h in
private theorem arc_diff_nonempty {A : Set Plane} {a b : Plane}
    (hA : IsArcBetween A a b) : (A \ {a, b}).Nonempty := by
  by_contra hn
  rw [Set.not_nonempty_iff_eq_empty] at hn
  have hh := hA.left_mem_closure_diff
  simpa [hn] using hh

/-- Five pairwise connected branch points cannot be drawn by polygonal arcs
meeting only at their common endpoints. -/
theorem false_of_polygonal (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j)) : False := by
  classical
  have hC := h.fourCycle_sep hpoly
  have hP := h.arc 0 2 (by decide)
  have hQ := h.arc 1 3 (by decide)
  have hPcomp : P 0 2 \ {x 0, x 2} ⊆ (fourCycle P)ᶜ := by
    rintro z ⟨hz, hzends⟩ hzC
    exact hzends (h.inter_fourCycle_pair (by decide) (by decide) ⟨hz, hzC⟩)
  have hQcomp : P 1 3 \ {x 1, x 3} ⊆ (fourCycle P)ᶜ := by
    rintro z ⟨hz, hzends⟩ hzC
    exact hzends (h.inter_fourCycle_pair (by decide) (by decide) ⟨hz, hzC⟩)
  obtain ⟨Ω, Ω', hpair, hPΩ⟩ := hC.exists_isRegionPair_subset
    hP.isPreconnected_diff (arc_diff_nonempty hP) (Set.disjoint_left.2 hPcomp)
  have hcover : P 1 3 \ {x 1, x 3} ⊆ Ω ∪ Ω' := by
    rw [hpair.union_eq]
    exact hQcomp
  have hQΩ' : P 1 3 \ {x 1, x 3} ⊆ Ω' := by
    intro z hz
    rcases hcover hz with hzΩ | hzΩ'
    · have hQΩ := hQ.isPreconnected_diff.subset_left_of_subset_union
        (hpair.left.isOpen hC) (hpair.right.isOpen hC) hpair.disjoint hcover ⟨z, hz, hzΩ⟩
      obtain ⟨w, hwQ, hwP⟩ := h.diagonal_intersects hpoly hpair.left hPΩ hQ hQΩ
      exact (Set.disjoint_left.1 (h.disjoint_edges
        (i := 0) (j := 2) (k := 1) (l := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hwP hwQ).elim
    · exact hzΩ'
  have hx4 : x 4 ∈ Ω ∪ Ω' := by
    rw [hpair.union_eq]
    exact h.fifth_not_fourCycle
  rcases hx4 with hx4 | hx4
  · exact h.diagonal_fifth_false hpoly hpair.left hPΩ hx4
  · have h' := h.relabel alternateOrder
    have hp' : ∀ i j, i ≠ j → IsPolygonal (P (alternateOrder i) (alternateOrder j)) :=
      fun i j hij => hpoly _ _ (fun he => hij (alternateOrder.injective he))
    apply h'.diagonal_fifth_false hp' (Ω := Ω')
    · rw [h.fourCycle_alternate]
      exact hpair.right
    · change P 1 3 \ {x 1, x 3} ⊆ Ω'
      exact hQΩ'
    · change x 4 ∈ Ω'
      exact hx4

/-- No topological K5 arc configuration exists.  This includes subdivisions:
each branch path is simply the arc joining its two branch vertices. -/
theorem elim : False := by
  obtain ⟨P', hP', hpoly⟩ := h.exists_polygonal
  exact hP'.false_of_polygonal hpoly

end IsArcK5
end Graph
