module

public import Papers.GraphicalZonotopes.TreeJoinGraph

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.TreeJoin
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem outer_core (S : Finset V) : outer (core S)=S := by
  ext v
  simp

theorem core_injective : Function.Injective (core : Finset V → Finset (Vertex V)) := by
  intro S U h
  simpa only [outer_core] using congrArg outer h

theorem core_subset_core_iff (S U : Finset V) : core S⊆core U ↔ S⊆U := by
  constructor
  · intro h v hv
    exact (old_mem_core U v).mp (h ((old_mem_core S v).mpr hv))
  · exact core_mono

theorem outer_clique {T : SimpleGraph V} {C : Finset (Vertex V)}
    (hc : (graph T).IsClique C) : T.IsClique (outer C) := by
  intro u hu v hv huv
  exact hc ((mem_outer C u).mp hu) ((mem_outer C v).mp hv)
    (fun he => huv (old.injective he))

theorem forest_clique_card_le_two {T : SimpleGraph V} (hT : T.IsAcyclic)
    {C : Finset V} (hc : T.IsClique C) : C.card≤2 := by
  by_contra h
  obtain ⟨D,hDC,hD⟩ := exists_subset_card_eq (show 3≤C.card by omega)
  exact hT.cliqueFree_three D ⟨fun u hu v hv huv => hc (hDC hu) (hDC hv) huv,hD⟩

theorem tetrahedron_hubs {T : SimpleGraph V} (hT : T.IsAcyclic)
    {C : Finset (Vertex V)} (hcard : C.card=4) (hcl : (graph T).IsClique C) :
    a∈C ∧ b∈C := by
  have hout := forest_clique_card_le_two hT (outer_clique hcl)
  constructor
  · by_contra ha
    have hs : C⊆insert b ((outer C).map old) := by
      intro x hx
      rcases vertex_cases x with rfl|rfl|⟨v,rfl⟩
      · exact False.elim (ha hx)
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_map.mpr ⟨v,(mem_outer C v).mpr hx,rfl⟩)
    have hn := (card_le_card hs).trans (card_insert_le _ _)
    simp only [card_map] at hn
    omega
  · by_contra hb
    have hs : C⊆insert a ((outer C).map old) := by
      intro x hx
      rcases vertex_cases x with rfl|rfl|⟨v,rfl⟩
      · exact mem_insert_self _ _
      · exact False.elim (hb hx)
      · exact mem_insert_of_mem (mem_map.mpr ⟨v,(mem_outer C v).mpr hx,rfl⟩)
    have hn := (card_le_card hs).trans (card_insert_le _ _)
    simp only [card_map] at hn
    omega

theorem tetrahedra_eq_edges {T : SimpleGraph V} (hT : T.IsAcyclic) :
    tetrahedra (graph T)=(edgeFamily T).image core := by
  ext C
  constructor
  · intro hC
    obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
    obtain ⟨ha,hb⟩ := tetrahedron_hubs hT hc hcl
    have he := core_outer ha hb
    refine mem_image.mpr ⟨outer C,?_,he⟩
    apply (mem_edgeFamily T _).mpr
    refine ⟨?_,fun u hu v hv huv => outer_clique hcl hu hv huv⟩
    have hn := core_card (outer C)
    rw [he,hc] at hn
    omega
  · intro hC
    obtain ⟨E,hE,rfl⟩ := mem_image.mp hC
    obtain ⟨hcard,hcl⟩ := (mem_edgeFamily T E).mp hE
    exact mem_filter.mpr ⟨mem_univ _,by simp [hcard],
      (core_clique_iff T E).mpr hcl⟩

theorem pair_core_injective (v : V) :
    Function.Injective (fun w : V => core ({v,w} : Finset V)) := by
  intro w z he
  have h := core_injective he
  have hw : w=v ∨ w=z := by
    have hm : w∈({v,z} : Finset V) := by rw [←h]; simp
    simpa only [mem_insert,mem_singleton] using hm
  rcases hw with hw|hw
  · have hz : z=v := by
      have hm : z∈({v,w} : Finset V) := by rw [h]; simp
      simpa only [hw,mem_insert,mem_singleton,or_self] using hm
    exact hw.trans hz.symm
  · exact hw

theorem tetrahedra_over_vertex {T : SimpleGraph V} (hT : T.IsAcyclic) (v : V) :
    (tetrahedra (graph T)).filter (fun C => core ({v} : Finset V)⊆C)=
      (T.neighborFinset v).image (fun w => core ({v,w} : Finset V)) := by
  ext C
  constructor
  · intro hC
    obtain ⟨hC,hsub⟩ := mem_filter.mp hC
    rw [tetrahedra_eq_edges hT] at hC
    obtain ⟨E,hE,rfl⟩ := mem_image.mp hC
    have hv : v∈E := singleton_subset_iff.mp ((core_subset_core_iff _ _).mp hsub)
    obtain ⟨hcard,hcl⟩ := (mem_edgeFamily T E).mp hE
    obtain ⟨u,w,huw,rfl⟩ := card_eq_two.mp hcard
    rcases mem_insert.mp hv with hv|hv
    · subst u
      have hadj : T.Adj v w := hcl v (by simp) w (by simp) huw
      exact mem_image.mpr ⟨w,(T.mem_neighborFinset v w).mpr hadj,rfl⟩
    · have he : v=w := mem_singleton.mp hv
      subst w
      have hadj : T.Adj v u := hcl v (by simp) u (by simp) huw.symm
      exact mem_image.mpr ⟨u,(T.mem_neighborFinset v u).mpr hadj,by rw [pair_comm]⟩
  · intro hC
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hC
    have hadj := (T.mem_neighborFinset v w).mp hw
    refine mem_filter.mpr ⟨?_,core_mono (by simp)⟩
    rw [tetrahedra_eq_edges hT]
    exact mem_image.mpr ⟨{v,w},(pair_mem_edgeFamily T (T.ne_of_adj hadj)).mpr hadj,rfl⟩

/-- The triangle through the two hubs and v is contained in exactly
degree(v) tetrahedra. This is the literal multiplicity in the ambient join. -/
theorem triangleMultiplicity_core_singleton {T : SimpleGraph V}
    (hT : T.IsAcyclic) (v : V) :
    triangleMultiplicity (graph T) (core {v})=T.degree v := by
  unfold triangleMultiplicity
  rw [tetrahedra_over_vertex hT,card_image_of_injective _ (pair_core_injective v)]
  exact T.card_neighborFinset_eq_degree v

theorem triangleMultiplicity_le_one_of_missing_hub {T : SimpleGraph V}
    (hT : T.IsAcyclic) {S : Finset (Vertex V)} (hS : S.card=3)
    (hmiss : a∉S ∨ b∉S) : triangleMultiplicity (graph T) S≤1 := by
  rcases hmiss with ha|hb
  · have hs : (tetrahedra (graph T)).filter (fun C => S⊆C)⊆{insert a S} := by
      intro C hC
      obtain ⟨hC,hSC⟩ := mem_filter.mp hC
      obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
      have hsub : insert a S⊆C := insert_subset_iff.mpr
        ⟨(tetrahedron_hubs hT hc hcl).1,hSC⟩
      apply mem_singleton.mpr
      exact (eq_of_subset_of_card_le hsub (by rw [card_insert_of_notMem ha,hS,hc])).symm
    simpa only [triangleMultiplicity,card_singleton] using card_le_card hs
  · have hs : (tetrahedra (graph T)).filter (fun C => S⊆C)⊆{insert b S} := by
      intro C hC
      obtain ⟨hC,hSC⟩ := mem_filter.mp hC
      obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
      have hsub : insert b S⊆C := insert_subset_iff.mpr
        ⟨(tetrahedron_hubs hT hc hcl).2,hSC⟩
      apply mem_singleton.mpr
      exact (eq_of_subset_of_card_le hsub (by rw [card_insert_of_notMem hb,hS,hc])).symm
    simpa only [triangleMultiplicity,card_singleton] using card_le_card hs

/-- For a forest, admissibility of the join is exactly the ordinary
maximum-degree bound three. -/
theorem admissible_iff_maxDegree {T : SimpleGraph V} (hT : T.IsAcyclic) :
    Admissible (graph T) ↔ T.maxDegree≤3 := by
  constructor
  · intro h
    apply T.maxDegree_le_of_forall_degree_le
    intro v
    have hc : (graph T).IsClique (core ({v} : Finset V)) :=
      (core_clique_iff T _).mpr (by simp [SimpleGraph.isClique_singleton])
    have hm := h (core {v}) (by simp) hc
    rwa [triangleMultiplicity_core_singleton hT v] at hm
  · intro h S hS hc
    by_cases ha : a∈S
    · by_cases hb : b∈S
      · have he := core_outer ha hb
        have hs : (outer S).card=1 := by
          have h := core_card (outer S)
          rw [he,hS] at h
          omega
        obtain ⟨v,hv⟩ := card_eq_one.mp hs
        rw [←he,hv,triangleMultiplicity_core_singleton hT v]
        exact (T.degree_le_maxDegree v).trans h
      · exact (triangleMultiplicity_le_one_of_missing_hub hT hS (Or.inr hb)).trans (by decide)
    · exact (triangleMultiplicity_le_one_of_missing_hub hT hS (Or.inl ha)).trans (by decide)

end GraphicalZonotopes.TreeJoin
