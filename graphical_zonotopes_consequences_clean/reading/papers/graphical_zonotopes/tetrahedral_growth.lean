module

public import Papers.GraphicalZonotopes.GraphModels
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The induced graph, represented on the original vertex type with isolated
vertices outside the displayed set. -/
def inducedOn (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨fun _ _ h => ⟨G.adj_symm h.1,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

/-- A tetrahedron followed by vertices attached along existing triangles of
the ambient graph. Extra ambient edges are allowed; equality in the eventual
edge count will prove that there are no extras. -/
inductive TetrahedralGrowth (G : SimpleGraph V) : Finset V → Prop
  | base (C : Finset V) (hcard : C.card = 4) (hcl : G.IsClique C) :
      TetrahedralGrowth G C
  | attach {S : Finset V} (h : TetrahedralGrowth G S) (u : V) (hu : u ∉ S)
      (T : Finset V) (hcard : T.card = 3) (hsub : T ⊆ S) (hcl : G.IsClique T)
      (hadj : ∀ v ∈ T, G.Adj u v) : TetrahedralGrowth G (insert u S)

theorem TetrahedralGrowth.card_ge_four {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) : 4 ≤ S.card := by
  induction h with
  | base C hc hcl => omega
  | attach h u hu T hT hsub hcl hadj ih =>
    rw [card_insert_of_notMem hu]
    omega

/-- A tetrahedron sharing a triangle with the vertices already present adds
at most one vertex. Steps adding no vertex need no extra assumption. -/
theorem TetrahedralGrowth.extend_fourClique {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (C : Finset V) (hc : C.card = 4)
    (hcl : G.IsClique C) (hover : 3 ≤ (C ∩ S).card) :
    TetrahedralGrowth G (S ∪ C) := by
  have hcard := card_sdiff_add_card_inter C S
  have hsmall : (C \ S).card = 0 ∨ (C \ S).card = 1 := by omega
  rcases hsmall with hz | ho
  · have hsub : C ⊆ S := sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hz)
    simpa only [union_eq_left.mpr hsub] using h
  · obtain ⟨u,hu⟩ := card_eq_one.mp ho
    have humem : u ∈ C \ S := by rw [hu]; exact mem_singleton_self u
    have huC : u ∈ C := (mem_sdiff.mp humem).1
    have huS : u ∉ S := (mem_sdiff.mp humem).2
    let T := C.erase u
    have hTcard : T.card = 3 := by
      dsimp [T]
      rw [card_erase_of_mem huC,hc]
    have hTS : T ⊆ S := by
      intro v hv
      obtain ⟨hvu,hvC⟩ := mem_erase.mp hv
      by_contra hvS
      have hm : v ∈ C \ S := mem_sdiff.mpr ⟨hvC,hvS⟩
      rw [hu] at hm
      exact hvu (mem_singleton.mp hm)
    have hTcl : G.IsClique T := fun v hv w hw hvw =>
      hcl (mem_of_mem_erase hv) (mem_of_mem_erase hw) hvw
    have hA : ∀ v ∈ T, G.Adj u v := by
      intro v hv
      have hm := mem_erase.mp hv
      exact hcl huC hm.2 (Ne.symm hm.1)
    have hcover : S ∪ C = insert u S := by
      ext v
      simp only [mem_union,mem_insert]
      constructor
      · rintro (hv | hv)
        · exact Or.inr hv
        · by_cases hvu : v = u
          · exact Or.inl hvu
          · exact Or.inr (hTS (mem_erase.mpr ⟨hvu,hv⟩))
      · rintro (rfl | hv)
        · exact Or.inr huC
        · exact Or.inl hv
    rw [hcover]
    exact TetrahedralGrowth.attach h u huS T hTcard hTS hTcl hA

def tetrahedronGraph (F : Finset (Finset V)) : SimpleGraph {C : Finset V // C ∈ F} where
  Adj C D := C ≠ D ∧ 3 ≤ (C.1 ∩ D.1).card
  symm := ⟨fun C D h => ⟨Ne.symm h.1,by simpa only [inter_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Every nonempty triangle-connected family of tetrahedra has a growth
ordering on its entire vertex union. The finite maximum argument closes under
every neighboring tetrahedron, so this includes all members of the component. -/
theorem tetrahedralGrowth_of_connected_family (G : SimpleGraph V)
    (F : Finset (Finset V)) (hne : F.Nonempty)
    (hcl : ∀ C ∈ F, C.card = 4 ∧ G.IsClique C)
    (hconn : (tetrahedronGraph F).Preconnected) :
    TetrahedralGrowth G (F.biUnion id) := by
  classical
  obtain ⟨C₀,hC₀⟩ := hne
  let S := F.biUnion id
  have hCS : ∀ C ∈ F, C ⊆ S := by
    intro C hC v hv
    exact mem_biUnion.mpr ⟨C,hC,hv⟩
  let candidates : Finset (Finset V) := univ.filter
    (fun U => C₀ ⊆ U ∧ U ⊆ S ∧ TetrahedralGrowth G U)
  have hbase : C₀ ∈ candidates := by
    apply mem_filter.mpr
    exact ⟨mem_univ _,Subset.rfl,hCS C₀ hC₀,
      TetrahedralGrowth.base C₀ (hcl C₀ hC₀).1 (hcl C₀ hC₀).2⟩
  obtain ⟨U,hU,hmax⟩ := candidates.exists_max_image Finset.card ⟨C₀,hbase⟩
  obtain ⟨hC₀U,hUS,hgrowth⟩ := (mem_filter.mp hU).2
  have hclosed : ∀ C ∈ F, 3 ≤ (C ∩ U).card → C ⊆ U := by
    intro C hC hover
    have hg := hgrowth.extend_fourClique C (hcl C hC).1 (hcl C hC).2 hover
    have hcand : U ∪ C ∈ candidates := by
      apply mem_filter.mpr
      refine ⟨mem_univ _,hC₀U.trans subset_union_left,?_,hg⟩
      exact union_subset hUS (hCS C hC)
    have he : U ∪ C = U :=
      (eq_of_subset_of_card_le subset_union_left (hmax _ hcand)).symm
    intro v hv
    rw [← he]
    exact mem_union_right U hv
  have hall : ∀ C : {C : Finset V // C ∈ F}, C.1 ⊆ U := by
    intro C
    have hp := (SimpleGraph.reachable_iff_reflTransGen
      (G := tetrahedronGraph F) ⟨C₀,hC₀⟩ C).mp (hconn _ _)
    induction hp with
    | refl => exact hC₀U
    | @tail D E hp hDE ih =>
      apply hclosed E.1 E.2
      refine hDE.2.trans (card_le_card ?_)
      intro v hv
      exact mem_inter.mpr ⟨(mem_inter.mp hv).2,ih (mem_inter.mp hv).1⟩
  have hSU : S ⊆ U := by
    intro v hv
    obtain ⟨C,hC,hvC⟩ := mem_biUnion.mp hv
    exact hall ⟨C,hC⟩ hvC
  have he : U = S := subset_antisymm hUS hSU
  simpa only [he,S] using hgrowth

theorem inducedOn_clique {G : SimpleGraph V} {S : Finset V}
    (hcl : G.IsClique S) : inducedOn G S = cliqueGraph S := by
  ext u v
  constructor
  · intro h
    exact ⟨G.ne_of_adj h.1,h.2⟩
  · rintro ⟨hne,hu,hv⟩
    exact ⟨hcl hu hv hne,hu,hv⟩

theorem edgeFamily_cliqueGraph (S : Finset V) :
    edgeFamily (cliqueGraph S) = S.powersetCard 2 := by
  classical
  ext C
  rw [mem_edgeFamily,mem_powersetCard]
  constructor
  · rintro ⟨hc,hcl⟩
    refine ⟨?_,hc⟩
    obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hc
    have h := hcl u (by simp) v (by simp) huv
    exact insert_subset h.2.1 (singleton_subset_iff.mpr h.2.2)
  · rintro ⟨hsub,hc⟩
    exact ⟨hc,fun u hu v hv huv => ⟨huv,hsub hu,hsub hv⟩⟩

def earlierNeighbors (G : SimpleGraph V) (S : Finset V) (u : V) : Finset V := by
  classical
  exact S.filter (G.Adj u)

@[simp] theorem mem_earlierNeighbors (G : SimpleGraph V) (S : Finset V) (u v : V) :
    v ∈ earlierNeighbors G S u ↔ v ∈ S ∧ G.Adj u v := by
  classical
  simp [earlierNeighbors]

def addedPairs (G : SimpleGraph V) (S : Finset V) (u : V) : Finset (Finset V) :=
  (earlierNeighbors G S u).image (fun v => {u,v})

theorem addedPairs_card (G : SimpleGraph V) (S : Finset V) (u : V) :
    (addedPairs G S u).card = (earlierNeighbors G S u).card := by
  apply card_image_of_injOn
  intro v hv w hw he
  have huv := G.ne_of_adj ((mem_earlierNeighbors G S u v).mp hv).2
  change ({u,v} : Finset V)=({u,w} : Finset V) at he
  have hmem : v ∈ ({u,w} : Finset V) := by rw [← he]; simp
  rcases mem_insert.mp hmem with h | h
  · exact False.elim (huv h.symm)
  · exact mem_singleton.mp h

theorem edgeFamily_inducedOn_insert (G : SimpleGraph V) (S : Finset V) (u : V)
    (hu : u ∉ S) :
    edgeFamily (inducedOn G (insert u S)) = edgeFamily (inducedOn G S) ∪ addedPairs G S u := by
  classical
  ext C
  rw [mem_union]
  constructor
  · intro hC
    obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ C).mp hC
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
    have h := hcl a (by simp) b (by simp) hab
    change G.Adj a b ∧ a ∈ insert u S ∧ b ∈ insert u S at h
    by_cases hau : a = u
    · subst a
      have hbS : b ∈ S := (mem_insert.mp h.2.2).resolve_left (Ne.symm hab)
      exact Or.inr (mem_image.mpr ⟨b,(mem_earlierNeighbors G S u b).mpr ⟨hbS,h.1⟩,rfl⟩)
    · by_cases hbu : b = u
      · subst b
        have haS : a ∈ S := (mem_insert.mp h.2.1).resolve_left hau
        exact Or.inr (mem_image.mpr ⟨a,(mem_earlierNeighbors G S u a).mpr
          ⟨haS,G.adj_symm h.1⟩,pair_comm u a⟩)
      · apply Or.inl
        apply (pair_mem_edgeFamily _ hab).mpr
        exact ⟨h.1,(mem_insert.mp h.2.1).resolve_left hau,
          (mem_insert.mp h.2.2).resolve_left hbu⟩
  · rintro (hC | hC)
    · obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ C).mp hC
      apply (mem_edgeFamily _ C).mpr
      refine ⟨hc,?_⟩
      intro a ha b hb hab
      have h := hcl a ha b hb hab
      exact ⟨h.1,mem_insert_of_mem h.2.1,mem_insert_of_mem h.2.2⟩
    · obtain ⟨v,hv,rfl⟩ := mem_image.mp hC
      obtain ⟨hvS,huv⟩ := (mem_earlierNeighbors G S u v).mp hv
      exact (pair_mem_edgeFamily _ (G.ne_of_adj huv)).mpr
        ⟨huv,mem_insert_self _ _,mem_insert_of_mem hvS⟩

theorem edgeFamily_addedPairs_disjoint (G : SimpleGraph V) (S : Finset V) (u : V)
    (hu : u ∉ S) : Disjoint (edgeFamily (inducedOn G S)) (addedPairs G S u) := by
  classical
  rw [Finset.disjoint_left]
  intro C hC hnew
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hnew
  have huv := G.ne_of_adj ((mem_earlierNeighbors G S u v).mp hv).2
  have h := (pair_mem_edgeFamily _ huv).mp hC
  exact hu h.2.1

theorem induced_edge_count_insert (G : SimpleGraph V) (S : Finset V) (u : V)
    (hu : u ∉ S) :
    (edgeFamily (inducedOn G (insert u S))).card =
      (edgeFamily (inducedOn G S)).card + (earlierNeighbors G S u).card := by
  rw [edgeFamily_inducedOn_insert G S u hu,
    card_union_of_disjoint (edgeFamily_addedPairs_disjoint G S u hu),addedPairs_card]

theorem inducedOn_insert_eq_attach (G : SimpleGraph V) (S T : Finset V) (u : V)
    (hu : u ∉ S) (hT : earlierNeighbors G S u = T) :
    inducedOn G (insert u S) = inducedOn G S ⊔ attachmentStar u T := by
  ext v w
  change (G.Adj v w ∧ v ∈ insert u S ∧ w ∈ insert u S) ↔
    (G.Adj v w ∧ v ∈ S ∧ w ∈ S) ∨
      (v ≠ w ∧ ((v = u ∧ w ∈ T) ∨ (w = u ∧ v ∈ T)))
  rw [← hT]
  simp only [mem_earlierNeighbors,mem_insert]
  constructor
  · rintro ⟨hvw,hv,hw⟩
    have hvwne := G.ne_of_adj hvw
    rcases hv with rfl | hv
    · exact Or.inr ⟨hvwne,Or.inl ⟨rfl,hw.resolve_left (Ne.symm hvwne),hvw⟩⟩
    · rcases hw with rfl | hw
      · exact Or.inr ⟨hvwne,Or.inr ⟨rfl,hv,G.adj_symm hvw⟩⟩
      · exact Or.inl ⟨hvw,hv,hw⟩
  · rintro (⟨hvw,hv,hw⟩ | ⟨hne,(⟨rfl,hw,huw⟩ | ⟨rfl,hv,huv⟩)⟩)
    · exact ⟨hvw,Or.inr hv,Or.inr hw⟩
    · exact ⟨huw,Or.inl rfl,Or.inr hw⟩
    · exact ⟨G.adj_symm huv,Or.inr hv,Or.inl rfl⟩

/-- The complete combinatorial counting step of Theorem4.1, including the
necessary 3-tree equality condition. It applies to arbitrary ambient graphs,
with no K5-free assumption and no bound on the number of vertices. -/
theorem TetrahedralGrowth.edge_bound_and_equality {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) :
    3*S.card-6 ≤ (edgeFamily (inducedOn G S)).card ∧
      ((edgeFamily (inducedOn G S)).card = 3*S.card-6 →
        ThreeTreeOn S (inducedOn G S)) := by
  classical
  induction h with
  | base C hc hcl =>
    rw [inducedOn_clique hcl]
    have he : (edgeFamily (cliqueGraph C)).card = 6 := by
      rw [edgeFamily_cliqueGraph,card_powersetCard,hc]
      decide
    refine ⟨?_,?_⟩
    · omega
    · intro _
      exact ThreeTreeOn.tetrahedron C hc
  | @attach S h u hu T hT hsub hcl hadj ih =>
    have hS := h.card_ge_four
    have hTN : T ⊆ earlierNeighbors G S u := by
      intro v hv
      exact (mem_earlierNeighbors G S u v).mpr ⟨hsub hv,hadj v hv⟩
    have hN : 3 ≤ (earlierNeighbors G S u).card := by
      simpa only [hT] using card_le_card hTN
    rw [card_insert_of_notMem hu,induced_edge_count_insert G S u hu]
    refine ⟨by omega,?_⟩
    intro he
    have hprev : (edgeFamily (inducedOn G S)).card = 3*S.card-6 := by omega
    have hNcard : (earlierNeighbors G S u).card = 3 := by omega
    have hNT : earlierNeighbors G S u = T :=
      (eq_of_subset_of_card_le hTN (by omega)).symm
    rw [inducedOn_insert_eq_attach G S T u hu hNT]
    apply ThreeTreeOn.attach (ih.2 hprev) u hu T hT hsub
    intro v hv w hw hvw
    exact ⟨hcl hv hw hvw,hsub hv,hsub hw⟩

@[simp] theorem inducedOn_univ (G : SimpleGraph V) : inducedOn G univ = G := by
  ext u v
  simp [inducedOn]

theorem edge_bound_of_connected_tetrahedra (G : SimpleGraph V)
    (F : Finset (Finset V)) (hne : F.Nonempty)
    (hcl : ∀ C ∈ F, C.card = 4 ∧ G.IsClique C)
    (hconn : (tetrahedronGraph F).Preconnected) (hcover : F.biUnion id = univ) :
    3*Fintype.card V-6 ≤ (edgeFamily G).card ∧
      ((edgeFamily G).card = 3*Fintype.card V-6 → IsThreeTree G) := by
  have hgrowth := tetrahedralGrowth_of_connected_family G F hne hcl hconn
  rw [hcover] at hgrowth
  simpa [IsThreeTree] using hgrowth.edge_bound_and_equality

end GraphicalZonotopes
