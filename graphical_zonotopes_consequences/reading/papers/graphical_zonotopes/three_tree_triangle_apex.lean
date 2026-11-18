module

public import Papers.GraphicalZonotopes.ActiveDeletion
public import Papers.GraphicalZonotopes.PartialThreeTreeGraph

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every component left after deleting a triangle of a 3-tree contains
an apex of a tetrahedron on that triangle. The path is an actual graph path
in the complement of the triangle, rather than a clique-incidence path. -/
theorem ThreeTreeOn.triangle_apex_reachable {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (T : Finset V) (hT : T.card = 3) (hcT : G.IsClique T)
    (x : V) (hxS : x ∈ S) (hxT : x ∉ T) :
    ∃ w, w ∈ S ∧ ∃ hwT : w ∉ T,
      (∀ t ∈ T, G.Adj w t) ∧
      (G.induce ((T : Set V)ᶜ)).Reachable ⟨x,hxT⟩ ⟨w,hwT⟩ := by
  induction h generalizing T x with
  | tetrahedron C hC =>
    have hTC := (ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcT
    refine ⟨x,hxS,hxT,?_,SimpleGraph.Reachable.rfl⟩
    intro t ht
    exact ⟨fun he => hxT (he ▸ ht),hxS,hTC ht⟩
  | @attach S G h u hu A hA hAS hcA ih =>
    by_cases huT : u ∈ T
    · have hTA : T.erase u ⊆ A := by
        intro t ht
        exact (attached_vertex_adj_iff h hu hAS t).mp
          (hcT huT (mem_of_mem_erase ht) (Ne.symm (ne_of_mem_erase ht)))
      have hnot : ¬ A ⊆ T := by
        intro hAT
        have he : A = T := eq_of_subset_of_card_le hAT (by omega)
        exact hu (hAS (he.symm ▸ huT))
      obtain ⟨w,hwA,hwT⟩ := not_subset.mp hnot
      have hxold : x ∈ S := (mem_insert.mp hxS).resolve_left
        (fun he => hxT (he ▸ huT))
      have hxE : x ∉ T.erase u := fun hx => hxT (mem_of_mem_erase hx)
      have hwE : w ∉ T.erase u := fun hw => hwT (mem_of_mem_erase hw)
      let f : activeDelete G S (T.erase u) →g
          (G ⊔ attachmentStar u A).induce ((T : Set V)ᶜ) :=
        { toFun := fun v => ⟨v.1,by
            intro hvT
            exact v.2.2 (mem_erase.mpr
              ⟨fun he => hu (he ▸ v.2.1),hvT⟩)⟩
          map_rel' := fun hab => Or.inl hab }
      have hconn := h.delete_at_most_two_connected (T.erase u)
        (by rw [card_erase_of_mem huT,hT])
      have hp := (hconn.preconnected ⟨x,hxold,hxE⟩ ⟨w,hAS hwA,hwE⟩).map f
      refine ⟨w,mem_insert_of_mem (hAS hwA),hwT,?_,hp⟩
      intro t ht
      by_cases htu : t = u
      · subst t
        exact (G ⊔ attachmentStar u A).adj_symm
          ((attached_vertex_adj_iff h hu hAS w).mpr hwA)
      · exact Or.inl (hcA hwA (hTA (mem_erase.mpr ⟨htu,ht⟩))
          (fun he => hwT (he ▸ ht)))
    · have hcOld : G.IsClique T := clique_before_attachment huT hcT
      have hmono : G.induce ((T : Set V)ᶜ) ≤
          (G ⊔ attachmentStar u A).induce ((T : Set V)ᶜ) :=
        fun _ _ hvw => Or.inl hvw
      by_cases hxu : x = u
      · subst x
        by_cases hAT : A = T
        · refine ⟨u,mem_insert_self _ _,huT,?_,SimpleGraph.Reachable.rfl⟩
          intro t ht
          exact (attached_vertex_adj_iff h hu hAS t).mpr (hAT.symm ▸ ht)
        · have hnot : ¬ A ⊆ T := fun hh => hAT (eq_of_subset_of_card_le hh (by omega))
          obtain ⟨a,haA,haT⟩ := not_subset.mp hnot
          obtain ⟨w,hwS,hwT,hwAdj,hwPath⟩ := ih T hT hcOld a (hAS haA) haT
          refine ⟨w,mem_insert_of_mem hwS,hwT,fun t ht => Or.inl (hwAdj t ht),?_⟩
          have hua : ((G ⊔ attachmentStar u A).induce ((T : Set V)ᶜ)).Adj
              ⟨u,huT⟩ ⟨a,haT⟩ := (attached_vertex_adj_iff h hu hAS a).mpr haA
          exact hua.reachable.trans (hwPath.mono hmono)
      · have hxold : x ∈ S := (mem_insert.mp hxS).resolve_left hxu
        obtain ⟨w,hwS,hwT,hwAdj,hwPath⟩ := ih T hT hcOld x hxold hxT
        exact ⟨w,mem_insert_of_mem hwS,hwT,fun t ht => Or.inl (hwAdj t ht),
          hwPath.mono hmono⟩

/-- A graph-theoretic obstruction forced by a plane drawing: two different
apices over one triangle cannot be joined while avoiding that triangle.
The forbidden configuration consists of a triangle, its six apex spokes,
and an apex-to-apex path, hence is a subdivision of K₅. -/
def TriangleApexSeparated (G : SimpleGraph V) : Prop :=
  ∀ (T : Finset V), T.card = 3 → G.IsClique T →
    ∀ (u w : V) (hu : u ∉ T) (hw : w ∉ T), u ≠ w →
      (∀ t ∈ T, G.Adj u t) → (∀ t ∈ T, G.Adj w t) →
      ¬ (G.induce ((T : Set V)ᶜ)).Reachable ⟨u,hu⟩ ⟨w,hw⟩

theorem TriangleApexSeparated.mono {G H : SimpleGraph V}
    (hH : TriangleApexSeparated H) (hGH : G ≤ H) : TriangleApexSeparated G := by
  intro T hT hcT u w hu hw huw huT hwT hp
  exact hH T hT (fun a ha b hb hab => hGH (hcT ha hb hab)) u w hu hw huw
    (fun t ht => hGH (huT t ht)) (fun t ht => hGH (hwT t ht))
    (hp.mono (fun _ _ hadj => hGH hadj))

theorem TriangleApexSeparated.cliqueFree_five {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) : G.CliqueFree 5 := by
  intro C hC
  obtain ⟨T,hTC,hT⟩ := exists_subset_card_eq (show 3 ≤ C.card by rw [hC.card_eq]; omega)
  have hd : (C \ T).card = 2 := by
    rw [card_sdiff_of_subset hTC,hC.card_eq,hT]
  obtain ⟨u,w,huw,hew⟩ := card_eq_two.mp hd
  have hu : u ∈ C ∧ u ∉ T := mem_sdiff.mp (by rw [hew]; simp)
  have hw : w ∈ C ∧ w ∉ T := mem_sdiff.mp (by rw [hew]; simp)
  apply hG T hT (fun a ha b hb hab => hC.isClique (hTC ha) (hTC hb) hab)
    u w hu.2 hw.2 huw
    (fun t ht => hC.isClique hu.1 (hTC ht) (fun he => hu.2 (he ▸ ht)))
    (fun t ht => hC.isClique hw.1 (hTC ht) (fun he => hw.2 (he ▸ ht)))
  exact SimpleGraph.Adj.reachable (hC.isClique hu.1 hw.1 huw)

/-- Under the actual triangle-apex obstruction, tetrahedral growth never
introduces an extra edge. This is the planar support argument without an
Euler formula or any assumed edge-density inequality. -/
theorem TetrahedralGrowth.induced_threeTree {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hG : TriangleApexSeparated G) :
    ThreeTreeOn S (inducedOn G S) := by
  induction h with
  | base C hc hcl =>
    rw [inducedOn_clique hcl]
    exact ThreeTreeOn.tetrahedron C hc
  | @attach S h u hu T hT hTS hcT hadj ih =>
    have hcOld : (inducedOn G S).IsClique T :=
      fun a ha b hb hab => ⟨hcT ha hb hab,hTS ha,hTS hb⟩
    have hNT : earlierNeighbors G S u = T := by
      apply subset_antisymm
      · intro x hx
        obtain ⟨hxS,hux⟩ := (mem_earlierNeighbors G S u x).mp hx
        by_contra hxT
        obtain ⟨w,hwS,hwT,hwAdj,hwPath⟩ :=
          ih.triangle_apex_reachable T hT hcOld x hxS hxT
        have huT : u ∉ T := fun ht => hu (hTS ht)
        have huw : u ≠ w := fun he => hu (he ▸ hwS)
        apply hG T hT hcT u w huT hwT huw hadj
          (fun t ht => (hwAdj t ht).1)
        have hux' : (G.induce ((T : Set V)ᶜ)).Adj ⟨u,huT⟩ ⟨x,hxT⟩ := hux
        have hmono : (inducedOn G S).induce ((T : Set V)ᶜ) ≤
            G.induce ((T : Set V)ᶜ) := fun _ _ he => he.1
        exact hux'.reachable.trans (hwPath.mono hmono)
      · intro x hx
        exact (mem_earlierNeighbors G S u x).mpr ⟨hTS hx,hadj x hx⟩
    rw [inducedOn_insert_eq_attach G S T u hu hNT]
    exact ThreeTreeOn.attach ih u hu T hT hTS hcOld

theorem TriangleApexSeparated.connected_family_threeTree {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (F : Finset (Finset V)) (hne : F.Nonempty)
    (hcl : ∀ C ∈ F, C.card = 4 ∧ G.IsClique C)
    (hconn : (tetrahedronGraph F).Preconnected) :
    ThreeTreeOn (F.biUnion id) (inducedOn G (F.biUnion id)) :=
  (tetrahedralGrowth_of_connected_family G F hne hcl hconn).induced_threeTree hG

end GraphicalZonotopes
