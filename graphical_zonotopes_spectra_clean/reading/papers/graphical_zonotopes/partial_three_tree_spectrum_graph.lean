module

public import Papers.GraphicalZonotopes.PartialThreeTreeSupport
public import Papers.GraphicalZonotopes.ThreeTreeSharedEdges
public import Papers.GraphicalZonotopes.TetrahedralCardinality

/-! # Admissible clique collections in partial 3-trees

The collections below consist of actual tetrahedra, connected by shared
triangles. Their multiplicity condition is imposed on the selected collection,
not on all tetrahedra of the ambient graph.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Admissible.mono {G H : SimpleGraph V} (hH : Admissible H) (hGH : G ≤ H) :
    Admissible G := by
  intro T hT hc
  exact (triangleMultiplicity_mono hGH T).trans
    (hH T hT (fun u hu v hv huv => hGH (hc hu hv huv)))

/-- Construction prefixes can have any requested size, and remain genuine
subgraphs of the final 3-tree. -/
theorem ThreeTreeOn.prefix {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {m : ℕ} (hm : 4 ≤ m) (hmS : m ≤ S.card) :
    ∃ T : Finset V, ∃ H : SimpleGraph V,
      T ⊆ S ∧ T.card = m ∧ H ≤ G ∧ ThreeTreeOn T H := by
  induction h generalizing m with
  | tetrahedron C hC =>
    have he : m = 4 := by omega
    exact ⟨C,cliqueGraph C,Subset.rfl,by omega,le_rfl,ThreeTreeOn.tetrahedron C hC⟩
  | @attach S G h u hu A hA hAS hcA ih =>
    by_cases hmold : m ≤ S.card
    · obtain ⟨T,H,hTS,hT,hHG,hH⟩ := ih hm hmold
      exact ⟨T,H,hTS.trans (subset_insert _ _),hT,hHG.trans le_sup_left,hH⟩
    · have he : (insert u S).card = m := by
        rw [card_insert_of_notMem hu] at hmS ⊢
        omega
      exact ⟨insert u S,G ⊔ attachmentStar u A,Subset.rfl,he,le_rfl,
        ThreeTreeOn.attach h u hu A hA hAS hcA⟩

theorem ThreeTreeOn.tetrahedronGraph_preconnected {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (tetrahedronGraph (tetrahedra G)).Preconnected := by
  intro C D
  have hp := h.tetrahedra_reachable C.2 D.2
  rw [SimpleGraph.reachable_eq_reflTransGen] at hp
  have hh : ∀ E, Relation.ReflTransGen (TriangleComponents.cliqueGraph G).Adj C.1 E →
      ∃ hE : E ∈ tetrahedra G,
        (tetrahedronGraph (tetrahedra G)).Reachable C ⟨E,hE⟩ := by
    intro E hE
    induction hE with
    | refl => exact ⟨C.2,SimpleGraph.Reachable.rfl⟩
    | @tail E F hE hEF ih =>
      obtain ⟨hEmem,hreach⟩ := ih
      have hFmem : F ∈ tetrahedra G := mem_filter.mpr
        ⟨mem_univ _,hEF.2.1,hEF.2.2.2.1⟩
      refine ⟨hFmem,hreach.trans (SimpleGraph.Adj.reachable ?_)⟩
      exact ⟨fun he => hEF.2.2.2.2.1 (congrArg Subtype.val he),hEF.2.2.2.2.2⟩
  obtain ⟨hD,hreach⟩ := hh _ hp
  exact hreach

structure IsAdmissibleCliqueCollection (G : SimpleGraph V)
    (F : Finset (Finset V)) : Prop where
  nonempty : F.Nonempty
  included : F ⊆ tetrahedra G
  connected : (tetrahedronGraph F).Preconnected
  thin : ∀ T : Finset V, T.card = 3 → (F.filter (fun C => T ⊆ C)).card ≤ 3

theorem admissibleCliqueCollection_singleton {G : SimpleGraph V} {C : Finset V}
    (hC : C ∈ tetrahedra G) : IsAdmissibleCliqueCollection G {C} := by
  refine ⟨singleton_nonempty _,singleton_subset_iff.mpr hC,?_,?_⟩
  · intro A B
    have he : A = B := by
      apply Subtype.ext
      exact (mem_singleton.mp A.2).trans (mem_singleton.mp B.2).symm
    subst B
    exact SimpleGraph.Reachable.rfl
  · intro T hT
    have hc := card_filter_le (s := ({C} : Finset (Finset V))) (p := fun D => T ⊆ D)
    simp only [card_singleton] at hc
    omega

theorem ThreeTreeOn.admissibleCliqueCollection {S : Finset V} {H G : SimpleGraph V}
    (h : ThreeTreeOn S H) (hA : Admissible H) (hHG : H ≤ G) :
    IsAdmissibleCliqueCollection G (tetrahedra H) := by
  refine ⟨h.tetrahedra_nonempty,tetrahedra_mono hHG,h.tetrahedronGraph_preconnected,?_⟩
  intro T hT
  by_cases hc : H.IsClique T
  · exact hA T hT hc
  · have he : (tetrahedra H).filter (fun C => T ⊆ C) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro C hC
      obtain ⟨hC,hTC⟩ := mem_filter.mp hC
      have hcl := (mem_filter.mp hC).2.2
      exact hc (fun u hu v hv huv => hcl (hTC hu) (hTC hv) huv)
    rw [he,card_empty]
    omega

theorem IsAdmissibleCliqueCollection.four {G : SimpleGraph V}
    {F : Finset (Finset V)} (hF : IsAdmissibleCliqueCollection G F) :
    ∀ C ∈ F, C.card = 4 ∧ G.IsClique C := by
  intro C hC
  exact (mem_filter.mp (hF.included hC)).2

/-- In a partial 3-tree a connected collection already contains every
tetrahedron induced on its union. There are no hidden extra clique nodes. -/
theorem IsAdmissibleCliqueCollection.induced_structure {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) {F : Finset (Finset V)}
    (hF : IsAdmissibleCliqueCollection G F) :
    ThreeTreeOn (F.biUnion id) (inducedOn G (F.biUnion id)) ∧
      tetrahedra (inducedOn G (F.biUnion id)) = F ∧
      Admissible (inducedOn G (F.biUnion id)) ∧
      (F.biUnion id).card = F.card + 3 := by
  let U := F.biUnion id
  have ht := hG.connected_family_threeTree F hF.nonempty hF.four hF.connected
  have hsub : F ⊆ tetrahedra (inducedOn G U) := by
    intro C hC
    refine mem_filter.mpr ⟨mem_univ _,(hF.four C hC).1,?_⟩
    intro u hu v hv huv
    exact ⟨(hF.four C hC).2 hu hv huv,
      mem_biUnion.mpr ⟨C,hC,hu⟩,mem_biUnion.mpr ⟨C,hC,hv⟩⟩
  have hu := connected_tetrahedra_union_card F hF.nonempty
    (fun C hC => (hF.four C hC).1) hF.connected
  have hfour : 4 ≤ U.card := ht.active_card_ge_four
  have hcard : (tetrahedra (inducedOn G U)).card = U.card - 3 := ht.tetrahedra_card
  have he : tetrahedra (inducedOn G U) = F := by
    apply (eq_of_subset_of_card_le hsub ?_).symm
    rw [hcard]
    change U.card ≤ F.card + 3 at hu
    omega
  refine ⟨ht,he,?_,?_⟩
  · intro T hT hc
    change ((tetrahedra (inducedOn G U)).filter (fun C => T ⊆ C)).card ≤ 3
    rw [he]
    exact hF.thin T hT
  · rw [he] at hcard
    change U.card = F.card + 3
    omega

def admissibleCliqueCollections (G : SimpleGraph V) : Finset (Finset (Finset V)) := by
  classical
  exact univ.filter (IsAdmissibleCliqueCollection G)

/-- The invariant M(G) of Corollaries 6.7 and 6.8. -/
def maximumAdmissibleCliqueCount (G : SimpleGraph V) : ℕ :=
  (admissibleCliqueCollections G).sup Finset.card

theorem admissibleClique_count_le_maximum {G : SimpleGraph V} {F : Finset (Finset V)}
    (hF : IsAdmissibleCliqueCollection G F) : F.card ≤ maximumAdmissibleCliqueCount G := by
  apply le_sup
  exact mem_filter.mpr ⟨mem_univ _,hF⟩

theorem maximumAdmissibleCliqueCount_attained {G : SimpleGraph V}
    (hG : (tetrahedra G).Nonempty) :
    ∃ F : Finset (Finset V), IsAdmissibleCliqueCollection G F ∧
      F.card = maximumAdmissibleCliqueCount G := by
  obtain ⟨C,hC⟩ := hG
  have hne : (admissibleCliqueCollections G).Nonempty :=
    ⟨{C},mem_filter.mpr ⟨mem_univ _,admissibleCliqueCollection_singleton hC⟩⟩
  obtain ⟨F,hF,hmax⟩ := (admissibleCliqueCollections G).exists_max_image Finset.card hne
  have hf := (mem_filter.mp hF).2
  refine ⟨F,hf,le_antisymm (admissibleClique_count_le_maximum hf) ?_⟩
  exact Finset.sup_le_iff.mpr hmax

end GraphicalZonotopes
