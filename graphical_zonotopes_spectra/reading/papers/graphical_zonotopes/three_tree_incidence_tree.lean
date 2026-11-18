module

public import Papers.GraphicalZonotopes.ThreeTreeIncidence
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triangles_cliqueGraph {C : Finset V} (hC : C.card=4) :
    triangles (cliqueGraph C)=C.powersetCard 3 := by
  classical
  ext T
  rw [mem_triangles,mem_powersetCard]
  constructor
  · rintro ⟨hT,hcl⟩
    exact ⟨(ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcl,hT⟩
  · rintro ⟨hTC,hT⟩
    exact ⟨hT,fun u hu v hv huv => ⟨huv,hTC hu,hTC hv⟩⟩

theorem triangles_after_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {A : Finset V}
    (hA : A.card=3) (hAS : A⊆S) (hcA : G.IsClique A) :
    triangles (G⊔attachmentStar u A)=triangles G∪
      (A.powersetCard 2).image (insert u) := by
  classical
  ext T
  rw [mem_triangles,mem_union,mem_triangles,mem_image]
  constructor
  · rintro ⟨hT,hcl⟩
    by_cases huT : u∈T
    · right
      refine ⟨T.erase u,mem_powersetCard.mpr ⟨?_,?_⟩,insert_erase huT⟩
      · intro v hv
        exact (attached_vertex_adj_iff h hu hAS v).mp
          (hcl huT (mem_of_mem_erase hv) (Ne.symm (ne_of_mem_erase hv)))
      · rw [card_erase_of_mem huT,hT]
    · exact Or.inl ⟨hT,clique_before_attachment huT hcl⟩
  · rintro (⟨hT,hcl⟩ | ⟨B,hB,rfl⟩)
    · exact ⟨hT,fun v hv w hw hvw => Or.inl (hcl hv hw hvw)⟩
    · obtain ⟨hBA,hB⟩ := mem_powersetCard.mp hB
      have huB : u∉B := fun hum => hu (hAS (hBA hum))
      refine ⟨by rw [card_insert_of_notMem huB,hB],?_⟩
      have hcl := attached_tetrahedron_clique h hu hAS hcA
      exact fun v hv w hw hvw => hcl (insert_subset_insert u hBA hv)
        (insert_subset_insert u hBA hw) hvw

theorem triangles_after_attachment_card {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {A : Finset V}
    (hA : A.card=3) (hAS : A⊆S) (hcA : G.IsClique A) :
    (triangles (G⊔attachmentStar u A)).card=(triangles G).card+3 := by
  classical
  have hdis : Disjoint (triangles G) ((A.powersetCard 2).image (insert u)) := by
    apply disjoint_left.mpr
    intro T hT hnew
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hnew
    obtain ⟨hT,hcl⟩ := mem_triangles.mp hT
    exact hu ((h.clique_subset_active (by omega) hcl) (mem_insert_self _ _))
  have himage : ((A.powersetCard 2).image (insert u)).card=(A.powersetCard 2).card := by
    apply card_image_of_injOn
    intro B hB C hC he
    have huB : u∉B := fun hum => hu (hAS ((mem_powersetCard.mp hB).1 hum))
    have huC : u∉C := fun hum => hu (hAS ((mem_powersetCard.mp hC).1 hum))
    have herase := congrArg (fun D : Finset V => D.erase u) he
    simpa [huB,huC] using herase
  rw [triangles_after_attachment h hu hA hAS hcA,card_union_of_disjoint hdis,
    himage,card_powersetCard,hA]
  norm_num

/-- The exact count includes all graph triangles, not a chosen set of
construction separators. -/
theorem ThreeTreeOn.triangles_card {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (triangles G).card=3*(tetrahedra G).card+1 := by
  classical
  induction h with
  | tetrahedron C hC =>
    rw [triangles_cliqueGraph hC,card_powersetCard,hC,
      tetrahedra_cliqueGraph hC,card_singleton]
    norm_num
  | @attach S G h u hu A hA hAS hcA ih =>
    rw [triangles_after_attachment_card h hu hA hAS hcA,
      tetrahedra_after_attachment h hu hA hAS hcA,
      card_insert_of_notMem (attached_tetrahedron_not_old h hu),ih]
    omega

def incidenceCliqueNeighbors (G : SimpleGraph V) (C : ↥(tetrahedra G)) :
    ↥(C.1.powersetCard 3) ≃ (cliqueTriangleIncidence G).neighborSet (Sum.inl C) := by
  classical
  have hc := (mem_filter.mp C.2).2
  let f : ↥(C.1.powersetCard 3) →
      (cliqueTriangleIncidence G).neighborSet (Sum.inl C) := fun T =>
    ⟨Sum.inr ⟨T.1,mem_triangles.mpr
      ⟨(mem_powersetCard.mp T.2).2,fun u hu v hv huv =>
        hc.2 ((mem_powersetCard.mp T.2).1 hu) ((mem_powersetCard.mp T.2).1 hv) huv⟩⟩,
      (mem_powersetCard.mp T.2).1⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro T U he
    apply Subtype.ext
    simpa only [f, Subtype.mk.injEq, Sum.inr.injEq] using he
  · rintro ⟨N,hN⟩
    cases N with
    | inl D => exact False.elim hN
    | inr T =>
      refine ⟨⟨T.1,mem_powersetCard.mpr ⟨hN,(mem_triangles.mp T.2).1⟩⟩,?_⟩
      rfl

theorem incidence_clique_degree (G : SimpleGraph V) (C : ↥(tetrahedra G)) :
    (cliqueTriangleIncidence G).degree (Sum.inl C)=4 := by
  classical
  have hc := (mem_filter.mp C.2).2.1
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← Fintype.card_congr (incidenceCliqueNeighbors G C)]
  simp only [Fintype.card_coe,card_powersetCard,hc]
  norm_num

theorem incidence_edge_card (G : SimpleGraph V) :
    (cliqueTriangleIncidence G).edgeFinset.card=4*(tetrahedra G).card := by
  classical
  let L : Finset (CliqueTriangleNode G) := univ.image Sum.inl
  let R : Finset (CliqueTriangleNode G) := univ.image Sum.inr
  have hb : (cliqueTriangleIncidence G).IsBipartiteWith L R := by
    constructor
    · apply Set.disjoint_left.mpr
      intro N hL hR
      obtain ⟨C,hC,hCN⟩ := mem_image.mp hL
      obtain ⟨T,hT,hTN⟩ := mem_image.mp hR
      have he := hCN.trans hTN.symm
      cases he
    · intro N M hNM
      cases N <;> cases M
      · exact False.elim hNM
      · exact Or.inl ⟨by simp [L],by simp [R]⟩
      · exact Or.inr ⟨by simp [R],by simp [L]⟩
      · exact False.elim hNM
  calc
    (cliqueTriangleIncidence G).edgeFinset.card=
        ∑ N∈L,(cliqueTriangleIncidence G).degree N :=
      (SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hb).symm
    _=∑ C : ↥(tetrahedra G),(4:ℕ) := by
      dsimp [L]
      rw [sum_image (fun C hC D hD hCD => Sum.inl.inj hCD)]
      simp only [incidence_clique_degree]
    _=4*(tetrahedra G).card := by simp [Nat.mul_comm]

/-- The complete literal clique–triangle incidence graph of any 3-tree
is a tree. Connectedness and the exact vertex/edge counts are independently
proved for all actual cliques, so no incidence-tree property is assumed. -/
theorem ThreeTreeOn.incidence_isTree {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (cliqueTriangleIncidence G).IsTree := by
  classical
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨h.incidence_connected,?_⟩
  simp only [Nat.card_eq_fintype_card,CliqueTriangleNode,Fintype.card_sum,Fintype.card_coe]
  rw [← SimpleGraph.edgeFinset_card,incidence_edge_card,h.triangles_card]
  omega

end GraphicalZonotopes
