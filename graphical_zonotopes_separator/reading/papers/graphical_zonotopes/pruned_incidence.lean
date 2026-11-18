module

public import Papers.GraphicalZonotopes.ThreeTreeIncidenceTree
public import Mathlib.Logic.Embedding.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def internalTriangles (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact (triangles G).filter (fun T => 2≤triangleMultiplicity G T)

theorem mem_internalTriangles {G : SimpleGraph V} {T : Finset V} :
    T∈internalTriangles G ↔ T∈triangles G ∧ 2≤triangleMultiplicity G T := by
  classical
  simp [internalTriangles]

abbrev InternalIncidenceNode (G : SimpleGraph V) :=
  ↥(tetrahedra G) ⊕ ↥(internalTriangles G)

def internalIncidenceEmbedding (G : SimpleGraph V) :
    InternalIncidenceNode G ↪ CliqueTriangleNode G :=
  Function.Embedding.sumMap (Function.Embedding.refl _) {
    toFun := fun T => ⟨T.1,(mem_internalTriangles.mp T.2).1⟩
    inj' := by intro T U he; apply Subtype.ext; simpa only [Subtype.mk.injEq] using he }

/-- The incidence tree with leaf triangles removed. Every remaining
edge carries a nonconstant response, so the local matching property applies
in both directions without a distinguished global root. -/
def internalIncidence (G : SimpleGraph V) : SimpleGraph (InternalIncidenceNode G) :=
  (cliqueTriangleIncidence G).comap (internalIncidenceEmbedding G)

@[simp] theorem internalIncidence_adj_left_right (G : SimpleGraph V)
    (C : ↥(tetrahedra G)) (T : ↥(internalTriangles G)) :
    (internalIncidence G).Adj (Sum.inl C) (Sum.inr T) ↔ T.1⊆C.1 := Iff.rfl

theorem internal_triangle_of_shared {G : SimpleGraph V} {C D T : Finset V}
    (hC : C∈tetrahedra G) (hD : D∈tetrahedra G) (hCD : C≠D)
    (hT : T.card=3) (hTC : T⊆C) (hTD : T⊆D) : T∈internalTriangles G := by
  classical
  have hc := (mem_filter.mp hC).2.2
  apply mem_internalTriangles.mpr
  refine ⟨mem_triangles.mpr ⟨hT,fun u hu v hv huv => hc (hTC hu) (hTC hv) huv⟩,?_⟩
  unfold triangleMultiplicity
  exact Nat.succ_le_of_lt (one_lt_card.mpr
    ⟨C,mem_filter.mpr ⟨hC,hTC⟩,D,mem_filter.mpr ⟨hD,hTD⟩,hCD⟩)

theorem internalIncidence_reachable_of_shared {G : SimpleGraph V}
    (C D : ↥(tetrahedra G))
    (hCD : (TriangleComponents.cliqueGraph G).Adj C.1 D.1) :
    (internalIncidence G).Reachable (Sum.inl C) (Sum.inl D) := by
  classical
  obtain ⟨T,hTsub,hTcard⟩ := exists_subset_card_eq hCD.2.2.2.2.2
  have hTC : T⊆C.1 := hTsub.trans inter_subset_left
  have hTD : T⊆D.1 := hTsub.trans inter_subset_right
  have hT := internal_triangle_of_shared C.2 D.2 hCD.2.2.2.2.1 hTcard hTC hTD
  exact (SimpleGraph.Adj.reachable
    (show (internalIncidence G).Adj (Sum.inl C) (Sum.inr ⟨T,hT⟩) from hTC)).trans
      (SimpleGraph.Adj.reachable
        (show (internalIncidence G).Adj (Sum.inr ⟨T,hT⟩) (Sum.inl D) from hTD))

theorem internalIncidence_reachable_of_tetrahedron_reachable {G : SimpleGraph V}
    (C D : ↥(tetrahedra G))
    (hp : (TriangleComponents.cliqueGraph G).Reachable C.1 D.1) :
    (internalIncidence G).Reachable (Sum.inl C) (Sum.inl D) := by
  classical
  rw [SimpleGraph.reachable_eq_reflTransGen] at hp
  have hpath : ∀ E,Relation.ReflTransGen (TriangleComponents.cliqueGraph G).Adj C.1 E →
      ∃ hE : E∈tetrahedra G,
        (internalIncidence G).Reachable (Sum.inl C) (Sum.inl ⟨E,hE⟩) := by
    intro E hE
    induction hE with
    | refl => exact ⟨C.2,SimpleGraph.Reachable.rfl⟩
    | @tail E F hE hEF ih =>
      obtain ⟨hEmem,hreach⟩ := ih
      have hFmem : F∈tetrahedra G := mem_filter.mpr
        ⟨mem_univ _,hEF.2.1,hEF.2.2.2.1⟩
      exact ⟨hFmem,hreach.trans
        (internalIncidence_reachable_of_shared ⟨E,hEmem⟩ ⟨F,hFmem⟩ hEF)⟩
  obtain ⟨hD,hreach⟩ := hpath _ hp
  exact hreach

theorem ThreeTreeOn.internalIncidence_connected {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (internalIncidence G).Connected := by
  classical
  obtain ⟨C,hC⟩ := h.tetrahedra_nonempty
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inl ⟨C,hC⟩,?_⟩
  intro N
  cases N with
  | inl D =>
    exact internalIncidence_reachable_of_tetrahedron_reachable ⟨C,hC⟩ D
      (h.tetrahedra_reachable hC D.2)
  | inr T =>
    have ht := mem_triangles.mp (mem_internalTriangles.mp T.2).1
    obtain ⟨D,hD,hTD⟩ := h.triangle_extends ht.1 ht.2
    exact (internalIncidence_reachable_of_tetrahedron_reachable ⟨C,hC⟩ ⟨D,hD⟩
      (h.tetrahedra_reachable hC hD)).trans
        (SimpleGraph.Adj.reachable
          (show (internalIncidence G).Adj (Sum.inl ⟨D,hD⟩) (Sum.inr T) from hTD))

theorem ThreeTreeOn.internalIncidence_isTree {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (internalIncidence G).IsTree := by
  exact ⟨h.internalIncidence_connected,
    h.incidence_isTree.isAcyclic.of_comap (internalIncidenceEmbedding G)⟩

end GraphicalZonotopes
