module

public import Papers.GraphicalZonotopes.ThreeTreeCliques
public import Papers.GraphicalZonotopes.CliqueComponents
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def triangles (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact univ.filter (fun T => T.card=3 ∧ G.IsClique T)

theorem mem_triangles {G : SimpleGraph V} {T : Finset V} :
    T∈triangles G ↔ T.card=3 ∧ G.IsClique T := by
  classical
  simp [triangles]

/-- Every triangle of an ordinary 3-tree lies in an actual tetrahedron;
the statement includes triangles created at the last attachment. -/
theorem ThreeTreeOn.triangle_extends {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {T : Finset V} (hT : T.card=3) (hcT : G.IsClique T) :
    ∃ C∈tetrahedra G,T⊆C := by
  classical
  induction h generalizing T with
  | tetrahedron C hC =>
    refine ⟨C,?_,?_⟩
    · rw [tetrahedra_cliqueGraph hC]
      exact mem_singleton_self _
    · exact (ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcT
  | @attach S G h u hu A hA hAS hcA ih =>
    rw [tetrahedra_after_attachment h hu hA hAS hcA]
    by_cases huT : u∈T
    · refine ⟨insert u A,mem_insert_self _ _,?_⟩
      intro v hv
      by_cases hvu : v=u
      · exact mem_insert.mpr (Or.inl hvu)
      · exact mem_insert.mpr (Or.inr
          ((attached_vertex_adj_iff h hu hAS v).mp (hcT huT hv (Ne.symm hvu))))
    · obtain ⟨C,hC,hTC⟩ := ih hT (clique_before_attachment huT hcT)
      exact ⟨C,mem_insert_of_mem hC,hTC⟩

theorem ThreeTreeOn.tetrahedra_nonempty {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (tetrahedra G).Nonempty := by
  classical
  induction h with
  | tetrahedron C hC => rw [tetrahedra_cliqueGraph hC]; exact singleton_nonempty _
  | @attach S G h u hu T hT hTS hcT ih =>
    rw [tetrahedra_after_attachment h hu hT hTS hcT]
    exact insert_nonempty _ _

theorem tetrahedronAdjacency_mono {G H : SimpleGraph V} (h : G≤H) :
    TriangleComponents.cliqueGraph G≤TriangleComponents.cliqueGraph H := by
  intro C D hCD
  exact ⟨hCD.1,hCD.2.1,
    fun u hu v hv huv => h (hCD.2.2.1 hu hv huv),
    fun u hu v hv huv => h (hCD.2.2.2.1 hu hv huv),hCD.2.2.2.2⟩

/-- All actual tetrahedra of a 3-tree are joined by shared triangles. This
is a statement about the graph itself, independent of a chosen coefficient
vector or an extreme-ray assumption. -/
theorem ThreeTreeOn.tetrahedra_reachable {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {C D : Finset V}
    (hC : C∈tetrahedra G) (hD : D∈tetrahedra G) :
    (TriangleComponents.cliqueGraph G).Reachable C D := by
  classical
  induction h generalizing C D with
  | tetrahedron A hA =>
    rw [tetrahedra_cliqueGraph hA,mem_singleton] at hC hD
    subst C
    subst D
    exact SimpleGraph.Reachable.rfl
  | @attach S G h u hu T hT hTS hcT ih =>
    have hm := tetrahedronAdjacency_mono
      (show G≤G⊔attachmentStar u T from le_sup_left)
    obtain ⟨K,hK,hTK⟩ := h.triangle_extends hT hcT
    have hk := (mem_filter.mp hK).2
    have huT : u∉T := fun huT => hu (hTS huT)
    have hnew : (TriangleComponents.cliqueGraph (G⊔attachmentStar u T)).Reachable
        (insert u T) K :=
      TriangleComponents.reachable_of_shared_triangle
        (by rw [card_insert_of_notMem huT,hT]) hk.1
        (attached_tetrahedron_clique h hu hTS hcT)
        (fun a ha b hb hab => Or.inl (hk.2 ha hb hab)) hT (subset_insert _ _) hTK
    rw [tetrahedra_after_attachment h hu hT hTS hcT] at hC hD
    rcases mem_insert.mp hC with rfl | hC
    · rcases mem_insert.mp hD with rfl | hD
      · exact SimpleGraph.Reachable.rfl
      · exact hnew.trans (SimpleGraph.Reachable.mono hm (ih hK hD))
    · rcases mem_insert.mp hD with rfl | hD
      · exact (hnew.trans (SimpleGraph.Reachable.mono hm (ih hK hC))).symm
      · exact SimpleGraph.Reachable.mono hm (ih hC hD)

abbrev CliqueTriangleNode (G : SimpleGraph V) := ↥(tetrahedra G) ⊕ ↥(triangles G)

/-- The literal bipartite clique-triangle incidence graph used to root the
construction in Section 6. Its nodes are all tetrahedra and all triangles,
and its edges express containment. -/
def cliqueTriangleIncidence (G : SimpleGraph V) : SimpleGraph (CliqueTriangleNode G) where
  Adj x y := match x,y with
    | Sum.inl C,Sum.inr T => T.1⊆C.1
    | Sum.inr T,Sum.inl C => T.1⊆C.1
    | _,_ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

instance (G : SimpleGraph V) : DecidableRel (cliqueTriangleIncidence G).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp [cliqueTriangleIncidence] <;> infer_instance

/-- A shared triangle gives the actual length-two incidence path. -/
theorem incidence_reachable_of_shared_triangle {G : SimpleGraph V}
    (C D : ↥(tetrahedra G)) (hCD : (TriangleComponents.cliqueGraph G).Adj C.1 D.1) :
    (cliqueTriangleIncidence G).Reachable (Sum.inl C) (Sum.inl D) := by
  classical
  obtain ⟨T,hTsub,hTcard⟩ := exists_subset_card_eq hCD.2.2.2.2.2
  have hTC : T⊆C.1 := hTsub.trans inter_subset_left
  have hTD : T⊆D.1 := hTsub.trans inter_subset_right
  have hT : T∈triangles G := mem_triangles.mpr
    ⟨hTcard,fun u hu v hv huv => hCD.2.2.1 (hTC hu) (hTC hv) huv⟩
  exact (SimpleGraph.Adj.reachable
    (show (cliqueTriangleIncidence G).Adj (Sum.inl C) (Sum.inr ⟨T,hT⟩) from hTC)).trans
      (SimpleGraph.Adj.reachable
        (show (cliqueTriangleIncidence G).Adj (Sum.inr ⟨T,hT⟩) (Sum.inl D) from hTD))

theorem incidence_reachable_of_tetrahedron_reachable {G : SimpleGraph V}
    (C D : ↥(tetrahedra G))
    (hp : (TriangleComponents.cliqueGraph G).Reachable C.1 D.1) :
    (cliqueTriangleIncidence G).Reachable (Sum.inl C) (Sum.inl D) := by
  classical
  rw [SimpleGraph.reachable_eq_reflTransGen] at hp
  have hpath : ∀ E,Relation.ReflTransGen (TriangleComponents.cliqueGraph G).Adj C.1 E →
      ∃ hE : E∈tetrahedra G,
        (cliqueTriangleIncidence G).Reachable (Sum.inl C) (Sum.inl ⟨E,hE⟩) := by
    intro E hE
    induction hE with
    | refl => exact ⟨C.2,SimpleGraph.Reachable.rfl⟩
    | @tail E F hE hEF ih =>
      obtain ⟨hEmem,hreach⟩ := ih
      have hFmem : F∈tetrahedra G := mem_filter.mpr
        ⟨mem_univ _,hEF.2.1,hEF.2.2.2.1⟩
      exact ⟨hFmem,hreach.trans
        (incidence_reachable_of_shared_triangle ⟨E,hEmem⟩ ⟨F,hFmem⟩ hEF)⟩
  obtain ⟨hD,hreach⟩ := hpath _ hp
  exact hreach

theorem ThreeTreeOn.incidence_connected {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (cliqueTriangleIncidence G).Connected := by
  classical
  obtain ⟨C,hC⟩ := h.tetrahedra_nonempty
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inl ⟨C,hC⟩,?_⟩
  intro N
  cases N with
  | inl D =>
    exact incidence_reachable_of_tetrahedron_reachable ⟨C,hC⟩ D
      (h.tetrahedra_reachable hC D.2)
  | inr T =>
    have ht := mem_triangles.mp T.2
    obtain ⟨D,hD,hTD⟩ := h.triangle_extends ht.1 ht.2
    exact (incidence_reachable_of_tetrahedron_reachable ⟨C,hC⟩ ⟨D,hD⟩
      (h.tetrahedra_reachable hC hD)).trans
        (SimpleGraph.Adj.reachable
          (show (cliqueTriangleIncidence G).Adj (Sum.inl ⟨D,hD⟩) (Sum.inr T) from hTD))

end GraphicalZonotopes
