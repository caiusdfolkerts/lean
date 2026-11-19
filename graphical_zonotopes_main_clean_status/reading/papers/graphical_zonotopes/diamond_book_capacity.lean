module

public import Papers.GraphicalZonotopes.DiamondBookGraph

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset
open scoped BigOperators
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def boundary (k : ℕ) : Finset (Vertex k):={a k,b k,u k,v k}
def privateVertex (k : ℕ) (j : Fin k) : Vertex k:=⟨j.val+4,by omega⟩
def privatePart (k : ℕ) (j : Fin k) : Finset (Vertex k):={privateVertex k j}

theorem boundary_card (k : ℕ) : (boundary k).card=4 := by
  simp [boundary,a,b,u,v,Fin.ext_iff]

theorem mem_boundary_iff (k : ℕ) (x : Vertex k) : x∈boundary k ↔ x.val<4 := by
  simp only [boundary,mem_insert,mem_singleton,Fin.ext_iff,a,b,u,v]
  omega

theorem privateVertex_injective (k : ℕ) : Function.Injective (privateVertex k) := by
  intro i j hij
  apply Fin.ext
  have hh:=congrArg Fin.val hij
  change i.val+4=j.val+4 at hh
  omega

theorem private_part_value (k : ℕ) (j : Fin k) : part k (privateVertex k j)=3 := by
  simp [part,privateVertex]

theorem partition (k : ℕ) : Separator.Partition (graph k) (boundary k) (privatePart k) where
  boundary_disjoint j:=by
    apply disjoint_left.mpr
    intro x hx hxp
    have he:x=privateVertex k j:=mem_singleton.mp hxp
    rw [he,mem_boundary_iff] at hx
    change j.val+4<4 at hx
    omega
  private_disjoint:=by
    intro i j hij
    exact disjoint_singleton.mpr (fun he => hij (privateVertex_injective k he))
  cover x:=by
    by_cases hx:x.val<4
    · exact Or.inl ((mem_boundary_iff k x).mpr hx)
    · apply Or.inr
      let j : Fin k:=⟨x.val-4,by have:=x.isLt; omega⟩
      refine ⟨j,?_⟩
      apply mem_singleton.mpr
      apply Fin.ext
      change x.val=(x.val-4)+4
      omega
  no_cross_edge:=by
    intro i j x y hx hy hxy
    have hx':x=privateVertex k i:=mem_singleton.mp hx
    have hy':y=privateVertex k j:=mem_singleton.mp hy
    subst x
    subst y
    change part k (privateVertex k i)≠part k (privateVertex k j) at hxy
    rw [private_part_value,private_part_value] at hxy
    exact False.elim (hxy rfl)

theorem boundary_cliques_card (k : ℕ) :
    (Separator.boundaryCliques (graph k) (boundary k)).card=7 := by
  classical
  have hp (x : Vertex k) : ({x} : Finset (Vertex k)).powerset={∅,{x}} := by
    ext S
    simp [Finset.subset_singleton_iff]
  norm_num [Separator.boundaryCliques,boundary,IsCliqueCoordinate,
    SimpleGraph.IsClique,Set.Pairwise,graph,part_a,part_b,part_u,part_v,
    Finset.powerset_insert,hp,Finset.filter_insert,Finset.filter_singleton]
  exact of_decide_eq_true rfl

def boundaryEdges (k : ℕ) : Finset (Vertex k × Vertex k):=
  {(a k,b k),(a k,u k),(a k,v k),(b k,u k),(b k,v k)}

theorem boundary_edge_iff (k : ℕ) (x y : Vertex k) :
    (x<y ∧ (graph k).Adj x y ∧ x∈boundary k ∧ y∈boundary k) ↔
      (x,y)∈boundaryEdges k := by
  constructor
  · rintro ⟨hlt,he,hx,hy⟩
    simp only [boundary,mem_insert,mem_singleton] at hx hy
    rcases hx with rfl|rfl|rfl|rfl <;>
      rcases hy with rfl|rfl|rfl|rfl <;>
      norm_num [boundaryEdges,graph,part,a,b,u,v,Fin.lt_def] at *
  · intro he
    simp only [boundaryEdges,mem_insert,mem_singleton,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      norm_num [boundary,graph,part,a,b,u,v,Fin.lt_def]

def boundaryEdgeEquiv (k : ℕ) :
    Separator.BoundaryEdge (graph k) (boundary k) ≃ ↥(boundaryEdges k) where
  toFun e:=⟨e.1.1,(boundary_edge_iff k _ _).mp ⟨e.1.2.1,e.1.2.2,e.2⟩⟩
  invFun e:=
    let h:=(boundary_edge_iff k e.1.1 e.1.2).mpr e.2
    ⟨⟨e.1,h.1,h.2.1⟩,h.2.2⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem common_boundary_ab (k : ℕ) :
    commonNeighbors (graph k) (a k) (b k)∩boundary k={u k,v k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn,hB⟩:=mem_inter.mp hx
    simp only [boundary,mem_insert,mem_singleton] at hB
    rcases hB with rfl|rfl|rfl|rfl
    all_goals simp_all [mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl
    all_goals apply mem_inter.mpr
    all_goals constructor
    all_goals simp [boundary,mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]

theorem common_boundary_au (k : ℕ) :
    commonNeighbors (graph k) (a k) (u k)∩boundary k={b k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn,hB⟩:=mem_inter.mp hx
    simp only [boundary,mem_insert,mem_singleton] at hB
    rcases hB with rfl|rfl|rfl|rfl
    all_goals simp_all [mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    subst x
    all_goals apply mem_inter.mpr
    all_goals constructor
    all_goals simp [boundary,mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]

theorem common_boundary_av (k : ℕ) :
    commonNeighbors (graph k) (a k) (v k)∩boundary k={b k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn,hB⟩:=mem_inter.mp hx
    simp only [boundary,mem_insert,mem_singleton] at hB
    rcases hB with rfl|rfl|rfl|rfl
    all_goals simp_all [mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    subst x
    all_goals apply mem_inter.mpr
    all_goals constructor
    all_goals simp [boundary,mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]

theorem common_boundary_bu (k : ℕ) :
    commonNeighbors (graph k) (b k) (u k)∩boundary k={a k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn,hB⟩:=mem_inter.mp hx
    simp only [boundary,mem_insert,mem_singleton] at hB
    rcases hB with rfl|rfl|rfl|rfl
    all_goals simp_all [mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    subst x
    all_goals apply mem_inter.mpr
    all_goals constructor
    all_goals simp [boundary,mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]

theorem common_boundary_bv (k : ℕ) :
    commonNeighbors (graph k) (b k) (v k)∩boundary k={a k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn,hB⟩:=mem_inter.mp hx
    simp only [boundary,mem_insert,mem_singleton] at hB
    rcases hB with rfl|rfl|rfl|rfl
    all_goals simp_all [mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    subst x
    all_goals apply mem_inter.mpr
    all_goals constructor
    all_goals simp [boundary,mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]

theorem boundary_rows_count (k : ℕ) :
    (∑ e : Separator.BoundaryEdge (graph k) (boundary k),
      2^(commonNeighbors (graph k) e.1.1.1 e.1.1.2∩boundary k).card)=12 := by
  classical
  have hsum : (∑ e : Separator.BoundaryEdge (graph k) (boundary k),
      2^(commonNeighbors (graph k) e.1.1.1 e.1.1.2∩boundary k).card)=
      ∑ e∈boundaryEdges k,2^(commonNeighbors (graph k) e.1 e.2∩boundary k).card := by
    calc
      _ = ∑ e : ↥(boundaryEdges k),
          (2 : ℕ)^(commonNeighbors (graph k) e.1.1 e.1.2∩boundary k).card :=
        Fintype.sum_equiv (boundaryEdgeEquiv k)
          (fun e : Separator.BoundaryEdge (graph k) (boundary k) =>
            (2 : ℕ)^(commonNeighbors (graph k) e.1.1.1 e.1.1.2∩boundary k).card)
          (fun e : ↥(boundaryEdges k) =>
            (2 : ℕ)^(commonNeighbors (graph k) e.1.1 e.1.2∩boundary k).card)
          (fun _ => rfl)
      _ = _ := sum_coe_sort (boundaryEdges k)
        (fun e : Vertex k × Vertex k =>
          (2 : ℕ)^(commonNeighbors (graph k) e.1 e.2∩boundary k).card)
  rw [hsum]
  simp [boundaryEdges,common_boundary_ab,common_boundary_au,common_boundary_av,
    common_boundary_bu,common_boundary_bv]

/-- The exact diamond separator capacity, independent of the number of
private vertices and allowing every zero private block. -/
theorem active_capacity (k : ℕ) (z : graphicalFunctionSpace (graph k))
    (hz : ExtremeSupermodular z.1) :
    Fintype.card (Gluing.ActiveBranch (((Separator.functionEquiv (partition k)).symm z).2))≤6 := by
  have hb:=Separator.separator_capacity_for_function (partition k) z hz
  rw [boundary_rows_count,boundary_cliques_card] at hb
  exact hb

theorem dimension_le_nine (k : ℕ) (z : graphicalFunctionSpace (graph k))
    (hz : ExtremeSupermodular z.1) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1))≤9 := by
  have hb:=Separator.finrank_le_boundary_add_active (partition k)
    (fun j => by simp [privatePart]) z hz.2.1
  rw [boundary_card] at hb
  have ha:=active_capacity k z hz
  omega

end GraphicalZonotopes.DiamondBook
