module

public import Papers.GraphicalZonotopes.BoundaryCapacityStrict
public import Papers.GraphicalZonotopes.CliqueSeparatorCapacity

/-! # Boundary counts are counts in the actual induced graph -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.Separator
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable (G : SimpleGraph V) (B : Finset V)

def inducedBoundaryGraph : SimpleGraph B := G.comap Subtype.val

def inducedContextToBoundary (r : BoundaryContext (inducedBoundaryGraph G B)) : BoundaryRow G B :=
  ⟨⟨⟨(r.1.1.1.1,r.1.1.2.1),r.1.2.1,r.1.2.2⟩,
    ⟨r.2.1.map (Function.Embedding.subtype _),mem_powerset.mpr (by
      intro w hw
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hw
      have h := (mem_commonNeighbors (inducedBoundaryGraph G B) _ _ v).mp
        ((mem_powerset.mp r.2.2) hv)
      exact (mem_commonNeighbors G _ _ _).mpr h)⟩⟩,
    r.1.1.1.2,r.1.1.2.2,by
      intro w hw
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hw
      exact v.2⟩

def boundaryContextToInduced (r : BoundaryRow G B) : BoundaryContext (inducedBoundaryGraph G B) :=
  ⟨⟨(⟨r.1.1.1.1,r.2.1⟩,⟨r.1.1.1.2,r.2.2.1⟩),r.1.1.2.1,r.1.1.2.2⟩,
    ⟨r.1.2.1.subtype (·∈B),mem_powerset.mpr (by
      intro w hw
      have h := (mem_commonNeighbors G _ _ _).mp
        ((mem_powerset.mp r.1.2.2) (mem_subtype.mp hw))
      exact (mem_commonNeighbors (inducedBoundaryGraph G B) _ _ w).mpr h)⟩⟩

def inducedBoundaryContextEquiv : BoundaryContext (inducedBoundaryGraph G B) ≃ BoundaryRow G B where
  toFun := inducedContextToBoundary G B
  invFun := boundaryContextToInduced G B
  left_inv r := by
    rcases r with ⟨⟨⟨u,v⟩,huv,hadj⟩,⟨S,hS⟩⟩
    apply Sigma.ext (by rfl)
    apply heq_of_eq
    apply Subtype.ext
    ext w
    simp [boundaryContextToInduced,inducedContextToBoundary]
  right_inv r := by
    apply Subtype.ext
    apply Sigma.ext (by rfl)
    apply heq_of_eq
    apply Subtype.ext
    exact subtype_map_of_mem r.2.2.2

def inducedBoundaryCliqueEquiv : CliqueIndex (inducedBoundaryGraph G B) ≃ boundaryIndex G B where
  toFun C := ⟨⟨C.1.map (Function.Embedding.subtype _),by
      refine ⟨by simpa only [card_map] using C.2.1,?_⟩
      intro u hu v hv huv
      obtain ⟨u',hu',rfl⟩ := mem_map.mp hu
      obtain ⟨v',hv',rfl⟩ := mem_map.mp hv
      exact C.2.2 hu' hv' (fun h => huv (congrArg Subtype.val h))⟩,by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hw
    exact v.2⟩
  invFun C := ⟨C.1.1.subtype (·∈B),by
    have he := subtype_map_of_mem C.2
    refine ⟨?_,?_⟩
    · have hc := congrArg Finset.card he
      rw [card_map] at hc
      rw [hc]
      exact C.1.2.1
    · intro u hu v hv huv
      exact C.1.2.2 (mem_subtype.mp hu) (mem_subtype.mp hv)
        (fun h => huv (Subtype.ext h))⟩
  left_inv C := by
    apply Subtype.ext
    ext w
    simp
  right_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    exact subtype_map_of_mem C.2

/-- A nonclique boundary has strictly less capacity than the complete
boundary on the same vertex set, with the actual induced rows and cliques. -/
theorem boundary_capacity_lt_of_not_clique (hs : 3≤B.card) (hB : ¬G.IsClique B) :
    Fintype.card (BoundaryRow G B)-(boundaryCliques G B).card+1<cliqueCapacity B.card := by
  have hnot : inducedBoundaryGraph G B≠⊤ := by
    intro he
    apply hB
    intro u hu v hv huv
    have ht : (⊤ : SimpleGraph B).Adj ⟨u,hu⟩ ⟨v,hv⟩ :=
      (SimpleGraph.top_adj _ _).mpr (fun h => huv (congrArg Subtype.val h))
    rw [←he] at ht
    exact ht
  have h := BoundaryCapacity.proper_capacity_lt (inducedBoundaryGraph G B)
    (by simpa only [Fintype.card_coe] using hs) hnot
  rw [Fintype.card_congr (inducedBoundaryContextEquiv G B),
    Fintype.card_congr (inducedBoundaryCliqueEquiv G B),boundaryIndex_card] at h
  have htop : inducedBoundaryGraph (⊤ : SimpleGraph V) B=⊤ := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    simp only [inducedBoundaryGraph,SimpleGraph.comap_adj,SimpleGraph.top_adj]
    exact not_congr Subtype.val_inj
  rw [←htop,Fintype.card_congr (inducedBoundaryContextEquiv (⊤ : SimpleGraph V) B),
    Fintype.card_congr (inducedBoundaryCliqueEquiv (⊤ : SimpleGraph V) B),
    boundaryIndex_card,
    boundaryRow_card_of_clique (G := (⊤ : SimpleGraph V)) (by intro u hu v hv huv; exact huv),
    boundaryCliques_card_of_clique (G := (⊤ : SimpleGraph V)) (by intro u hu v hv huv; exact huv)] at h
  exact Nat.add_lt_add_right h 1

end GraphicalZonotopes.Separator
