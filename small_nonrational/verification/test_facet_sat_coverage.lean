module
prelude
public import FacetSatCoverage

@[expose] public section

namespace Papers.RationalityTen.FacetSat.Tests

open GrowthDAG SparseGrowthDAG

def oneKind (_ : Fin 3) : Nat := 0
def quota (key : Nat) : Nat := if key = 0 then 2 else 0

example : Boundary.leafCheck oneKind quota [0, 1] = true := by decide
example : Boundary.leafCheck oneKind quota [0] = false := by decide
example : Boundary.leafCheck oneKind quota [0, 0] = false := by decide

example {r : Nat} {relation : Fin 3 → Fin 3 → Bool}
    {ridges : Fin 3 → Fin r → Bool} (S : List (Fin 3))
    (H : Boundary oneKind relation ridges quota S)
    (h0 : (0 : Fin 3) ∈ S) (h1 : (1 : Fin 3) ∈ S) :
    Same (family [0, 1]) (family S) := by
  apply H.same_of_subset_checked [0, 1] (by decide)
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact h0
  · exact List.mem_singleton.mp hc ▸ h1

example {r : Nat} {relation : Fin 3 → Fin 3 → Bool}
    {ridges : Fin 3 → Fin r → Bool} (S : List (Fin 3))
    (H : Boundary oneKind relation ridges quota S)
    (hnot : ¬Same (family [0, 1]) (family S)) :
    (0 : Fin 3) ∈ S → (1 : Fin 3) ∈ S → False := by
  intro h0 h1
  apply H.block_leaf_checked [0, 1] (by decide) hnot
  exact all_mem_cons (fun c => c ∈ S) 0 [1] h0
    (all_mem_cons (fun c => c ∈ S) 1 [] h1 (all_mem_nil _))

end Papers.RationalityTen.FacetSat.Tests
