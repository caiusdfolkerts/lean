import Schoenflies.Graph.Drawing

open Set Schoenflies

namespace Graph

/-- Five distinct points joined pairwise by simple plane arcs that meet only at
common endpoints.  Ordered pairs give the same arc after reversal.  This is an
actual geometric configuration, including when one arc is a subdivided graph path. -/
structure IsArcK5 (x : Fin 5 → Plane) (P : Fin 5 → Fin 5 → Set Plane) : Prop where
  injective : Function.Injective x
  arc : ∀ i j, i ≠ j → IsArcBetween (P i j) (x i) (x j)
  symm : ∀ i j, P i j = P j i
  vertex : ∀ i j k, i ≠ j → x k ∈ P i j → k = i ∨ k = j
  meet : ∀ i j k l, i ≠ j → k ≠ l →
    (i, j) ≠ (k, l) → (i, j) ≠ (l, k) →
    P i j ∩ P k l ⊆ ({x i, x j} : Set Plane) ∩ ({x k, x l} : Set Plane)

end Graph
