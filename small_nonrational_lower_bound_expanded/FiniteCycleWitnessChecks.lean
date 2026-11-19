module

public import FiniteCycleIntervals

@[expose] public section

/-!
# Witness-directed finite cycle replay

The producer supplies a candidate index and a permutation index for each
natural code. The kernel checks their required equalities directly. This
avoids searching the whole catalogue inside a decidable existential;
completeness still follows from the exact encoding of every function.
-/

namespace Papers.RationalityTen.FiniteCycleCandidates
open PolygonBoundaryCatalogue

variable {n k c p : ℕ}

def coverageAt (cells : Fin c → Polygon n) (root : Polygon n)
    (f : Fin k → Fin n) (i : Fin c) : Bool :=
  decide (Function.Injective f →
    (cycle f = root ∨ compatible (cycle f) root) → cells i = cycle f)

def neighborAt (cells : Fin c → Polygon n) (neighbors : Finset (Fin c))
    (hn : 3 ≤ n) (perms : Fin p → Fin n → Fin n)
    (f : Fin k → Fin n) (a : Fin p) (i : Fin c) : Bool :=
  decide (Function.Injective f → compatible (cycle f) (triangle n hn) →
    baseEdge n hn ∈ (cycle f).edges →
      i ∈ neighbors ∧ cells i = relabelPolygon (perms a) (cycle f))

theorem covered_of_code_checks (hn : 0 < n) (cells : Fin c → Polygon n)
    (root : Polygon n) (witness : ℕ → Fin c)
    (h : CodeInterval (fun code => coverageAt cells root
      (decodeFunction n hn k code) (witness code)) 0 (n ^ k)) :
    ∀ f : Fin k → Fin n, Covered cells root f := by
  intro f hf heligible
  have hc := of_decide_eq_true
    (h (encodeFunction f) (Nat.zero_le _) (encodeFunction_lt f))
  rw [decodeFunction_encode] at hc
  exact ⟨witness (encodeFunction f), hc hf heligible⟩

theorem neighbor_of_code_checks (hn : 0 < n) (hthree : 3 ≤ n)
    (cells : Fin c → Polygon n) (neighbors : Finset (Fin c))
    (perms : Fin p → Fin n → Fin n) (permutation : ℕ → Fin p) (cell : ℕ → Fin c)
    (h : CodeInterval (fun code => neighborAt cells neighbors hthree perms
      (decodeFunction n hn k code) (permutation code) (cell code)) 0 (n ^ k)) :
    ∀ f : Fin k → Fin n, NeighborWitness cells neighbors hthree perms f := by
  intro f hf hcompat hedge
  have hc := of_decide_eq_true
    (h (encodeFunction f) (Nat.zero_le _) (encodeFunction_lt f))
  rw [decodeFunction_encode] at hc
  exact ⟨permutation (encodeFunction f), cell (encodeFunction f), hc hf hcompat hedge⟩

end Papers.RationalityTen.FiniteCycleCandidates
