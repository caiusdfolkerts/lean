module

public import FiniteInjectionCodes
public import FiniteCycleWitnessChecks

@[expose] public section

/-! Exact witness replay over the reduced, complete domain of injections. -/

namespace Papers.RationalityTen.FiniteCycleCandidates
open PolygonBoundaryCatalogue

variable {n k c p : ℕ}

theorem covered_of_injection_checks (hk : k ≤ n) (cells : Fin c → Polygon n)
    (root : Polygon n) (witness : ℕ → Fin c)
    (h : CodeInterval (fun code => coverageAt cells root
      (decodeInjection n k hk code) (witness code)) 0 (injectionCount n k)) :
    ∀ f : Fin k → Fin n, Covered cells root f := by
  intro f hf heligible
  obtain ⟨code, hcode, hdecode⟩ := exists_injection_code hk f hf
  have hc := of_decide_eq_true (h code (Nat.zero_le _) hcode)
  rw [hdecode] at hc
  exact ⟨witness code, hc hf heligible⟩

theorem neighbor_of_injection_checks (hk : k ≤ n) (hthree : 3 ≤ n)
    (cells : Fin c → Polygon n) (neighbors : Finset (Fin c))
    (perms : Fin p → Fin n → Fin n) (permutation : ℕ → Fin p) (cell : ℕ → Fin c)
    (h : CodeInterval (fun code => neighborAt cells neighbors hthree perms
      (decodeInjection n k hk code) (permutation code) (cell code)) 0 (injectionCount n k)) :
    ∀ f : Fin k → Fin n, NeighborWitness cells neighbors hthree perms f := by
  intro f hf hcompat hedge
  obtain ⟨code, hcode, hdecode⟩ := exists_injection_code hk f hf
  have hc := of_decide_eq_true (h code (Nat.zero_le _) hcode)
  rw [hdecode] at hc
  exact ⟨permutation code, cell code, hc hf hcompat hedge⟩

end Papers.RationalityTen.FiniteCycleCandidates
