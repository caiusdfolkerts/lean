module
prelude
public import GraphCaseCertificate
public import GraphRouteCasesData

@[expose] public section
namespace Papers.RationalityTen.GraphFiniteDispatch
open GraphCaseCertificate ConcreteGrowth FiniteChecks

/-- A closed interval of the original global compact key table. -/
def Block (lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i → i < hi → Result (GraphRoutes.compactKeys.entry i)

theorem block_of_table (table : Table {key : GraphRouteSelector.Key // Result key})
    (offset count : Nat)
    (h : Interval (fun i => decide ((table.get i).val =
      GraphRoutes.compactKeys.entry (offset + i))) 0 count) :
    Block offset (offset + count) := by
  intro i hlo hhi
  have hj : i - offset < count := by omega
  have hkey := of_decide_eq_true (h (i - offset) (Nat.zero_le _) hj)
  have hsum : offset + (i - offset) = i := by omega
  rw [hsum] at hkey
  exact hkey ▸ (table.get (i - offset)).property

theorem Block.append {lo mid hi : Nat} (h1 : Block lo mid) (h2 : Block mid hi) :
    Block lo hi := by
  intro i hlo hhi
  by_cases hm : i < mid
  · exact h1 i hlo hm
  · exact h2 i (Nat.le_of_not_lt hm) hhi

#print axioms block_of_table
#print axioms Block.append
end Papers.RationalityTen.GraphFiniteDispatch
