module
prelude

public import RawBoundaryMatch

@[expose] public section

/-!
# Small exact checks for graph-growth frames

The data producer records only vertex and cell maps. Every inverse law,
complete relabeled face family, and graph bit is checked in Lean. No
compatibility matrix or stored permutation of all 1,024 masks is needed.
-/

namespace Papers.RationalityTen.RawGraphGrowthFrames

open GrowthRenaming RawBoundaryMatch ConcreteGrowth

def packedCellMap {n : Nat} (hn : 0 < n) (width code : Nat) (a : Fin n) : Fin n :=
  ⟨((code >>> (width * a.val)) % 2 ^ width) % n, Nat.mod_lt _ hn⟩

def inverseCheckAt {n : Nat} (forward inverse : Fin n → Fin n) (a : Fin n) : Bool :=
  decide (inverse (forward a) = a) && decide (forward (inverse a) = a)

def checkedCellBijection {n : Nat} (forward inverse : Fin n → Fin n)
    (h : ∀ a, inverseCheckAt forward inverse a = true) : Bijection (Fin n) where
  forward := forward
  inverse := inverse
  left_inverse a := of_decide_eq_true (Bool.and_eq_true_iff.mp (h a)).1
  right_inverse a := of_decide_eq_true (Bool.and_eq_true_iff.mp (h a)).2

/-- Complete equality of the decoded cell record, with list order ignored
only for its two face families. Canonical edge ordering is checked separately
by the existing `WellFormed` predicate. -/
def cellRelabelCheck (vertices : Fin 10 → Fin 10) (A B : Cell) : Bool :=
  ((decide (B.kind = A.kind) &&
      decide (B.vertices = renameMask vertices A.vertices)) &&
    sameSetCheck (A.edges.map (renameMask vertices)) B.edges) &&
    sameSetCheck (A.ridgeMasks.map (renameMask vertices)) B.ridgeMasks

theorem cellRelabelCheck_sound (vertices : Fin 10 → Fin 10) (A B : Cell)
    (h : cellRelabelCheck vertices A B = true) :
    B.kind = A.kind ∧ B.vertices = renameMask vertices A.vertices ∧
      (∀ m, m ∈ A.edges.map (renameMask vertices) ↔ m ∈ B.edges) ∧
      (∀ m, m ∈ A.ridgeMasks.map (renameMask vertices) ↔ m ∈ B.ridgeMasks) := by
  obtain ⟨hhead, hridges⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hvalues, hedges⟩ := Bool.and_eq_true_iff.mp hhead
  obtain ⟨hkind, hvertices⟩ := Bool.and_eq_true_iff.mp hvalues
  exact ⟨of_decide_eq_true hkind, of_decide_eq_true hvertices,
    sameSetCheck_sound _ _ hedges, sameSetCheck_sound _ _ hridges⟩

def graphCheckAt (required : Nat) (vertices : Fin 10 → Fin 10) (q : Fin 45) : Bool :=
  decide (required.testBit
    (TenGraphEdges.encode (vertices (TenGraphEdges.first q))
      (vertices (TenGraphEdges.second q))).val = required.testBit q.val)

#print axioms checkedCellBijection
#print axioms cellRelabelCheck_sound

end Papers.RationalityTen.RawGraphGrowthFrames
