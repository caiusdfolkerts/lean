module
prelude
public import BitsetFamilyCheck
public import FastAdjacentMask

@[expose] public section

namespace Papers.RationalityTen.BitsetAdjacentCellCheck

open ConcreteGrowth

def check (a : Nat) (A B : Cell) : Bool :=
  ((decide (B.kind = A.kind) && decide (B.vertices = FastAdjacentMask.swap a A.vertices)) &&
    BitsetFamilyCheck.check (A.edges.map (FastAdjacentMask.swap a)) B.edges) &&
    BitsetFamilyCheck.check (A.ridgeMasks.map (FastAdjacentMask.swap a)) B.ridgeMasks

theorem check_eq (a : Nat) (A B : Cell) :
    check a A B = RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (FastAdjacentMask.vertexCode a)) A B := by
  simp only [check, BitsetFamilyCheck.check_eq]
  exact FastAdjacentMask.cellRelabelCheck_eq a A B

#print axioms check_eq

end Papers.RationalityTen.BitsetAdjacentCellCheck
