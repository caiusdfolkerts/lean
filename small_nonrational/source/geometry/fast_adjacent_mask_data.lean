module
prelude
public import RawGraphGrowthFrames
public import FiniteChecks

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FastAdjacentMask
open Papers.RationalityTen ConcreteGrowth FiniteChecks RawBoundaryMatch

def vertexTable : Table Nat :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf 654820258305)
 (.leaf 654820258080))
 (.branch 3
 (.leaf 654820254480)
 (.leaf 654820196880)))
 (.branch 6
 (.branch 5
 (.leaf 654819275280)
 (.leaf 654804529680))
 (.branch 7
 (.leaf 654568600080)
 (.branch 8
 (.leaf 650793726480)
 (.leaf 590395748880)))))
def vertexCode (a : Nat) := vertexTable.get a
def rawSwap (a mask : Nat) : Nat :=
  if mask.testBit a == mask.testBit (a+1) then mask
  else Nat.xor mask (Nat.shiftLeft 3 a)
def test (i : Nat) : Bool :=
  decide (rawSwap (i / 1024) (i % 1024) =
    renameMask (TenGraphEdges.vertexMap (vertexCode (i / 1024))) (i % 1024))
def swap (a mask : Nat) : Nat :=
  if a < 9 ∧ mask < 1024 then rawSwap a mask
  else renameMask (TenGraphEdges.vertexMap (vertexCode a)) mask

end Papers.RationalityTen.FastAdjacentMask
