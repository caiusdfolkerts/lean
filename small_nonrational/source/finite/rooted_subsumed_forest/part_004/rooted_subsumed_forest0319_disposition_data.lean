module
prelude
public import RootedSubsumedForest0319Data
public import RawLeafCertificate
public import OldTerminalMatches.M007

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 3
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 6
 (.branch 5
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 2))))
 (.branch 12
 (.leaf (.quota 3))
 (.branch 14
 (.branch 13
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.leaf (.quota 3)))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.leaf (.quota 3))
 (.branch 20
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.branch 23
 (.branch 22
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.branch 29
 (.branch 27
 (.leaf (.quota 2))
 (.branch 28
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 31
 (.leaf (.quota 3))
 (.branch 32
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 37
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 40
 (.branch 39
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 41
 (.leaf (.quota 3))
 (.leaf (.quota 1)))))
 (.branch 46
 (.branch 44
 (.leaf (.quota 2))
 (.branch 45
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 48
 (.branch 47
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0491)))
 (.branch 49
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 60
 (.branch 55
 (.leaf (.quota 1))
 (.branch 57
 (.branch 56
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 58
 (.leaf (.quota 1))
 (.branch 59
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.leaf (.quota 2)))
 (.branch 66
 (.branch 65
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 67
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
