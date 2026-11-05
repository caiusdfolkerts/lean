module
prelude
public import SmallSubsumedForest07Data
public import RawLeafCertificate
public import OldTerminalMatches.M000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest07
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 42
 (.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0012))
 (.leaf (.incidence 3)))
 (.leaf (.incidence 3)))
 (.branch 7
 (.branch 6
 (.leaf (.incidence 7))
 (.leaf (.incidence 3)))
 (.leaf (.incidence 3))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (.incidence 3))
 (.leaf (.incidence 5)))
 (.branch 13
 (.leaf (.incidence 3))
 (.branch 14
 (.leaf (.quota 2))
 (.leaf (.incidence 3)))))
 (.branch 18
 (.branch 16
 (.leaf (.incidence 3))
 (.leaf (.incidence 6)))
 (.branch 19
 (.leaf (.incidence 7))
 (.branch 20
 (.leaf (.incidence 7))
 (.leaf (.incidence 5)))))))
 (.branch 31
 (.branch 26
 (.branch 23
 (.leaf (.incidence 5))
 (.branch 24
 (.leaf (.incidence 5))
 (.branch 25
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0013))
 (.leaf (.incidence 6)))))
 (.branch 28
 (.branch 27
 (.leaf (.incidence 5))
 (.leaf (.incidence 8)))
 (.branch 29
 (.leaf (.incidence 6))
 (.branch 30
 (.leaf (.incidence 9))
 (.leaf (.incidence 5))))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf (.incidence 8))
 (.leaf (.incidence 9)))
 (.branch 34
 (.leaf (.incidence 3))
 (.branch 35
 (.leaf (.incidence 5))
 (.leaf (.incidence 3)))))
 (.branch 39
 (.branch 37
 (.leaf (.incidence 5))
 (.branch 38
 (.leaf (.incidence 8))
 (.leaf (.incidence 3))))
 (.branch 40
 (.leaf (.incidence 5))
 (.branch 41
 (.leaf (.incidence 3))
 (.leaf (.incidence 5))))))))
 (.branch 63
 (.branch 52
 (.branch 47
 (.branch 44
 (.branch 43
 (.leaf (.incidence 5))
 (.leaf (.incidence 4)))
 (.leaf (.incidence 4)))
 (.leaf (.incidence 4)))
 (.branch 57
 (.branch 54
 (.leaf (.incidence 4))
 (.branch 55
 (.leaf (.incidence 4))
 (.branch 56
 (.leaf (.incidence 4))
 (.leaf (.incidence 3)))))
 (.branch 60
 (.branch 58
 (.leaf (.incidence 5))
 (.branch 59
 (.leaf (.incidence 8))
 (.leaf (.incidence 6))))
 (.branch 61
 (.leaf (.incidence 8))
 (.branch 62
 (.leaf (.incidence 6))
 (.leaf (.incidence 7)))))))
 (.branch 73
 (.branch 68
 (.branch 65
 (.branch 64
 (.leaf (.incidence 7))
 (.leaf (.incidence 6)))
 (.branch 66
 (.leaf (.incidence 6))
 (.branch 67
 (.leaf (.incidence 5))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0014)))))
 (.branch 70
 (.branch 69
 (.leaf (.incidence 6))
 (.leaf (.incidence 9)))
 (.branch 71
 (.leaf (.incidence 3))
 (.branch 72
 (.leaf (.incidence 3))
 (.leaf (.incidence 4))))))
 (.branch 78
 (.branch 75
 (.leaf (.incidence 4))
 (.branch 76
 (.leaf (.incidence 3))
 (.leaf (.incidence 4))))
 (.branch 81
 (.branch 79
 (.leaf (.incidence 4))
 (.branch 80
 (.leaf (.incidence 3))
 (.leaf (.incidence 4))))
 (.branch 82
 (.leaf (.incidence 3))
 (.branch 83
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest07
