module
prelude
public import RootedSubsumedForest0321Data
public import RawLeafCertificate
public import OldTerminalMatches.M007

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0321
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 68
 (.branch 34
 (.branch 17
 (.branch 8
 (.leaf (.quota 2))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 11
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 14
 (.leaf (.quota 1))
 (.branch 15
 (.leaf (.quota 2))
 (.leaf (.quota 3))))))
 (.branch 25
 (.branch 21
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 51
 (.branch 42
 (.leaf (.quota 2))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 48
 (.branch 47
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 59
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 54
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 57
 (.leaf (.quota 2))
 (.branch 58
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 63
 (.branch 61
 (.branch 60
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 102
 (.branch 85
 (.branch 76
 (.branch 72
 (.leaf (.quota 2))
 (.branch 74
 (.branch 73
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 80
 (.leaf (.quota 2))
 (.branch 82
 (.leaf (.quota 1))
 (.branch 83
 (.leaf (.quota 1))
 (.branch 84
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0505)))))))
 (.branch 93
 (.leaf (.quota 2))
 (.branch 97
 (.leaf (.quota 2))
 (.branch 99
 (.branch 98
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 100
 (.leaf (.quota 1))
 (.branch 101
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 119
 (.branch 110
 (.branch 106
 (.branch 104
 (.branch 103
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 105
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 114
 (.branch 112
 (.leaf (.quota 2))
 (.branch 113
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 116
 (.leaf (.quota 2))
 (.branch 117
 (.leaf (.quota 2))
 (.branch 118
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 127
 (.leaf (.quota 2))
 (.branch 131
 (.branch 129
 (.leaf (.quota 2))
 (.branch 130
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 133
 (.branch 132
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0321
