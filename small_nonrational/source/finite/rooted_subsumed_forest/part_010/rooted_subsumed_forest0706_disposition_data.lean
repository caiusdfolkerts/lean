module
prelude
public import RootedSubsumedForest0706Data
public import RawLeafCertificate
public import OldTerminalMatches.M019

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0706
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 69
 (.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 3
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 6
 (.branch 5
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 7
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 12
 (.leaf (.quota 2))
 (.branch 14
 (.leaf (.quota 2))
 (.branch 15
 (.leaf (.quota 2))
 (.branch 16
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))))
 (.branch 25
 (.branch 21
 (.leaf (.quota 2))
 (.branch 23
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 28
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 31
 (.branch 30
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))
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
 (.leaf (.quota 2))
 (.branch 49
 (.leaf (.quota 2))
 (.branch 50
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 54
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 64
 (.leaf (.quota 2))
 (.branch 66
 (.leaf (.quota 2))
 (.branch 67
 (.leaf (.quota 2))
 (.branch 68
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 104
 (.branch 86
 (.branch 77
 (.branch 73
 (.branch 71
 (.leaf (.quota 2))
 (.branch 72
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 95
 (.branch 90
 (.branch 88
 (.branch 87
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 99
 (.branch 97
 (.leaf (.quota 2))
 (.branch 98
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1228))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))))
 (.branch 121
 (.leaf (.quota 2))
 (.branch 130
 (.branch 125
 (.branch 123
 (.branch 122
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 127
 (.branch 126
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 128
 (.leaf (.quota 2))
 (.branch 129
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M019.r1229))))))
 (.branch 134
 (.branch 132
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 136
 (.branch 135
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 137
 (.leaf (.quota 2))
 (.branch 138
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0706
