module
prelude
public import RootedSubsumedForest0354Data
public import RawLeafCertificate
public import OldTerminalMatches.M014

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0354
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 78
 (.branch 39
 (.branch 19
 (.branch 9
 (.branch 4
 (.leaf (.quota 3))
 (.branch 6
 (.branch 5
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 14
 (.leaf (.quota 2))
 (.branch 16
 (.branch 15
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0951)))
 (.branch 17
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0952))
 (.leaf (.quota 2))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 22
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0953))
 (.branch 23
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 26
 (.branch 25
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 27
 (.leaf (.quota 2))
 (.branch 28
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.leaf (.quota 2))))
 (.branch 58
 (.branch 48
 (.branch 43
 (.leaf (.quota 2))
 (.branch 45
 (.leaf (.quota 2))
 (.branch 46
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 53
 (.branch 50
 (.leaf (.quota 2))
 (.branch 51
 (.leaf (.quota 2))
 (.branch 52
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 55
 (.leaf (.quota 2))
 (.branch 56
 (.leaf (.quota 2))
 (.branch 57
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))))
 (.branch 68
 (.branch 63
 (.branch 60
 (.leaf (.quota 2))
 (.branch 61
 (.leaf (.quota 2))
 (.branch 62
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 65
 (.branch 64
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 66
 (.leaf (.quota 2))
 (.branch 67
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 73
 (.branch 70
 (.branch 69
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 117
 (.branch 97
 (.branch 87
 (.leaf (.quota 2))
 (.branch 92
 (.branch 89
 (.branch 88
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 94
 (.leaf (.quota 2))
 (.branch 95
 (.leaf (.quota 2))
 (.branch 96
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))))
 (.branch 107
 (.branch 102
 (.branch 99
 (.leaf (.quota 2))
 (.branch 100
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 104
 (.branch 103
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 105
 (.leaf (.quota 1))
 (.branch 106
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 112
 (.branch 109
 (.branch 108
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.branch 110
 (.leaf (.quota 1))
 (.branch 111
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0954))
 (.leaf (.quota 2)))))
 (.branch 114
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 136
 (.branch 126
 (.branch 121
 (.branch 119
 (.leaf (.quota 2))
 (.branch 120
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 123
 (.branch 122
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 124
 (.leaf (.quota 2))
 (.branch 125
 (.leaf (.quota 3))
 (.leaf (.quota 2))))))
 (.branch 131
 (.leaf (.quota 2))
 (.branch 133
 (.leaf (.quota 2))
 (.branch 134
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 146
 (.leaf (.quota 2))
 (.branch 151
 (.branch 148
 (.branch 147
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 149
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0955))
 (.branch 150
 (.leaf (.matching Nonrational.OldTerminalMatches.M014.r0956))
 (.leaf (.quota 1)))))
 (.branch 153
 (.leaf (.quota 2))
 (.branch 154
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0354
