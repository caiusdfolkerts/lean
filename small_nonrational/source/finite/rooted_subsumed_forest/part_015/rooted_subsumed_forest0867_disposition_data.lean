module
prelude
public import RootedSubsumedForest0867Data
public import RawLeafCertificate
public import OldTerminalMatches.M025

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0867
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 86
 (.branch 43
 (.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.leaf (.quota 2))
 (.branch 3
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 7
 (.leaf (.quota 1))
 (.branch 8
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1652))
 (.branch 9
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1653))
 (.leaf (.quota 1))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 32
 (.leaf (.quota 2))
 (.branch 37
 (.branch 34
 (.leaf (.quota 2))
 (.branch 35
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 64
 (.branch 53
 (.branch 48
 (.leaf (.quota 2))
 (.branch 50
 (.branch 49
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 51
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 58
 (.branch 55
 (.branch 54
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 61
 (.branch 59
 (.leaf (.quota 2))
 (.branch 60
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 62
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 75
 (.branch 69
 (.leaf (.quota 2))
 (.branch 72
 (.branch 70
 (.leaf (.quota 2))
 (.branch 71
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 73
 (.leaf (.quota 1))
 (.branch 74
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 80
 (.branch 77
 (.branch 76
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 83
 (.branch 81
 (.leaf (.quota 2))
 (.branch 82
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 84
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 129
 (.branch 107
 (.branch 96
 (.branch 91
 (.branch 88
 (.branch 87
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 89
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 93
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 101
 (.branch 98
 (.leaf (.quota 1))
 (.branch 99
 (.leaf (.quota 2))
 (.branch 100
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2))))
 (.branch 118
 (.branch 112
 (.leaf (.quota 2))
 (.branch 115
 (.branch 113
 (.leaf (.quota 2))
 (.branch 114
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))
 (.branch 123
 (.branch 120
 (.leaf (.quota 1))
 (.branch 121
 (.leaf (.quota 1))
 (.branch 122
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1654)))))
 (.branch 126
 (.branch 124
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1655))
 (.branch 125
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1656))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))))
 (.branch 150
 (.branch 139
 (.branch 134
 (.branch 131
 (.branch 130
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1657))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 136
 (.leaf (.quota 2))
 (.branch 137
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 144
 (.branch 141
 (.leaf (.quota 2))
 (.branch 142
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 147
 (.branch 145
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 148
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 161
 (.branch 155
 (.branch 152
 (.branch 151
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 153
 (.leaf (.quota 1))
 (.branch 154
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 158
 (.leaf (.quota 2))
 (.branch 159
 (.leaf (.quota 2))
 (.branch 160
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 166
 (.branch 163
 (.leaf (.quota 2))
 (.branch 164
 (.leaf (.quota 2))
 (.branch 165
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 169
 (.branch 167
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 170
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0867
