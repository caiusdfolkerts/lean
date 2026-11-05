module
prelude
public import RootedSubsumedForest0869Data
public import RawLeafCertificate
public import OldTerminalMatches.M025

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0869
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 90
 (.branch 45
 (.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.leaf (.quota 2))
 (.branch 3
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.branch 8
 (.leaf (.quota 2))
 (.branch 9
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 16
 (.branch 13
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 19
 (.branch 17
 (.leaf (.quota 3))
 (.branch 18
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.branch 20
 (.leaf (.quota 3))
 (.branch 21
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf (.quota 2))
 (.leaf (.quota 3)))
 (.branch 25
 (.leaf (.quota 3))
 (.branch 26
 (.leaf (.quota 1))
 (.leaf (.quota 3)))))
 (.branch 30
 (.leaf (.quota 3))
 (.branch 31
 (.leaf (.quota 1))
 (.leaf (.quota 3)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf (.quota 3))
 (.branch 35
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 3)))
 (.branch 42
 (.branch 40
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 67
 (.leaf (.quota 2))
 (.branch 78
 (.leaf (.quota 2))
 (.branch 84
 (.branch 81
 (.leaf (.quota 2))
 (.branch 82
 (.leaf (.quota 2))
 (.branch 83
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 87
 (.branch 85
 (.leaf (.quota 2))
 (.branch 86
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 88
 (.leaf (.quota 2))
 (.branch 89
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 135
 (.branch 112
 (.branch 101
 (.branch 95
 (.branch 92
 (.branch 91
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 93
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 123
 (.leaf (.quota 2))
 (.branch 129
 (.branch 126
 (.branch 124
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1658))
 (.leaf (.quota 2)))
 (.branch 127
 (.leaf (.quota 2))
 (.branch 128
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 132
 (.branch 130
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 133
 (.leaf (.quota 1))
 (.branch 134
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 158
 (.branch 146
 (.branch 140
 (.branch 137
 (.branch 136
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 138
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 143
 (.branch 141
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1659))
 (.branch 142
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 152
 (.leaf (.quota 2))
 (.branch 155
 (.branch 153
 (.leaf (.quota 1))
 (.branch 154
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 156
 (.leaf (.quota 2))
 (.branch 157
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 169
 (.branch 163
 (.branch 160
 (.branch 159
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 161
 (.leaf (.quota 1))
 (.branch 162
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1660))
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1661)))))
 (.branch 166
 (.leaf (.quota 2))
 (.branch 167
 (.leaf (.quota 1))
 (.branch 168
 (.leaf (.matching Nonrational.OldTerminalMatches.M025.r1662))
 (.leaf (.quota 1))))))
 (.branch 175
 (.branch 172
 (.leaf (.quota 2))
 (.branch 173
 (.leaf (.quota 2))
 (.branch 174
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 178
 (.leaf (.quota 1))
 (.branch 179
 (.leaf (.quota 2))
 (.branch 180
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0869
