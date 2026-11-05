module
prelude
public import RootedSubsumedForest0721Data
public import RawLeafCertificate
public import OldTerminalMatches.M020

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0721
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
 (.leaf (.quota 2))
 (.branch 8
 (.leaf (.quota 2))
 (.branch 9
 (.leaf (.quota 2))
 (.branch 10
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.leaf (.quota 2)))
 (.branch 33
 (.leaf (.quota 2))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf (.quota 1))
 (.branch 35
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 42
 (.branch 40
 (.leaf (.quota 2))
 (.branch 41
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))))
 (.branch 67
 (.leaf (.quota 2))
 (.branch 78
 (.branch 72
 (.branch 69
 (.branch 68
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 75
 (.branch 73
 (.leaf (.quota 2))
 (.branch 74
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 76
 (.leaf (.quota 1))
 (.branch 77
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1307))))))
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1308))
 (.branch 80
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1309))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1310))))
 (.branch 82
 (.leaf (.quota 1))
 (.branch 83
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2))))))
 (.branch 135
 (.branch 112
 (.branch 101
 (.branch 95
 (.branch 92
 (.branch 91
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 93
 (.leaf (.quota 2))
 (.branch 94
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 2)))
 (.branch 106
 (.leaf (.quota 2))
 (.branch 109
 (.branch 107
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 123
 (.branch 117
 (.branch 114
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 120
 (.branch 118
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 157
 (.branch 146
 (.branch 140
 (.branch 137
 (.branch 136
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 138
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 143
 (.leaf (.quota 2))
 (.branch 144
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 151
 (.branch 148
 (.leaf (.quota 2))
 (.branch 149
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 154
 (.branch 152
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1311))
 (.branch 153
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1312))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1313))))
 (.branch 155
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1314))
 (.branch 156
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 168
 (.branch 162
 (.branch 159
 (.branch 158
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1315))
 (.leaf (.quota 2)))
 (.branch 160
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1316))
 (.leaf (.quota 2))))
 (.branch 165
 (.branch 163
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1317))
 (.leaf (.quota 2)))
 (.branch 166
 (.leaf (.quota 2))
 (.branch 167
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 174
 (.branch 171
 (.branch 169
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 172
 (.leaf (.quota 2))
 (.branch 173
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 177
 (.branch 175
 (.leaf (.quota 2))
 (.branch 176
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 178
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0721
