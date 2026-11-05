module
prelude
public import RootedSubsumedForest0365Data
public import RawLeafCertificate
public import OldTerminalMatches.M018

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 96
 (.branch 48
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.leaf (.quota 2))
 (.branch 4
 (.leaf (.quota 2))
 (.branch 5
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1203))
 (.leaf (.quota 2)))))
 (.branch 9
 (.branch 7
 (.leaf (.quota 2))
 (.branch 8
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1204))))
 (.branch 10
 (.leaf (.quota 2))
 (.branch 11
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.leaf (.quota 2)))
 (.branch 36
 (.branch 30
 (.leaf (.quota 2))
 (.branch 33
 (.leaf (.quota 2))
 (.branch 34
 (.leaf (.quota 3))
 (.leaf (.quota 2)))))
 (.branch 42
 (.leaf (.quota 2))
 (.branch 45
 (.branch 43
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1205))
 (.branch 44
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 46
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 72
 (.branch 60
 (.branch 54
 (.branch 51
 (.leaf (.quota 2))
 (.branch 52
 (.leaf (.quota 2))
 (.branch 53
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 57
 (.leaf (.quota 2))
 (.branch 58
 (.leaf (.quota 2))
 (.branch 59
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 66
 (.branch 63
 (.branch 61
 (.leaf (.quota 2))
 (.branch 62
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.branch 84
 (.branch 78
 (.branch 75
 (.leaf (.quota 2))
 (.branch 76
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 90
 (.branch 87
 (.leaf (.quota 2))
 (.branch 88
 (.leaf (.quota 1))
 (.branch 89
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 93
 (.leaf (.quota 2))
 (.branch 94
 (.leaf (.quota 2))
 (.branch 95
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))))
 (.branch 144
 (.branch 120
 (.branch 108
 (.branch 102
 (.branch 99
 (.branch 97
 (.leaf (.quota 2))
 (.branch 98
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 100
 (.leaf (.quota 2))
 (.branch 101
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 105
 (.branch 103
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 132
 (.branch 126
 (.leaf (.quota 2))
 (.branch 129
 (.branch 127
 (.leaf (.quota 2))
 (.branch 128
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2))))
 (.branch 138
 (.branch 135
 (.leaf (.quota 2))
 (.branch 136
 (.leaf (.quota 2))
 (.branch 137
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 141
 (.branch 139
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 168
 (.branch 156
 (.leaf (.quota 2))
 (.branch 162
 (.branch 159
 (.branch 157
 (.leaf (.quota 2))
 (.branch 158
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 160
 (.leaf (.quota 1))
 (.branch 161
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 165
 (.branch 163
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 166
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1206))
 (.branch 167
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1207))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1208)))))))
 (.branch 180
 (.branch 174
 (.branch 171
 (.branch 169
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1209))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 177
 (.branch 175
 (.leaf (.quota 2))
 (.branch 176
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 178
 (.leaf (.quota 1))
 (.branch 179
 (.leaf (.quota 1))
 (.leaf (.quota 3))))))
 (.branch 186
 (.branch 183
 (.branch 181
 (.leaf (.quota 3))
 (.branch 182
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 184
 (.leaf (.quota 3))
 (.branch 185
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 189
 (.branch 187
 (.leaf (.quota 2))
 (.branch 188
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.branch 190
 (.leaf (.quota 2))
 (.branch 191
 (.leaf (.quota 3))
 (.leaf (.quota 2))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase02.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
