module
prelude
public import RootedSubsumedForest0320Data
public import RawLeafCertificate
public import OldTerminalMatches.M007

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
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
 (.branch 1
 (.leaf (.quota 2))
 (.branch 2
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.branch 4
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 9
 (.branch 7
 (.leaf (.quota 3))
 (.branch 8
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 10
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))
 (.branch 18
 (.branch 15
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 21
 (.leaf (.quota 2))
 (.branch 22
 (.leaf (.quota 3))
 (.branch 23
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf (.quota 2))
 (.branch 26
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 33
 (.leaf (.quota 3))
 (.branch 34
 (.leaf (.quota 3))
 (.branch 35
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 42
 (.branch 39
 (.leaf (.quota 2))
 (.branch 40
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 45
 (.branch 43
 (.leaf (.quota 3))
 (.branch 44
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.branch 46
 (.leaf (.quota 3))
 (.branch 47
 (.leaf (.quota 3))
 (.leaf (.quota 1))))))))
 (.branch 72
 (.branch 60
 (.branch 54
 (.leaf (.quota 2))
 (.branch 57
 (.leaf (.quota 2))
 (.branch 58
 (.leaf (.quota 1))
 (.branch 59
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 66
 (.branch 63
 (.branch 61
 (.leaf (.quota 1))
 (.branch 62
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 69
 (.leaf (.quota 2))
 (.branch 70
 (.leaf (.quota 2))
 (.branch 71
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 84
 (.branch 78
 (.branch 75
 (.branch 73
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 76
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 81
 (.branch 79
 (.leaf (.quota 1))
 (.branch 80
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 82
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 90
 (.branch 87
 (.branch 85
 (.leaf (.quota 2))
 (.branch 86
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0492))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 93
 (.branch 91
 (.leaf (.quota 2))
 (.branch 92
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))))))
 (.branch 144
 (.branch 120
 (.branch 108
 (.branch 102
 (.branch 99
 (.branch 97
 (.leaf (.quota 2))
 (.branch 98
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 105
 (.branch 103
 (.leaf (.quota 1))
 (.branch 104
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.branch 106
 (.leaf (.quota 3))
 (.branch 107
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0493))
 (.leaf (.quota 1))))))
 (.branch 114
 (.branch 111
 (.branch 109
 (.leaf (.quota 1))
 (.branch 110
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 112
 (.leaf (.quota 1))
 (.branch 113
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0494))
 (.leaf (.quota 1)))))
 (.branch 117
 (.branch 115
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
 (.branch 132
 (.branch 126
 (.branch 123
 (.branch 121
 (.leaf (.quota 3))
 (.branch 122
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 124
 (.leaf (.quota 2))
 (.branch 125
 (.leaf (.quota 1))
 (.leaf (.quota 3)))))
 (.branch 129
 (.branch 127
 (.leaf (.quota 3))
 (.branch 128
 (.leaf (.quota 2))
 (.leaf (.quota 3))))
 (.branch 130
 (.leaf (.quota 2))
 (.branch 131
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 138
 (.branch 135
 (.branch 133
 (.leaf (.quota 2))
 (.branch 134
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 136
 (.leaf (.quota 2))
 (.branch 137
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0495))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0496)))))
 (.branch 141
 (.branch 139
 (.leaf (.quota 2))
 (.branch 140
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 142
 (.leaf (.quota 2))
 (.branch 143
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0497))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0498))))))))
 (.branch 168
 (.branch 156
 (.branch 150
 (.branch 147
 (.branch 145
 (.leaf (.quota 2))
 (.branch 146
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 148
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 153
 (.branch 151
 (.leaf (.quota 2))
 (.branch 152
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 154
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0499))
 (.branch 155
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 162
 (.branch 159
 (.branch 157
 (.leaf (.quota 2))
 (.branch 158
 (.leaf (.quota 1))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0500))))
 (.branch 160
 (.leaf (.quota 1))
 (.branch 161
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0501))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0502)))))
 (.branch 165
 (.leaf (.quota 2))
 (.branch 166
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 180
 (.branch 174
 (.branch 171
 (.branch 169
 (.leaf (.quota 1))
 (.branch 170
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0503))
 (.leaf (.quota 2))))
 (.branch 172
 (.leaf (.quota 2))
 (.branch 173
 (.leaf (.quota 3))
 (.leaf (.quota 1)))))
 (.branch 177
 (.branch 175
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 178
 (.leaf (.quota 2))
 (.branch 179
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 186
 (.branch 183
 (.branch 181
 (.leaf (.quota 1))
 (.branch 182
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M007.r0504))))
 (.leaf (.quota 2)))
 (.branch 189
 (.branch 187
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 190
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
