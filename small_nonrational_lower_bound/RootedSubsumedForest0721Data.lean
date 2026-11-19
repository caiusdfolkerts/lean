module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public meta import CertificateNumbers
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0721Packed000
public import RootedSubsumedForest0721Packed001
public import RootedSubsumedForest0721Packed002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0721
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 15427
abbrev leafCount : Nat := 180
cert_widths_3 13 14 7 8
cert_blocks_11
cert_counterTable_3
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table Nat :=
(.branch 90
 (.branch 45
 (.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 0))
 (.leaf (certNat% 1)))
 (.branch 3
 (.leaf (certNat% 2))
 (.branch 4
 (.leaf (certNat% 3))
 (.leaf (certNat% 4)))))
 (.branch 8
 (.branch 6
 (.leaf (certNat% 5))
 (.branch 7
 (.leaf (certNat% 6))
 (.leaf (certNat% 7))))
 (.branch 9
 (.leaf (certNat% 8))
 (.branch 10
 (.leaf (certNat% 9))
 (.leaf (certNat% 10))))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf (certNat% 11))
 (.leaf (certNat% 12)))
 (.branch 14
 (.leaf (certNat% 13))
 (.branch 15
 (.leaf (certNat% 14))
 (.leaf (certNat% 15)))))
 (.branch 19
 (.branch 17
 (.leaf (certNat% 16))
 (.branch 18
 (.leaf (certNat% 17))
 (.leaf (certNat% 18))))
 (.branch 20
 (.leaf (certNat% 19))
 (.branch 21
 (.leaf (certNat% 20))
 (.leaf (certNat% 21)))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf (certNat% 22))
 (.leaf (certNat% 23)))
 (.branch 25
 (.leaf (certNat% 24))
 (.branch 26
 (.leaf (certNat% 25))
 (.leaf (certNat% 26)))))
 (.branch 30
 (.branch 28
 (.leaf (certNat% 27))
 (.branch 29
 (.leaf (certNat% 28))
 (.leaf (certNat% 29))))
 (.branch 31
 (.leaf (certNat% 30))
 (.branch 32
 (.leaf (certNat% 31))
 (.leaf (certNat% 32))))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf (certNat% 33))
 (.branch 35
 (.leaf (certNat% 34))
 (.leaf (certNat% 35))))
 (.branch 37
 (.leaf (certNat% 36))
 (.branch 38
 (.leaf (certNat% 37))
 (.leaf (certNat% 38)))))
 (.branch 42
 (.branch 40
 (.leaf (certNat% 39))
 (.branch 41
 (.leaf (certNat% 40))
 (.leaf (certNat% 41))))
 (.branch 43
 (.leaf (certNat% 42))
 (.branch 44
 (.leaf (certNat% 43))
 (.leaf (certNat% 44))))))))
 (.branch 67
 (.branch 56
 (.branch 50
 (.branch 47
 (.branch 46
 (.leaf (certNat% 45))
 (.leaf (certNat% 46)))
 (.branch 48
 (.leaf (certNat% 47))
 (.branch 49
 (.leaf (certNat% 48))
 (.leaf (certNat% 49)))))
 (.branch 53
 (.branch 51
 (.leaf (certNat% 50))
 (.branch 52
 (.leaf (certNat% 51))
 (.leaf (certNat% 52))))
 (.branch 54
 (.leaf (certNat% 53))
 (.branch 55
 (.leaf (certNat% 54))
 (.leaf (certNat% 55))))))
 (.branch 61
 (.branch 58
 (.branch 57
 (.leaf (certNat% 56))
 (.leaf (certNat% 57)))
 (.branch 59
 (.leaf (certNat% 58))
 (.branch 60
 (.leaf (certNat% 59))
 (.leaf (certNat% 60)))))
 (.branch 64
 (.branch 62
 (.leaf (certNat% 61))
 (.branch 63
 (.leaf (certNat% 62))
 (.leaf (certNat% 63))))
 (.branch 65
 (.leaf (certNat% 64))
 (.branch 66
 (.leaf (certNat% 65))
 (.leaf (certNat% 66)))))))
 (.branch 78
 (.branch 72
 (.branch 69
 (.branch 68
 (.leaf (certNat% 67))
 (.leaf (certNat% 68)))
 (.branch 70
 (.leaf (certNat% 69))
 (.branch 71
 (.leaf (certNat% 70))
 (.leaf (certNat% 71)))))
 (.branch 75
 (.branch 73
 (.leaf (certNat% 72))
 (.branch 74
 (.leaf (certNat% 73))
 (.leaf (certNat% 74))))
 (.branch 76
 (.leaf (certNat% 75))
 (.branch 77
 (.leaf (certNat% 76))
 (.leaf (certNat% 77))))))
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf (certNat% 78))
 (.branch 80
 (.leaf (certNat% 79))
 (.leaf (certNat% 80))))
 (.branch 82
 (.leaf (certNat% 81))
 (.branch 83
 (.leaf (certNat% 82))
 (.leaf (certNat% 83)))))
 (.branch 87
 (.branch 85
 (.leaf (certNat% 84))
 (.branch 86
 (.leaf (certNat% 85))
 (.leaf (certNat% 86))))
 (.branch 88
 (.leaf (certNat% 87))
 (.branch 89
 (.leaf (certNat% 88))
 (.leaf (certNat% 89)))))))))
 (.branch 135
 (.branch 112
 (.branch 101
 (.branch 95
 (.branch 92
 (.branch 91
 (.leaf (certNat% 90))
 (.leaf (certNat% 91)))
 (.branch 93
 (.leaf (certNat% 92))
 (.branch 94
 (.leaf (certNat% 93))
 (.leaf (certNat% 94)))))
 (.branch 98
 (.branch 96
 (.leaf (certNat% 95))
 (.branch 97
 (.leaf (certNat% 96))
 (.leaf (certNat% 97))))
 (.branch 99
 (.leaf (certNat% 98))
 (.branch 100
 (.leaf (certNat% 99))
 (.leaf (certNat% 100))))))
 (.branch 106
 (.branch 103
 (.branch 102
 (.leaf (certNat% 101))
 (.leaf (certNat% 102)))
 (.branch 104
 (.leaf (certNat% 103))
 (.branch 105
 (.leaf (certNat% 104))
 (.leaf (certNat% 105)))))
 (.branch 109
 (.branch 107
 (.leaf (certNat% 106))
 (.branch 108
 (.leaf (certNat% 107))
 (.leaf (certNat% 108))))
 (.branch 110
 (.leaf (certNat% 109))
 (.branch 111
 (.leaf (certNat% 110))
 (.leaf (certNat% 111)))))))
 (.branch 123
 (.branch 117
 (.branch 114
 (.branch 113
 (.leaf (certNat% 112))
 (.leaf (certNat% 113)))
 (.branch 115
 (.leaf (certNat% 114))
 (.branch 116
 (.leaf (certNat% 115))
 (.leaf (certNat% 116)))))
 (.branch 120
 (.branch 118
 (.leaf (certNat% 117))
 (.branch 119
 (.leaf (certNat% 118))
 (.leaf (certNat% 119))))
 (.branch 121
 (.leaf (certNat% 120))
 (.branch 122
 (.leaf (certNat% 121))
 (.leaf (certNat% 122))))))
 (.branch 129
 (.branch 126
 (.branch 124
 (.leaf (certNat% 123))
 (.branch 125
 (.leaf (certNat% 124))
 (.leaf (certNat% 125))))
 (.branch 127
 (.leaf (certNat% 126))
 (.branch 128
 (.leaf (certNat% 127))
 (.leaf (certNat% 128)))))
 (.branch 132
 (.branch 130
 (.leaf (certNat% 129))
 (.branch 131
 (.leaf (certNat% 130))
 (.leaf (certNat% 131))))
 (.branch 133
 (.leaf (certNat% 132))
 (.branch 134
 (.leaf (certNat% 133))
 (.leaf (certNat% 134))))))))
 (.branch 157
 (.branch 146
 (.branch 140
 (.branch 137
 (.branch 136
 (.leaf (certNat% 135))
 (.leaf (certNat% 136)))
 (.branch 138
 (.leaf (certNat% 137))
 (.branch 139
 (.leaf (certNat% 138))
 (.leaf (certNat% 139)))))
 (.branch 143
 (.branch 141
 (.leaf (certNat% 140))
 (.branch 142
 (.leaf (certNat% 141))
 (.leaf (certNat% 142))))
 (.branch 144
 (.leaf (certNat% 143))
 (.branch 145
 (.leaf (certNat% 144))
 (.leaf (certNat% 145))))))
 (.branch 151
 (.branch 148
 (.branch 147
 (.leaf (certNat% 146))
 (.leaf (certNat% 147)))
 (.branch 149
 (.leaf (certNat% 148))
 (.branch 150
 (.leaf (certNat% 149))
 (.leaf (certNat% 150)))))
 (.branch 154
 (.branch 152
 (.leaf (certNat% 151))
 (.branch 153
 (.leaf (certNat% 152))
 (.leaf (certNat% 153))))
 (.branch 155
 (.leaf (certNat% 154))
 (.branch 156
 (.leaf (certNat% 155))
 (.leaf (certNat% 156)))))))
 (.branch 168
 (.branch 162
 (.branch 159
 (.branch 158
 (.leaf (certNat% 157))
 (.leaf (certNat% 158)))
 (.branch 160
 (.leaf (certNat% 159))
 (.branch 161
 (.leaf (certNat% 160))
 (.leaf (certNat% 161)))))
 (.branch 165
 (.branch 163
 (.leaf (certNat% 162))
 (.branch 164
 (.leaf (certNat% 163))
 (.leaf (certNat% 164))))
 (.branch 166
 (.leaf (certNat% 165))
 (.branch 167
 (.leaf (certNat% 166))
 (.leaf (certNat% 167))))))
 (.branch 174
 (.branch 171
 (.branch 169
 (.leaf (certNat% 168))
 (.branch 170
 (.leaf (certNat% 169))
 (.leaf (certNat% 170))))
 (.branch 172
 (.leaf (certNat% 171))
 (.branch 173
 (.leaf (certNat% 172))
 (.leaf (certNat% 173)))))
 (.branch 177
 (.branch 175
 (.leaf (certNat% 174))
 (.branch 176
 (.leaf (certNat% 175))
 (.leaf (certNat% 176))))
 (.branch 178
 (.leaf (certNat% 177))
 (.branch 179
 (.leaf (certNat% 178))
 (.leaf (certNat% 179))))))))))
cert_rawLeaves_4 13
cert_leaves_3
cert_quota_3 0 3 0 0 0 0 0 0 1 8
cert_nodeTest_5 96 03
cert_nodeTest_sound_4 96 03
cert_leafTest_4 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0721
