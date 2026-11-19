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
public import RootedSubsumedForest0695Packed000
public import RootedSubsumedForest0695Packed001
public import RootedSubsumedForest0695Packed002
public import RootedSubsumedForest0695Packed003

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 19755
abbrev leafCount : Nat := 138
cert_widths_3 13 15 7 8
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 100
 (.branch 50
 nodeBlocks000
 nodeBlocks001)
 (.branch 150
 nodeBlocks002
 nodeBlocks003))
def counterTable : Table Nat :=
(.branch 100
 (.branch 50
 nodeCounters000
 nodeCounters001)
 (.branch 150
 nodeCounters002
 nodeCounters003))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table Nat :=
(.branch 69
 (.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 0))
 (.leaf (certNat% 1)))
 (.branch 3
 (.leaf (certNat% 2))
 (.leaf (certNat% 3))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 4))
 (.leaf (certNat% 5)))
 (.branch 7
 (.leaf (certNat% 6))
 (.leaf (certNat% 7)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (certNat% 8))
 (.leaf (certNat% 9)))
 (.branch 11
 (.leaf (certNat% 10))
 (.leaf (certNat% 11))))
 (.branch 14
 (.branch 13
 (.leaf (certNat% 12))
 (.leaf (certNat% 13)))
 (.branch 15
 (.leaf (certNat% 14))
 (.branch 16
 (.leaf (certNat% 15))
 (.leaf (certNat% 16)))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf (certNat% 17))
 (.leaf (certNat% 18)))
 (.branch 20
 (.leaf (certNat% 19))
 (.leaf (certNat% 20))))
 (.branch 23
 (.branch 22
 (.leaf (certNat% 21))
 (.leaf (certNat% 22)))
 (.branch 24
 (.leaf (certNat% 23))
 (.leaf (certNat% 24)))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf (certNat% 25))
 (.leaf (certNat% 26)))
 (.branch 28
 (.leaf (certNat% 27))
 (.leaf (certNat% 28))))
 (.branch 31
 (.branch 30
 (.leaf (certNat% 29))
 (.leaf (certNat% 30)))
 (.branch 32
 (.leaf (certNat% 31))
 (.branch 33
 (.leaf (certNat% 32))
 (.leaf (certNat% 33))))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf (certNat% 34))
 (.leaf (certNat% 35)))
 (.branch 37
 (.leaf (certNat% 36))
 (.leaf (certNat% 37))))
 (.branch 40
 (.branch 39
 (.leaf (certNat% 38))
 (.leaf (certNat% 39)))
 (.branch 41
 (.leaf (certNat% 40))
 (.leaf (certNat% 41)))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf (certNat% 42))
 (.leaf (certNat% 43)))
 (.branch 45
 (.leaf (certNat% 44))
 (.leaf (certNat% 45))))
 (.branch 48
 (.branch 47
 (.leaf (certNat% 46))
 (.leaf (certNat% 47)))
 (.branch 49
 (.leaf (certNat% 48))
 (.branch 50
 (.leaf (certNat% 49))
 (.leaf (certNat% 50)))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf (certNat% 51))
 (.leaf (certNat% 52)))
 (.branch 54
 (.leaf (certNat% 53))
 (.leaf (certNat% 54))))
 (.branch 57
 (.branch 56
 (.leaf (certNat% 55))
 (.leaf (certNat% 56)))
 (.branch 58
 (.leaf (certNat% 57))
 (.branch 59
 (.leaf (certNat% 58))
 (.leaf (certNat% 59))))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf (certNat% 60))
 (.leaf (certNat% 61)))
 (.branch 63
 (.leaf (certNat% 62))
 (.leaf (certNat% 63))))
 (.branch 66
 (.branch 65
 (.leaf (certNat% 64))
 (.leaf (certNat% 65)))
 (.branch 67
 (.leaf (certNat% 66))
 (.branch 68
 (.leaf (certNat% 67))
 (.leaf (certNat% 68)))))))))
 (.branch 103
 (.branch 86
 (.branch 77
 (.branch 73
 (.branch 71
 (.branch 70
 (.leaf (certNat% 69))
 (.leaf (certNat% 70)))
 (.branch 72
 (.leaf (certNat% 71))
 (.leaf (certNat% 72))))
 (.branch 75
 (.branch 74
 (.leaf (certNat% 73))
 (.leaf (certNat% 74)))
 (.branch 76
 (.leaf (certNat% 75))
 (.leaf (certNat% 76)))))
 (.branch 81
 (.branch 79
 (.branch 78
 (.leaf (certNat% 77))
 (.leaf (certNat% 78)))
 (.branch 80
 (.leaf (certNat% 79))
 (.leaf (certNat% 80))))
 (.branch 83
 (.branch 82
 (.leaf (certNat% 81))
 (.leaf (certNat% 82)))
 (.branch 84
 (.leaf (certNat% 83))
 (.branch 85
 (.leaf (certNat% 84))
 (.leaf (certNat% 85)))))))
 (.branch 94
 (.branch 90
 (.branch 88
 (.branch 87
 (.leaf (certNat% 86))
 (.leaf (certNat% 87)))
 (.branch 89
 (.leaf (certNat% 88))
 (.leaf (certNat% 89))))
 (.branch 92
 (.branch 91
 (.leaf (certNat% 90))
 (.leaf (certNat% 91)))
 (.branch 93
 (.leaf (certNat% 92))
 (.leaf (certNat% 93)))))
 (.branch 98
 (.branch 96
 (.branch 95
 (.leaf (certNat% 94))
 (.leaf (certNat% 95)))
 (.branch 97
 (.leaf (certNat% 96))
 (.leaf (certNat% 97))))
 (.branch 100
 (.branch 99
 (.leaf (certNat% 98))
 (.leaf (certNat% 99)))
 (.branch 101
 (.leaf (certNat% 100))
 (.branch 102
 (.leaf (certNat% 101))
 (.leaf (certNat% 102))))))))
 (.branch 120
 (.branch 111
 (.branch 107
 (.branch 105
 (.branch 104
 (.leaf (certNat% 103))
 (.leaf (certNat% 104)))
 (.branch 106
 (.leaf (certNat% 105))
 (.leaf (certNat% 106))))
 (.branch 109
 (.branch 108
 (.leaf (certNat% 107))
 (.leaf (certNat% 108)))
 (.branch 110
 (.leaf (certNat% 109))
 (.leaf (certNat% 110)))))
 (.branch 115
 (.branch 113
 (.branch 112
 (.leaf (certNat% 111))
 (.leaf (certNat% 112)))
 (.branch 114
 (.leaf (certNat% 113))
 (.leaf (certNat% 114))))
 (.branch 117
 (.branch 116
 (.leaf (certNat% 115))
 (.leaf (certNat% 116)))
 (.branch 118
 (.leaf (certNat% 117))
 (.branch 119
 (.leaf (certNat% 118))
 (.leaf (certNat% 119)))))))
 (.branch 129
 (.branch 124
 (.branch 122
 (.branch 121
 (.leaf (certNat% 120))
 (.leaf (certNat% 121)))
 (.branch 123
 (.leaf (certNat% 122))
 (.leaf (certNat% 123))))
 (.branch 126
 (.branch 125
 (.leaf (certNat% 124))
 (.leaf (certNat% 125)))
 (.branch 127
 (.leaf (certNat% 126))
 (.branch 128
 (.leaf (certNat% 127))
 (.leaf (certNat% 128))))))
 (.branch 133
 (.branch 131
 (.branch 130
 (.leaf (certNat% 129))
 (.leaf (certNat% 130)))
 (.branch 132
 (.leaf (certNat% 131))
 (.leaf (certNat% 132))))
 (.branch 135
 (.branch 134
 (.leaf (certNat% 133))
 (.leaf (certNat% 134)))
 (.branch 136
 (.leaf (certNat% 135))
 (.branch 137
 (.leaf (certNat% 136))
 (.leaf (certNat% 137))))))))))
cert_rawLeaves_4 13
cert_leaves_3
cert_quota_3 0 2 0 0 0 1 0 0 4 4
cert_nodeTest_5 96 03
cert_nodeTest_sound_4 96 03
cert_leafTest_4 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
