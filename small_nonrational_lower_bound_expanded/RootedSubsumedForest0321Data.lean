module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public meta import CertificateNumbers
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0321Packed000
public import RootedSubsumedForest0321Packed001
public import RootedSubsumedForest0321Packed002
public import RootedSubsumedForest0321Packed003

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0321
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 22737
abbrev leafCount : Nat := 136
cert_widths_3 13 15 6 8
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
(.branch 68
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
 (.branch 59
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
 (.leaf (certNat% 58)))))
 (.branch 63
 (.branch 61
 (.branch 60
 (.leaf (certNat% 59))
 (.leaf (certNat% 60)))
 (.branch 62
 (.leaf (certNat% 61))
 (.leaf (certNat% 62))))
 (.branch 65
 (.branch 64
 (.leaf (certNat% 63))
 (.leaf (certNat% 64)))
 (.branch 66
 (.leaf (certNat% 65))
 (.branch 67
 (.leaf (certNat% 66))
 (.leaf (certNat% 67)))))))))
 (.branch 102
 (.branch 85
 (.branch 76
 (.branch 72
 (.branch 70
 (.branch 69
 (.leaf (certNat% 68))
 (.leaf (certNat% 69)))
 (.branch 71
 (.leaf (certNat% 70))
 (.leaf (certNat% 71))))
 (.branch 74
 (.branch 73
 (.leaf (certNat% 72))
 (.leaf (certNat% 73)))
 (.branch 75
 (.leaf (certNat% 74))
 (.leaf (certNat% 75)))))
 (.branch 80
 (.branch 78
 (.branch 77
 (.leaf (certNat% 76))
 (.leaf (certNat% 77)))
 (.branch 79
 (.leaf (certNat% 78))
 (.leaf (certNat% 79))))
 (.branch 82
 (.branch 81
 (.leaf (certNat% 80))
 (.leaf (certNat% 81)))
 (.branch 83
 (.leaf (certNat% 82))
 (.branch 84
 (.leaf (certNat% 83))
 (.leaf (certNat% 84)))))))
 (.branch 93
 (.branch 89
 (.branch 87
 (.branch 86
 (.leaf (certNat% 85))
 (.leaf (certNat% 86)))
 (.branch 88
 (.leaf (certNat% 87))
 (.leaf (certNat% 88))))
 (.branch 91
 (.branch 90
 (.leaf (certNat% 89))
 (.leaf (certNat% 90)))
 (.branch 92
 (.leaf (certNat% 91))
 (.leaf (certNat% 92)))))
 (.branch 97
 (.branch 95
 (.branch 94
 (.leaf (certNat% 93))
 (.leaf (certNat% 94)))
 (.branch 96
 (.leaf (certNat% 95))
 (.leaf (certNat% 96))))
 (.branch 99
 (.branch 98
 (.leaf (certNat% 97))
 (.leaf (certNat% 98)))
 (.branch 100
 (.leaf (certNat% 99))
 (.branch 101
 (.leaf (certNat% 100))
 (.leaf (certNat% 101))))))))
 (.branch 119
 (.branch 110
 (.branch 106
 (.branch 104
 (.branch 103
 (.leaf (certNat% 102))
 (.leaf (certNat% 103)))
 (.branch 105
 (.leaf (certNat% 104))
 (.leaf (certNat% 105))))
 (.branch 108
 (.branch 107
 (.leaf (certNat% 106))
 (.leaf (certNat% 107)))
 (.branch 109
 (.leaf (certNat% 108))
 (.leaf (certNat% 109)))))
 (.branch 114
 (.branch 112
 (.branch 111
 (.leaf (certNat% 110))
 (.leaf (certNat% 111)))
 (.branch 113
 (.leaf (certNat% 112))
 (.leaf (certNat% 113))))
 (.branch 116
 (.branch 115
 (.leaf (certNat% 114))
 (.leaf (certNat% 115)))
 (.branch 117
 (.leaf (certNat% 116))
 (.branch 118
 (.leaf (certNat% 117))
 (.leaf (certNat% 118)))))))
 (.branch 127
 (.branch 123
 (.branch 121
 (.branch 120
 (.leaf (certNat% 119))
 (.leaf (certNat% 120)))
 (.branch 122
 (.leaf (certNat% 121))
 (.leaf (certNat% 122))))
 (.branch 125
 (.branch 124
 (.leaf (certNat% 123))
 (.leaf (certNat% 124)))
 (.branch 126
 (.leaf (certNat% 125))
 (.leaf (certNat% 126)))))
 (.branch 131
 (.branch 129
 (.branch 128
 (.leaf (certNat% 127))
 (.leaf (certNat% 128)))
 (.branch 130
 (.leaf (certNat% 129))
 (.leaf (certNat% 130))))
 (.branch 133
 (.branch 132
 (.leaf (certNat% 131))
 (.leaf (certNat% 132)))
 (.branch 134
 (.leaf (certNat% 133))
 (.branch 135
 (.leaf (certNat% 134))
 (.leaf (certNat% 135))))))))))
cert_rawLeaves_4 13
cert_leaves_3
cert_quota_3 0 3 1 0 0 0 0 0 3 5
cert_nodeTest_5 48 02
cert_nodeTest_sound_4 48 02
cert_leafTest_4 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0321
