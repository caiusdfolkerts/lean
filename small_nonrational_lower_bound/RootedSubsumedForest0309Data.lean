module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0309
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 5577
abbrev leafCount : Nat := 10
cert_widths_3 14 13 6 4
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)
 (.branch 4
 (.leaf ⟨((certNat% 6)),(certNat% 7)⟩)
 (.leaf ⟨((certNat% 8)),(certNat% 9)⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨((certNat% 10)),(certNat% 11)⟩)
 (.branch 7
 (.leaf ⟨((certNat% 12)),(certNat% 13)⟩)
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)))
 (.branch 9
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)
 (.branch 10
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩))
 (.branch 14
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)
 (.branch 15
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.branch 18
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)))
 (.branch 20
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩)
 (.branch 21
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩)
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩))
 (.branch 25
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩)
 (.branch 26
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩)
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨((certNat% 54)),(certNat% 55)⟩)
 (.branch 29
 (.leaf ⟨((certNat% 56)),(certNat% 57)⟩)
 (.leaf ⟨((certNat% 58)),(certNat% 59)⟩)))
 (.branch 31
 (.leaf ⟨((certNat% 60)),(certNat% 61)⟩)
 (.branch 32
 (.leaf ⟨((certNat% 62)),(certNat% 63)⟩)
 (.leaf ⟨((certNat% 64)),(certNat% 65)⟩)))))
 (.branch 38
 (.branch 35
 (.branch 34
 (.leaf ⟨((certNat% 66)),(certNat% 67)⟩)
 (.leaf ⟨((certNat% 68)),(certNat% 69)⟩))
 (.branch 36
 (.leaf ⟨((certNat% 70)),(certNat% 71)⟩)
 (.branch 37
 (.leaf ⟨((certNat% 72)),(certNat% 73)⟩)
 (.leaf ⟨((certNat% 74)),(certNat% 75)⟩))))
 (.branch 41
 (.branch 39
 (.leaf ⟨((certNat% 76)),(certNat% 77)⟩)
 (.branch 40
 (.leaf ⟨((certNat% 78)),(certNat% 79)⟩)
 (.leaf ⟨((certNat% 80)),(certNat% 81)⟩)))
 (.branch 42
 (.leaf ⟨((certNat% 82)),(certNat% 83)⟩)
 (.branch 43
 (.leaf ⟨((certNat% 84)),(certNat% 85)⟩)
 (.leaf ⟨(certNat% 86),(certNat% 87)⟩)))))))
def counterTable : Table Nat :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 88))
 (.leaf (certNat% 89)))
 (.branch 3
 (.leaf (certNat% 90))
 (.branch 4
 (.leaf (certNat% 91))
 (.leaf (certNat% 92)))))
 (.branch 8
 (.branch 6
 (.leaf (certNat% 93))
 (.branch 7
 (.leaf (certNat% 94))
 (.leaf (certNat% 95))))
 (.branch 9
 (.leaf (certNat% 96))
 (.branch 10
 (.leaf (certNat% 97))
 (.leaf (certNat% 98))))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf (certNat% 99))
 (.leaf (certNat% 100)))
 (.branch 14
 (.leaf (certNat% 101))
 (.branch 15
 (.leaf (certNat% 102))
 (.leaf (certNat% 103)))))
 (.branch 19
 (.branch 17
 (.leaf (certNat% 104))
 (.branch 18
 (.leaf (certNat% 105))
 (.leaf (certNat% 106))))
 (.branch 20
 (.leaf (certNat% 107))
 (.branch 21
 (.leaf (certNat% 108))
 (.leaf (certNat% 109)))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf (certNat% 110))
 (.leaf (certNat% 111)))
 (.branch 25
 (.leaf (certNat% 112))
 (.branch 26
 (.leaf (certNat% 113))
 (.leaf (certNat% 114)))))
 (.branch 30
 (.branch 28
 (.leaf (certNat% 115))
 (.branch 29
 (.leaf (certNat% 116))
 (.leaf (certNat% 117))))
 (.branch 31
 (.leaf (certNat% 118))
 (.branch 32
 (.leaf (certNat% 119))
 (.leaf (certNat% 120))))))
 (.branch 38
 (.branch 35
 (.branch 34
 (.leaf (certNat% 121))
 (.leaf (certNat% 122)))
 (.branch 36
 (.leaf (certNat% 123))
 (.branch 37
 (.leaf (certNat% 124))
 (.leaf (certNat% 125)))))
 (.branch 41
 (.branch 39
 (.leaf (certNat% 126))
 (.branch 40
 (.leaf (certNat% 127))
 (.leaf (certNat% 128))))
 (.branch 42
 (.leaf (certNat% 129))
 (.branch 43
 (.leaf (certNat% 130))
 (.leaf (certNat% 131))))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf [0,6,35,116,381,772,911,1029,1146,1366,15242])
 (.leaf [0,31,35,119,204,384,911,1029,1146,1366,15242]))
 (.branch 3
 (.leaf [0,1,5,357,613,773,932,1029,1170,1364,15242])
 (.branch 4
 (.leaf [0,1,6,262,348,625,934,1017,1182,1364,15238])
 (.leaf [0,33,72,130,255,372,645,1012,1362,1571,15244]))))
 (.branch 7
 (.branch 6
 (.leaf [0,35,61,133,255,371,585,854,1119,1405,1571,15244])
 (.leaf [0,35,87,145,254,360,585,875,1000,1122,1570,15245]))
 (.branch 8
 (.leaf [0,28,35,145,242,360,588,896,998,1134,1572,15241])
 (.branch 9
 (.leaf [0,1,6,262,348,625,848,1014,1185,1364,15244])
 (.leaf [0,6,71,153,393,621,848,988,1362,1550,15244])))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 1 0 0 0 0 0 2 6
cert_nodeTest_5 48 01
cert_nodeTest_sound_4 48 01
cert_leafTest_4 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0309
