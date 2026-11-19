module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0279
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 5388
abbrev leafCount : Nat := 16
cert_widths_3 14 13 6 4
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 21
 (.branch 10
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
 (.branch 7
 (.branch 6
 (.leaf ⟨((certNat% 10)),(certNat% 11)⟩)
 (.leaf ⟨((certNat% 12)),(certNat% 13)⟩))
 (.branch 8
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)
 (.branch 9
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩)
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩))
 (.branch 13
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)
 (.branch 14
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)))
 (.branch 19
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)
 (.branch 20
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩)
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩))))))
 (.branch 32
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩)
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩))
 (.branch 24
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩)
 (.branch 25
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩)
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩))))
 (.branch 29
 (.branch 27
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩)
 (.branch 28
 (.leaf ⟨((certNat% 54)),(certNat% 55)⟩)
 (.leaf ⟨((certNat% 56)),(certNat% 57)⟩)))
 (.branch 30
 (.leaf ⟨((certNat% 58)),(certNat% 59)⟩)
 (.branch 31
 (.leaf ⟨((certNat% 60)),(certNat% 61)⟩)
 (.leaf ⟨((certNat% 62)),(certNat% 63)⟩)))))
 (.branch 37
 (.branch 34
 (.branch 33
 (.leaf ⟨((certNat% 64)),(certNat% 65)⟩)
 (.leaf ⟨((certNat% 66)),(certNat% 67)⟩))
 (.branch 35
 (.leaf ⟨((certNat% 68)),(certNat% 69)⟩)
 (.branch 36
 (.leaf ⟨((certNat% 70)),(certNat% 71)⟩)
 (.leaf ⟨((certNat% 72)),(certNat% 73)⟩))))
 (.branch 40
 (.branch 38
 (.leaf ⟨((certNat% 74)),(certNat% 75)⟩)
 (.branch 39
 (.leaf ⟨((certNat% 76)),(certNat% 77)⟩)
 (.leaf ⟨((certNat% 78)),(certNat% 79)⟩)))
 (.branch 41
 (.leaf ⟨((certNat% 80)),(certNat% 81)⟩)
 (.branch 42
 (.leaf ⟨((certNat% 82)),(certNat% 83)⟩)
 (.leaf ⟨(certNat% 84),(certNat% 85)⟩)))))))
def counterTable : Table Nat :=
(.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 86))
 (.leaf (certNat% 87)))
 (.branch 3
 (.leaf (certNat% 88))
 (.branch 4
 (.leaf (certNat% 89))
 (.leaf (certNat% 90)))))
 (.branch 7
 (.branch 6
 (.leaf (certNat% 91))
 (.leaf (certNat% 92)))
 (.branch 8
 (.leaf (certNat% 93))
 (.branch 9
 (.leaf (certNat% 94))
 (.leaf (certNat% 95))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (certNat% 96))
 (.leaf (certNat% 97)))
 (.branch 13
 (.leaf (certNat% 98))
 (.branch 14
 (.leaf (certNat% 99))
 (.leaf (certNat% 100)))))
 (.branch 18
 (.branch 16
 (.leaf (certNat% 101))
 (.branch 17
 (.leaf (certNat% 102))
 (.leaf (certNat% 103))))
 (.branch 19
 (.leaf (certNat% 104))
 (.branch 20
 (.leaf (certNat% 105))
 (.leaf (certNat% 106)))))))
 (.branch 32
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf (certNat% 107))
 (.leaf (certNat% 108)))
 (.branch 24
 (.leaf (certNat% 109))
 (.branch 25
 (.leaf (certNat% 110))
 (.leaf (certNat% 111)))))
 (.branch 29
 (.branch 27
 (.leaf (certNat% 112))
 (.branch 28
 (.leaf (certNat% 113))
 (.leaf (certNat% 114))))
 (.branch 30
 (.leaf (certNat% 115))
 (.branch 31
 (.leaf (certNat% 116))
 (.leaf (certNat% 117))))))
 (.branch 37
 (.branch 34
 (.branch 33
 (.leaf (certNat% 118))
 (.leaf (certNat% 119)))
 (.branch 35
 (.leaf (certNat% 120))
 (.branch 36
 (.leaf (certNat% 121))
 (.leaf (certNat% 122)))))
 (.branch 40
 (.branch 38
 (.leaf (certNat% 123))
 (.branch 39
 (.leaf (certNat% 124))
 (.leaf (certNat% 125))))
 (.branch 41
 (.leaf (certNat% 126))
 (.branch 42
 (.leaf (certNat% 127))
 (.leaf (certNat% 128))))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,71,155,196,413,614,765,991,1368,14844])
 (.leaf [0,71,161,245,621,768,919,1543,10925,14964]))
 (.branch 3
 (.leaf [0,71,174,412,614,765,785,979,1364,14908])
 (.leaf [0,35,138,247,385,1014,1149,1370,11577,14713])))
 (.branch 6
 (.branch 5
 (.leaf [0,71,136,257,612,944,997,1529,11609,14960])
 (.leaf [0,9,171,203,409,595,668,974,1184,11544,15194]))
 (.branch 7
 (.leaf [0,1,247,297,347,640,983,1474,11621,15211])
 (.leaf [0,57,137,189,367,651,1031,1473,11604,15218]))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf [0,1,201,345,618,1019,1175,1478,11633,14996])
 (.leaf [0,35,119,216,399,586,910,1125,1512,10945,15243]))
 (.branch 11
 (.leaf [0,35,138,413,889,1016,1122,1365,8837,15239])
 (.leaf [0,35,116,245,401,1028,1134,1369,9597,15243])))
 (.branch 14
 (.branch 13
 (.leaf [0,71,146,238,351,586,973,1461,1493,10117,15243])
 (.leaf [0,35,133,255,603,854,1021,1122,1571,9323,15244]))
 (.branch 15
 (.leaf [0,35,133,255,375,585,854,1127,1571,10816,15244])
 (.leaf [0,107,119,399,600,624,1021,1122,1571,8867,15244])))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 1 1 0 0 0 0 4 3
cert_nodeTest_5 48 01
cert_nodeTest_sound_4 48 01
cert_leafTest_4 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0279
