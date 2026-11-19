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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0243
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 5210
abbrev leafCount : Nat := 5
cert_widths_3 14 13 6 3
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 20
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
 (.branch 17
 (.branch 16
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩))
 (.branch 18
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)
 (.branch 19
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩))
 (.branch 23
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩)
 (.branch 24
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩)
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩)
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩))
 (.branch 28
 (.leaf ⟨((certNat% 54)),(certNat% 55)⟩)
 (.branch 29
 (.leaf ⟨((certNat% 56)),(certNat% 57)⟩)
 (.leaf ⟨((certNat% 58)),(certNat% 59)⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨((certNat% 60)),(certNat% 61)⟩)
 (.leaf ⟨((certNat% 62)),(certNat% 63)⟩))
 (.branch 33
 (.leaf ⟨((certNat% 64)),(certNat% 65)⟩)
 (.branch 34
 (.leaf ⟨((certNat% 66)),(certNat% 67)⟩)
 (.leaf ⟨((certNat% 68)),(certNat% 69)⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨((certNat% 70)),(certNat% 71)⟩)
 (.branch 37
 (.leaf ⟨((certNat% 72)),(certNat% 73)⟩)
 (.leaf ⟨((certNat% 74)),(certNat% 75)⟩)))
 (.branch 39
 (.leaf ⟨((certNat% 76)),(certNat% 77)⟩)
 (.branch 40
 (.leaf ⟨((certNat% 78)),(certNat% 79)⟩)
 (.leaf ⟨(certNat% 80),(certNat% 81)⟩)))))))
def counterTable : Table Nat :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 82))
 (.leaf (certNat% 83)))
 (.branch 3
 (.leaf (certNat% 84))
 (.branch 4
 (.leaf (certNat% 85))
 (.leaf (certNat% 86)))))
 (.branch 7
 (.branch 6
 (.leaf (certNat% 87))
 (.leaf (certNat% 88)))
 (.branch 8
 (.leaf (certNat% 89))
 (.branch 9
 (.leaf (certNat% 90))
 (.leaf (certNat% 91))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (certNat% 92))
 (.leaf (certNat% 93)))
 (.branch 13
 (.leaf (certNat% 94))
 (.branch 14
 (.leaf (certNat% 95))
 (.leaf (certNat% 96)))))
 (.branch 17
 (.branch 16
 (.leaf (certNat% 97))
 (.leaf (certNat% 98)))
 (.branch 18
 (.leaf (certNat% 99))
 (.branch 19
 (.leaf (certNat% 100))
 (.leaf (certNat% 101)))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf (certNat% 102))
 (.leaf (certNat% 103)))
 (.branch 23
 (.leaf (certNat% 104))
 (.branch 24
 (.leaf (certNat% 105))
 (.leaf (certNat% 106)))))
 (.branch 27
 (.branch 26
 (.leaf (certNat% 107))
 (.leaf (certNat% 108)))
 (.branch 28
 (.leaf (certNat% 109))
 (.branch 29
 (.leaf (certNat% 110))
 (.leaf (certNat% 111))))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf (certNat% 112))
 (.leaf (certNat% 113)))
 (.branch 33
 (.leaf (certNat% 114))
 (.branch 34
 (.leaf (certNat% 115))
 (.leaf (certNat% 116)))))
 (.branch 38
 (.branch 36
 (.leaf (certNat% 117))
 (.branch 37
 (.leaf (certNat% 118))
 (.leaf (certNat% 119))))
 (.branch 39
 (.leaf (certNat% 120))
 (.branch 40
 (.leaf (certNat% 121))
 (.leaf (certNat% 122))))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 2
 (.branch 1
 (.leaf [0,1,189,357,766,892,1025,1166,1394,1625,5348])
 (.leaf [0,107,184,212,414,645,765,900,1004,1118,5893]))
 (.branch 3
 (.leaf [0,35,116,258,338,395,767,857,968,1131,5897])
 (.branch 4
 (.leaf [0,35,128,246,340,408,766,859,1010,1571,6972])
 (.leaf [0,71,172,248,402,614,948,967,1478,7131]))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 0 0 0 0 1 0 4 4
cert_nodeTest_5 48 01
cert_nodeTest_sound_4 48 01
cert_leafTest_4 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0243
