module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0698
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 5256
abbrev leafCount : Nat := 3
cert_widths_3 13 13 7 2
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
 (.branch 31
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
 (.branch 28
 (.branch 27
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩)
 (.leaf ⟨((certNat% 54)),(certNat% 55)⟩))
 (.branch 29
 (.leaf ⟨((certNat% 56)),(certNat% 57)⟩)
 (.branch 30
 (.leaf ⟨((certNat% 58)),(certNat% 59)⟩)
 (.leaf ⟨((certNat% 60)),(certNat% 61)⟩)))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf ⟨((certNat% 62)),(certNat% 63)⟩)
 (.leaf ⟨((certNat% 64)),(certNat% 65)⟩))
 (.branch 34
 (.leaf ⟨((certNat% 66)),(certNat% 67)⟩)
 (.branch 35
 (.leaf ⟨((certNat% 68)),(certNat% 69)⟩)
 (.leaf ⟨((certNat% 70)),(certNat% 71)⟩))))
 (.branch 39
 (.branch 37
 (.leaf ⟨((certNat% 72)),(certNat% 73)⟩)
 (.branch 38
 (.leaf ⟨((certNat% 74)),(certNat% 75)⟩)
 (.leaf ⟨((certNat% 76)),(certNat% 77)⟩)))
 (.branch 40
 (.leaf ⟨((certNat% 78)),(certNat% 79)⟩)
 (.branch 41
 (.leaf ⟨((certNat% 80)),(certNat% 81)⟩)
 (.leaf ⟨(certNat% 82),(certNat% 83)⟩)))))))
def counterTable : Table Nat :=
(.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 84))
 (.leaf (certNat% 85)))
 (.branch 3
 (.leaf (certNat% 86))
 (.branch 4
 (.leaf (certNat% 87))
 (.leaf (certNat% 88)))))
 (.branch 7
 (.branch 6
 (.leaf (certNat% 89))
 (.leaf (certNat% 90)))
 (.branch 8
 (.leaf (certNat% 91))
 (.branch 9
 (.leaf (certNat% 92))
 (.leaf (certNat% 93))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (certNat% 94))
 (.leaf (certNat% 95)))
 (.branch 13
 (.leaf (certNat% 96))
 (.branch 14
 (.leaf (certNat% 97))
 (.leaf (certNat% 98)))))
 (.branch 18
 (.branch 16
 (.leaf (certNat% 99))
 (.branch 17
 (.leaf (certNat% 100))
 (.leaf (certNat% 101))))
 (.branch 19
 (.leaf (certNat% 102))
 (.branch 20
 (.leaf (certNat% 103))
 (.leaf (certNat% 104)))))))
 (.branch 31
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf (certNat% 105))
 (.leaf (certNat% 106)))
 (.branch 24
 (.leaf (certNat% 107))
 (.branch 25
 (.leaf (certNat% 108))
 (.leaf (certNat% 109)))))
 (.branch 28
 (.branch 27
 (.leaf (certNat% 110))
 (.leaf (certNat% 111)))
 (.branch 29
 (.leaf (certNat% 112))
 (.branch 30
 (.leaf (certNat% 113))
 (.leaf (certNat% 114))))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf (certNat% 115))
 (.leaf (certNat% 116)))
 (.branch 34
 (.leaf (certNat% 117))
 (.branch 35
 (.leaf (certNat% 118))
 (.leaf (certNat% 119)))))
 (.branch 39
 (.branch 37
 (.leaf (certNat% 120))
 (.branch 38
 (.leaf (certNat% 121))
 (.leaf (certNat% 122))))
 (.branch 40
 (.leaf (certNat% 123))
 (.branch 41
 (.leaf (certNat% 124))
 (.leaf (certNat% 125))))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 1
 (.leaf [0,32,43,164,248,347,922,1012,1289])
 (.branch 2
 (.leaf [0,1,6,262,385,556,736,988,1286,1610,4992])
 (.leaf [0,1,57,204,406,544,735,988,1298,1609,4996])))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 1 0 0 0 0 0 2 6
cert_nodeTest_5 96 03
cert_nodeTest_sound_4 96 03
cert_leafTest_4 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0698
