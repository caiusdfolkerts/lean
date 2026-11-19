module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixBase00GrowthCacheData
public import RootedSixBase00FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0240
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 21976
abbrev nodeCount : Nat := 4405
abbrev leafCount : Nat := 1
cert_widths_3 15 13 7 1
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)
 (.leaf ⟨((certNat% 6)),(certNat% 7)⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨((certNat% 8)),(certNat% 9)⟩)
 (.leaf ⟨((certNat% 10)),(certNat% 11)⟩))
 (.branch 7
 (.leaf ⟨((certNat% 12)),(certNat% 13)⟩)
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩))
 (.branch 11
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩)
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩))
 (.branch 15
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)
 (.branch 16
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩))))))
 (.branch 26
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩))
 (.branch 20
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩)
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩)
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩))
 (.branch 24
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩)
 (.branch 25
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩)
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩)))))
 (.branch 30
 (.branch 28
 (.branch 27
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩)
 (.leaf ⟨((certNat% 54)),(certNat% 55)⟩))
 (.branch 29
 (.leaf ⟨((certNat% 56)),(certNat% 57)⟩)
 (.leaf ⟨((certNat% 58)),(certNat% 59)⟩)))
 (.branch 32
 (.branch 31
 (.leaf ⟨((certNat% 60)),(certNat% 61)⟩)
 (.leaf ⟨((certNat% 62)),(certNat% 63)⟩))
 (.branch 33
 (.leaf ⟨((certNat% 64)),(certNat% 65)⟩)
 (.branch 34
 (.leaf ⟨((certNat% 66)),(certNat% 67)⟩)
 (.leaf ⟨((certNat% 68)),(certNat% 69)⟩)))))))
def counterTable : Table Nat :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 70))
 (.leaf (certNat% 71)))
 (.branch 3
 (.leaf (certNat% 72))
 (.leaf (certNat% 73))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 74))
 (.leaf (certNat% 75)))
 (.branch 7
 (.leaf (certNat% 76))
 (.leaf (certNat% 77)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (certNat% 78))
 (.leaf (certNat% 79)))
 (.branch 11
 (.leaf (certNat% 80))
 (.leaf (certNat% 81))))
 (.branch 14
 (.branch 13
 (.leaf (certNat% 82))
 (.leaf (certNat% 83)))
 (.branch 15
 (.leaf (certNat% 84))
 (.branch 16
 (.leaf (certNat% 85))
 (.leaf (certNat% 86)))))))
 (.branch 26
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf (certNat% 87))
 (.leaf (certNat% 88)))
 (.branch 20
 (.leaf (certNat% 89))
 (.leaf (certNat% 90))))
 (.branch 23
 (.branch 22
 (.leaf (certNat% 91))
 (.leaf (certNat% 92)))
 (.branch 24
 (.leaf (certNat% 93))
 (.branch 25
 (.leaf (certNat% 94))
 (.leaf (certNat% 95))))))
 (.branch 30
 (.branch 28
 (.branch 27
 (.leaf (certNat% 96))
 (.leaf (certNat% 97)))
 (.branch 29
 (.leaf (certNat% 98))
 (.leaf (certNat% 99))))
 (.branch 32
 (.branch 31
 (.leaf (certNat% 100))
 (.leaf (certNat% 101)))
 (.branch 33
 (.leaf (certNat% 102))
 (.branch 34
 (.leaf (certNat% 103))
 (.leaf (certNat% 104))))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
cert_leafTable_3
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 0 1 0 0 0 0 4 4
cert_nodeTest_5 96 00
cert_nodeTest_sound_4 96 00
cert_leafTest_4 00
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0240
