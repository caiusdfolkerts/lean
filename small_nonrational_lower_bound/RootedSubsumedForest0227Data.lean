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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0227
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 21976
abbrev nodeCount : Nat := 3831
abbrev leafCount : Nat := 1
cert_widths_3 15 12 7 1
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.branch 2
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩)
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨((certNat% 6)),(certNat% 7)⟩)
 (.leaf ⟨((certNat% 8)),(certNat% 9)⟩))
 (.branch 6
 (.leaf ⟨((certNat% 10)),(certNat% 11)⟩)
 (.leaf ⟨((certNat% 12)),(certNat% 13)⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩))
 (.branch 10
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩))
 (.branch 14
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩))
 (.branch 21
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩)
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩))
 (.branch 25
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩)
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩)
 (.leaf ⟨((certNat% 54)),(certNat% 55)⟩))
 (.branch 29
 (.leaf ⟨((certNat% 56)),(certNat% 57)⟩)
 (.leaf ⟨((certNat% 58)),(certNat% 59)⟩))))))
def counterTable : Table Nat :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (certNat% 60))
 (.branch 2
 (.leaf (certNat% 61))
 (.leaf (certNat% 62))))
 (.branch 5
 (.branch 4
 (.leaf (certNat% 63))
 (.leaf (certNat% 64)))
 (.branch 6
 (.leaf (certNat% 65))
 (.leaf (certNat% 66)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (certNat% 67))
 (.leaf (certNat% 68)))
 (.branch 10
 (.leaf (certNat% 69))
 (.leaf (certNat% 70))))
 (.branch 13
 (.branch 12
 (.leaf (certNat% 71))
 (.leaf (certNat% 72)))
 (.branch 14
 (.leaf (certNat% 73))
 (.leaf (certNat% 74))))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf (certNat% 75))
 (.branch 17
 (.leaf (certNat% 76))
 (.leaf (certNat% 77))))
 (.branch 20
 (.branch 19
 (.leaf (certNat% 78))
 (.leaf (certNat% 79)))
 (.branch 21
 (.leaf (certNat% 80))
 (.leaf (certNat% 81)))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf (certNat% 82))
 (.leaf (certNat% 83)))
 (.branch 25
 (.leaf (certNat% 84))
 (.leaf (certNat% 85))))
 (.branch 28
 (.branch 27
 (.leaf (certNat% 86))
 (.leaf (certNat% 87)))
 (.branch 29
 (.leaf (certNat% 88))
 (.leaf (certNat% 89)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
cert_leafTable_3
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 0 0 0 0 0 1 4 4
cert_nodeTest_5 96 00
cert_nodeTest_sound_4 96 00
cert_leafTest_4 00
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0227
