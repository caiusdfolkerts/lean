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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0278
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 4728
abbrev leafCount : Nat := 1
cert_widths_3 14 13 6 1
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 18
 (.branch 9
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
 (.branch 8
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩))
 (.branch 12
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩))
 (.branch 16
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩))
 (.branch 21
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩)
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩))
 (.branch 25
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩)
 (.branch 26
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩)
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨((certNat% 54)),(certNat% 55)⟩)
 (.leaf ⟨((certNat% 56)),(certNat% 57)⟩))
 (.branch 30
 (.leaf ⟨((certNat% 58)),(certNat% 59)⟩)
 (.branch 31
 (.leaf ⟨((certNat% 60)),(certNat% 61)⟩)
 (.leaf ⟨((certNat% 62)),(certNat% 63)⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨((certNat% 64)),(certNat% 65)⟩)
 (.leaf ⟨((certNat% 66)),(certNat% 67)⟩))
 (.branch 35
 (.leaf ⟨((certNat% 68)),(certNat% 69)⟩)
 (.branch 36
 (.leaf ⟨((certNat% 70)),(certNat% 71)⟩)
 (.leaf ⟨((certNat% 72)),(certNat% 73)⟩)))))))
def counterTable : Table Nat :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 74))
 (.leaf (certNat% 75)))
 (.branch 3
 (.leaf (certNat% 76))
 (.leaf (certNat% 77))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 78))
 (.leaf (certNat% 79)))
 (.branch 7
 (.leaf (certNat% 80))
 (.branch 8
 (.leaf (certNat% 81))
 (.leaf (certNat% 82))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (certNat% 83))
 (.leaf (certNat% 84)))
 (.branch 12
 (.leaf (certNat% 85))
 (.leaf (certNat% 86))))
 (.branch 15
 (.branch 14
 (.leaf (certNat% 87))
 (.leaf (certNat% 88)))
 (.branch 16
 (.leaf (certNat% 89))
 (.branch 17
 (.leaf (certNat% 90))
 (.leaf (certNat% 91)))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf (certNat% 92))
 (.leaf (certNat% 93)))
 (.branch 21
 (.leaf (certNat% 94))
 (.leaf (certNat% 95))))
 (.branch 24
 (.branch 23
 (.leaf (certNat% 96))
 (.leaf (certNat% 97)))
 (.branch 25
 (.leaf (certNat% 98))
 (.branch 26
 (.leaf (certNat% 99))
 (.leaf (certNat% 100))))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf (certNat% 101))
 (.leaf (certNat% 102)))
 (.branch 30
 (.leaf (certNat% 103))
 (.branch 31
 (.leaf (certNat% 104))
 (.leaf (certNat% 105)))))
 (.branch 34
 (.branch 33
 (.leaf (certNat% 106))
 (.leaf (certNat% 107)))
 (.branch 35
 (.leaf (certNat% 108))
 (.branch 36
 (.leaf (certNat% 109))
 (.leaf (certNat% 110))))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
cert_leafTable_3
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 1 0 0 0 1 0 5 2
cert_nodeTest_5 48 01
cert_nodeTest_sound_4 48 01
cert_leafTest_4 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0278
