module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixExtra06GrowthCacheData
public import RootedSixExtra06FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0836
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2300
abbrev nodeCount : Nat := 3528
abbrev leafCount : Nat := 3
cert_widths_3 12 12 8 2
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 14
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
 (.branch 10
 (.branch 8
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)
 (.branch 9
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩)
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩))
 (.branch 13
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)
 (.branch 16
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩))
 (.branch 20
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩)
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩)
 (.branch 23
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩)
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩)
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩))
 (.branch 27
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩)
 (.leaf ⟨(certNat% 54),(certNat% 55)⟩))))))
def counterTable : Table Nat :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (certNat% 56))
 (.branch 2
 (.leaf (certNat% 57))
 (.leaf (certNat% 58))))
 (.branch 5
 (.branch 4
 (.leaf (certNat% 59))
 (.leaf (certNat% 60)))
 (.branch 6
 (.leaf (certNat% 61))
 (.leaf (certNat% 62)))))
 (.branch 10
 (.branch 8
 (.leaf (certNat% 63))
 (.branch 9
 (.leaf (certNat% 64))
 (.leaf (certNat% 65))))
 (.branch 12
 (.branch 11
 (.leaf (certNat% 66))
 (.leaf (certNat% 67)))
 (.branch 13
 (.leaf (certNat% 68))
 (.leaf (certNat% 69))))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf (certNat% 70))
 (.branch 16
 (.leaf (certNat% 71))
 (.leaf (certNat% 72))))
 (.branch 19
 (.branch 18
 (.leaf (certNat% 73))
 (.leaf (certNat% 74)))
 (.branch 20
 (.leaf (certNat% 75))
 (.leaf (certNat% 76)))))
 (.branch 24
 (.branch 22
 (.leaf (certNat% 77))
 (.branch 23
 (.leaf (certNat% 78))
 (.leaf (certNat% 79))))
 (.branch 26
 (.branch 25
 (.leaf (certNat% 80))
 (.leaf (certNat% 81)))
 (.branch 27
 (.leaf (certNat% 82))
 (.leaf (certNat% 83)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 1
 (.leaf [0,1,8,205,290,484,555,749,860,1018,2298])
 (.branch 2
 (.leaf [0,6,12,109,421,543,855,1002,1194,1402,2298])
 (.leaf [0,1,24,182,266,543,855,1002,1194,1402,2298])))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 1 2 0 0 0 0 0 0 2 6
cert_nodeTest_4 240 06
cert_nodeTest_sound_3 240 06
cert_leafTest_5 06
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0836
