module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixExtra05GrowthCacheData
public import RootedSixExtra05FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0859
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 1130
abbrev leafCount : Nat := 8
cert_widths_3 12 11 9 3
def blocks : Table PackedRawNatGrowth.Block :=
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
def counterTable : Table Nat :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 18))
 (.leaf (certNat% 19)))
 (.branch 3
 (.leaf (certNat% 20))
 (.leaf (certNat% 21))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 22))
 (.leaf (certNat% 23)))
 (.branch 7
 (.leaf (certNat% 24))
 (.branch 8
 (.leaf (certNat% 25))
 (.leaf (certNat% 26))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,17,18,137,162,167,249,448,599,706,812,910])
 (.leaf [0,17,152,161,167,251,385,448,603,815,826]))
 (.branch 3
 (.leaf [0,22,38,152,162,251,448,815])
 (.leaf [0,8,14,137,162,250,448,599,708,812])))
 (.branch 6
 (.branch 5
 (.leaf [0,23,87,128,163,188,250,381,447,599,816])
 (.leaf [0,23,39,104,163,192,250,402,447,599,816]))
 (.branch 7
 (.leaf [0,8,140,162,251,402,448,599,815])
 (.leaf [0,4,56,163,251,448]))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 0 0 0 0 0 0 3 7
cert_nodeTest_4 288 05
cert_nodeTest_sound_3 288 05
cert_leafTest_5 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0859
