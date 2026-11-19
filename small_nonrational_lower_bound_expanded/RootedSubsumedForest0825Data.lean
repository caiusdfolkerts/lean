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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0825
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 810
abbrev leafCount : Nat := 6
cert_widths_3 12 10 9 3
def blocks : Table PackedRawNatGrowth.Block :=
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
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩))))
cert_counterTable_9 14 15 16 17 18 19 20
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 3
 (.branch 1
 (.leaf [0,22,154,163,250,817,1569])
 (.branch 2
 (.leaf [0,1,162,173,251,282,402,818,1225,1568])
 (.leaf [0,136,163,251,616,725,811,1558])))
 (.branch 4
 (.leaf [0,1,160,248,545,675,752,1095,1225,1568])
 (.branch 5
 (.leaf [0,124,446,612,721,799,1410,1506])
 (.leaf [0,17,109,201,447,583,772,860,1408,1492]))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 2 0 0 0 0 0 5 2
cert_nodeTest_4 288 05
cert_nodeTest_sound_3 288 05
cert_leafTest_5 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0825
