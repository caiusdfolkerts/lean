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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0849
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 1042
abbrev leafCount : Nat := 2
cert_widths_3 12 11 9 1
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
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)))))
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
(.branch 1
 (.leaf [0,22,154,163,250,817,1569])
 (.leaf [0,136,163,251,616,725,811,1558]))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 1 0 0 0 0 0 6 3
cert_nodeTest_4 288 05
cert_nodeTest_sound_3 288 05
cert_leafTest_5 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0849
