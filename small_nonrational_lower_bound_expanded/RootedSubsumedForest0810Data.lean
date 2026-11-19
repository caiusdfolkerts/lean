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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0810
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 601
abbrev leafCount : Nat := 4
cert_widths_3 12 10 9 2
cert_blocks_13
cert_counterTable_4
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 2
 (.branch 1
 (.leaf [0,8,140,162,251,402,448,599,815])
 (.leaf [0,22,154,163,250,817,1569]))
 (.branch 3
 (.leaf [0,136,163,251,616,725,811,1558])
 (.leaf [0,88,161,249,506,562,650,751,1073,1569])))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 1 0 0 0 0 0 4 4
cert_nodeTest_4 288 05
cert_nodeTest_sound_3 288 05
cert_leafTest_5 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0810
