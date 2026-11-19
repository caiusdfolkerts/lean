module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0770
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 2
abbrev leafCount : Nat := 1
cert_widths_3 12 1 9 1
cert_blocks_8 0x24028c920a2260284b40a000040000006e000100000000006e3800002 0x4c00000000
cert_counterTable_12 0x80000000008001
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
cert_leafTable_3
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 2 0 0 0 0 0 0 0 1 6
cert_nodeTest_4 288 05
cert_nodeTest_sound_3 288 05
cert_leafTest_5 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0770
