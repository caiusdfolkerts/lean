module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSixExtra03GrowthCacheData
public import RootedSixExtra03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0802
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3150
abbrev nodeCount : Nat := 2
abbrev leafCount : Nat := 1
cert_widths_3 12 1 7 1
cert_blocks_8 0x3279d3079c0279b0079a387993479808797047963a795367940a7930679254791487902478f1878e5678d4a78c2678b1a78a5c789507882c78720786001800000076000100000079ac26f341 0x4000000000
cert_counterTable_12 0x80200000000000
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
cert_leafTable_3
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 1 0 0 0 0 0 0 8
cert_nodeTest_4 96 03
cert_nodeTest_sound_3 96 03
cert_leafTest_5 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0802
