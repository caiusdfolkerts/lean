module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public meta import CertificateNumbers
public import RootedSixExtra02GrowthCacheData
public import RootedSixExtra02FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0753
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 6620
abbrev nodeCount : Nat := 9
abbrev leafCount : Nat := 1
cert_widths_3 13 4 6 1
cert_blocks_9
cert_counterTable_6
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
cert_leafTable_3
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 0 0 1 0 0 0 0 0 8
cert_nodeTest_4 48 02
cert_nodeTest_sound_3 48 02
cert_leafTest_5 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0753
