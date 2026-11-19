module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public meta import CertificateNumbers
public import RootedSevenMixed032GrowthCacheData
public import IdentityRawMaps
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0032
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 529
abbrev nodeCount : Nat := 277
abbrev leafCount : Nat := 1
cert_widths_2 10 9 1
cert_blocks_3
cert_counterTable_2
cert_codes_2
cert_counters_2
cert_rawNodes_2
cert_leafTable_2
cert_rawLeaves_2
cert_leaves_2
cert_quota_2 0 1 5 3
cert_nodeTest_3 032
cert_nodeTest_sound 032
cert_leafTest_3 032
end Papers.RationalityTen.RootedForests.RootedRawForest0032
