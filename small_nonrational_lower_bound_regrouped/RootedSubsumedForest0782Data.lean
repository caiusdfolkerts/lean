module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixExtra01GrowthCacheData
public import RootedSixExtra01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0782
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3150
abbrev nodeCount : Nat := 319
abbrev leafCount : Nat := 1
cert_widths_3 12 9 6 1
cert_blocks_12
cert_counterTable_13
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
cert_leafTable_3
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 2 0 1 0 0 0 0 0 4 2
cert_nodeTest_4 48 01
cert_nodeTest_sound_3 48 01
cert_leafTest_5 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0782
