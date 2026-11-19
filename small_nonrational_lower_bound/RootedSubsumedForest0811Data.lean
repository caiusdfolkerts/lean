module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0811
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2300
abbrev nodeCount : Nat := 122
abbrev leafCount : Nat := 1
cert_widths_3 12 7 8 1
cert_blocks_6
cert_counterTable_6
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
cert_leafTable_3
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 1 0 0 0 0 0 0 0 2 7
cert_nodeTest_4 240 06
cert_nodeTest_sound_3 240 06
cert_leafTest_5 06
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0811
