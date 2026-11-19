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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0854
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 626
abbrev leafCount : Nat := 7
cert_widths_3 12 10 9 3
cert_blocks_13
cert_counterTable_4
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 3
 (.branch 1
 (.leaf [0,22,154,163,250,817,1569])
 (.branch 2
 (.leaf [0,4,56,163,251,448])
 (.leaf [0,1,72,160,248,445,793,875,938,1512])))
 (.branch 5
 (.branch 4
 (.leaf [0,1,87,160,248,445,838,965,1053,1590])
 (.leaf [0,17,34,248,289,445,507,944,1074,1276,1404,1588]))
 (.branch 6
 (.leaf [0,3,56,1410,1506,1566])
 (.leaf [0,1,53,179,310,486,838,965,1053,1405,1508,1564]))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 3 0 0 0 0 0 6 0
cert_nodeTest_4 288 05
cert_nodeTest_sound_3 288 05
cert_leafTest_5 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0854
