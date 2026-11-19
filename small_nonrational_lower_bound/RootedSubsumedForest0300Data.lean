module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSixBase00GrowthCacheData
public import RootedSixBase00FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0300Packed000
public import RootedSubsumedForest0300Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0300
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 21976
abbrev nodeCount : Nat := 7917
abbrev leafCount : Nat := 6
cert_widths_3 15 13 7 3
cert_blocks_10
cert_counterTable_11
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 3
 (.branch 1
 (.leaf [0,5,76,151,381,659,795,1113,1435,1523,1617])
 (.branch 2
 (.leaf [0,5,76,151,381,659,795,1103,1197,1532,1809])
 (.leaf [0,2,97,259,415,675,839,1112,1268])))
 (.branch 4
 (.leaf [0,1,46,235,391,651,926,1010,1112,1268,1505])
 (.branch 5
 (.leaf [0,1,5,359,656,812,1084,1266,1450,1531,1715])
 (.leaf [0,35,45,152,224,394,1096,1231,1452,1496,1717]))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 0 0 1 0 0 0 6 2
cert_nodeTest_5 96 00
cert_nodeTest_sound_4 96 00
cert_leafTest_4 00
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0300
