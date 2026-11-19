module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSixBase04GrowthCacheData
public import RootedSixBase04FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0707Packed000
public import RootedSubsumedForest0707Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2824
abbrev nodeCount : Nat := 10223
abbrev leafCount : Nat := 18
cert_widths_3 12 14 11 5
cert_blocks_10
cert_counterTable_11
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,1,41,48,206,374,557,867,934,990,1267,2818])
 (.leaf [0,1,25,46,215,383,909,930,977,1254,1595,2821]))
 (.branch 3
 (.leaf [0,2,17,55,202,495,557,814,890,1267,1658,2818])
 (.leaf [0,1,6,17,297,439,557,807,990,1267,1462,2818])))
 (.branch 6
 (.branch 5
 (.leaf [0,1,41,48,218,362,556,884,1002,1194,1255,2820])
 (.leaf [0,1,25,46,227,371,864,989,1198,1242,1594,2823]))
 (.branch 7
 (.leaf [0,5,41,48,134,398,533,926,966,1188,1267,2812])
 (.branch 8
 (.leaf [0,5,41,48,189,311,398,533,966,1267,1440,2812])
 (.leaf [0,8,16,47,177,357,568,1001,1243,2822])))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf [0,25,41,48,172,216,360,933,1002,1255,1552,2820])
 (.leaf [0,5,9,77,175,405,518,842,966,1185,1510,2705]))
 (.branch 12
 (.leaf [0,5,10,76,172,409,542,766,825,954,1521,2709])
 (.leaf [0,5,10,76,172,409,545,758,825,954,1808,2813])))
 (.branch 15
 (.branch 14
 (.leaf [0,18,41,55,149,205,496,569,802,1266,1637,2819])
 (.leaf [0,5,40,46,134,413,530,765,942,1259,1534,2706]))
 (.branch 16
 (.leaf [0,15,43,56,144,260,354,544,817,1219,1699,2816])
 (.branch 17
 (.leaf [0,25,41,48,189,216,355,360,1002,1255,1552,2820])
 (.leaf [0,5,16,137,521,790,948,1249,1536,1850,2550]))))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 3 1 0 0 0 0 0 5 3
cert_nodeTest_5 1152 04
cert_nodeTest_sound_4 1152 04
cert_leafTest_4 04
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
