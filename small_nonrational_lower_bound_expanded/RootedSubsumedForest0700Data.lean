module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0700Packed000
public import RootedSubsumedForest0700Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0700
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 12382
abbrev leafCount : Nat := 14
cert_widths_3 13 14 7 4
cert_blocks_10
cert_counterTable_11
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf [0,1,15,195,345,556,768,964,1278,1612,4868])
 (.branch 2
 (.leaf [0,2,42,239,347,412,578,1027,1274,1382])
 (.leaf [0,2,83,239,347,412,586,742,1027,1365])))
 (.branch 5
 (.branch 4
 (.leaf [0,1,61,189,344,556,740,940,1336,1549,5233])
 (.leaf [0,1,61,189,344,650,742,1175,1242,1470,5089]))
 (.branch 6
 (.leaf [0,32,60,164,248,347,735,1009,1117,1292])
 (.leaf [0,1,57,209,544,756,850,985,1290,1607,4978]))))
 (.branch 10
 (.branch 8
 (.leaf [0,6,36,161,568,748,949,976,1274,1613,4988])
 (.branch 9
 (.leaf [0,2,31,196,426,472,615,722,976,1297,1602,4997])
 (.leaf [0,1,77,219,405,542,732,1000,1297,1609,4997])))
 (.branch 12
 (.branch 11
 (.leaf [0,1,197,406,452,544,734,988,1298,1609,4996])
 (.leaf [0,1,195,352,511,554,708,1033,1277,1607,4994]))
 (.branch 13
 (.leaf [0,5,62,132,490,582,700,940,1113,1257,1530,4994])
 (.leaf [0,1,31,219,375,515,732,988,1117,1291,4986])))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 1 0 0 0 0 0 4 4
cert_nodeTest_5 96 03
cert_nodeTest_sound_4 96 03
cert_leafTest_4 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0700
