module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0704Packed000
public import RootedSubsumedForest0704Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0704
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 8280
abbrev leafCount : Nat := 10
cert_widths_3 13 14 7 4
cert_blocks_10
cert_counterTable_11
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf [0,2,100,227,346,413,598,754,1029,1294])
 (.leaf [0,2,43,243,347,412,581,850,1028,1293]))
 (.branch 3
 (.leaf [0,2,43,225,345,612,692,1014,1298,1378])
 (.branch 4
 (.leaf [0,42,80,179,232,347,514,582,1016,1281])
 (.leaf [0,33,43,186,258,347,1028,1293]))))
 (.branch 7
 (.branch 6
 (.leaf [0,1,54,221,545,763,947,1009,1295,4927,4982])
 (.leaf [0,31,51,128,257,751,948,973,1283,4928,4994]))
 (.branch 8
 (.leaf [0,1,32,204,406,647,739,957,1016,4996,5235])
 (.branch 9
 (.leaf [0,27,31,119,207,513,720,1134,1293,4990,5209])
 (.leaf [0,2,41,210,277,427,543,1016,1398,4996,5235])))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 2 0 0 0 0 0 5 2
cert_nodeTest_5 96 03
cert_nodeTest_sound_4 96 03
cert_leafTest_4 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0704
