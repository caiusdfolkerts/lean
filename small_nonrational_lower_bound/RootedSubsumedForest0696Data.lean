module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0696Packed000
public import RootedSubsumedForest0696Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0696
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 12131
abbrev leafCount : Nat := 15
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
 (.leaf [0,2,100,227,346,413,598,754,1029,1294])
 (.branch 2
 (.leaf [0,2,43,243,347,412,581,850,1028,1293])
 (.leaf [0,1,5,344,599,649,767,826,965,1242,1608])))
 (.branch 5
 (.branch 4
 (.leaf [0,1,5,344,544,756,806,975,1297,1356,1608])
 (.leaf [0,1,5,344,542,710,1021,1071,1298,1357,1608]))
 (.branch 6
 (.leaf [0,2,43,225,345,612,692,1014,1298,1378])
 (.leaf [0,6,79,116,345,554,703,1028,1063,1235,1549]))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf [0,2,59,188,345,607,642,712,968,1175,1233])
 (.leaf [0,17,57,117,215,347,584,712,992,1134,1257]))
 (.branch 10
 (.leaf [0,31,42,128,224,346,997,1094,1286,1380,4530])
 (.leaf [0,42,80,179,232,347,514,582,1016,1281])))
 (.branch 13
 (.branch 12
 (.leaf [0,31,42,128,224,346,887,957,997,1094,4670])
 (.leaf [0,41,77,162,215,275,347,398,546,992,1257]))
 (.branch 14
 (.leaf [0,38,41,164,212,347,558,949,992,1214,1257])
 (.leaf [0,33,43,186,258,347,1028,1293])))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 0 0 1 0 0 0 5 3
cert_nodeTest_5 96 03
cert_nodeTest_sound_4 96 03
cert_leafTest_4 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0696
