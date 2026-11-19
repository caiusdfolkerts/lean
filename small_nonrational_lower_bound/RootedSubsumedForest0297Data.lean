module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSixBase00GrowthCacheData
public import RootedSixBase00FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0297Packed000
public import RootedSubsumedForest0297Packed001
public import RootedSubsumedForest0297Packed002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0297
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 21976
abbrev nodeCount : Nat := 18616
abbrev leafCount : Nat := 18
cert_widths_3 15 15 7 5
cert_blocks_11
cert_counterTable_3
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,1,76,235,391,659,743,844,1509,11355])
 (.leaf [0,3,69,214,394,632,739,788,1075,1508,1681,12063]))
 (.branch 3
 (.leaf [0,34,75,182,245,420,647,1074,1497,10376])
 (.leaf [0,2,97,259,415,675,839,1112,1268])))
 (.branch 6
 (.branch 5
 (.leaf [0,31,75,199,240,365,488,647,842,1055,1507,11555])
 (.leaf [0,1,16,209,636,790,1099,1264,1522,1825,6208]))
 (.branch 7
 (.leaf [0,1,69,217,394,474,632,788,1075,1508,1681,12063])
 (.branch 8
 (.leaf [0,1,69,217,414,479,594,632,788,1060,1508,12074])
 (.leaf [0,2,15,204,680,836,1060,1266,1531,1716,6208])))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf [0,2,65,247,403,848,1164,1230,1495,9682])
 (.leaf [0,5,36,186,320,376,510,1066,1239,1476,1842,10202]))
 (.branch 12
 (.leaf [0,35,61,130,272,352,410,797,1104,1487,1858,11783])
 (.leaf [0,39,70,181,202,426,592,644,800,1048,1507,12075])))
 (.branch 15
 (.branch 14
 (.leaf [0,15,36,186,225,336,466,1057,1202,1511,1842,10419])
 (.leaf [0,31,38,201,204,353,375,834,1045,1524,1855,11894]))
 (.branch 16
 (.leaf [0,15,36,225,838,932,1060,1257,1437,1527,6763])
 (.branch 17
 (.leaf [0,15,19,177,249,537,692,848,1085,1164,1519,11855])
 (.leaf [0,15,94,237,679,835,1060,1243,1508,1709,7008]))))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 0 0 0 0 1 0 5 3
cert_nodeTest_5 96 00
cert_nodeTest_sound_4 96 00
cert_leafTest_4 00
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0297
