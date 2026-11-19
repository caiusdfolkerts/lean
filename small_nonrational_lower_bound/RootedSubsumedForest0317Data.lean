module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0317Packed000
public import RootedSubsumedForest0317Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 9003
abbrev leafCount : Nat := 12
cert_widths_3 14 14 6 4
cert_blocks_10
cert_counterTable_11
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf [0,2,16,225,666,767,934,1017,1178,1464])
 (.branch 2
 (.leaf [0,16,60,153,237,676,768,1005,1189,1466])
 (.leaf [0,36,100,160,249,390,768,920,1019,1175])))
 (.branch 4
 (.leaf [0,16,36,157,257,579,768,920,1019,1175])
 (.branch 5
 (.leaf [0,31,74,130,226,351,678,1029,1054,15242])
 (.leaf [0,31,74,132,195,382,678,789,1029,15242]))))
 (.branch 9
 (.branch 7
 (.leaf [0,1,221,377,618,1028,1158,1368,14998,15243])
 (.branch 8
 (.leaf [0,1,5,345,642,1005,1180,1368,15127,15230])
 (.leaf [0,111,182,214,362,585,984,1164,1419,15065,15239])))
 (.branch 10
 (.leaf [0,9,155,219,411,594,611,1033,1161,15187,15232])
 (.branch 11
 (.leaf [0,1,39,197,353,652,848,1019,15216,15244])
 (.leaf [0,5,45,125,355,652,848,1019,15216,15244])))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 2 0 0 0 0 0 5 2
cert_nodeTest_5 48 01
cert_nodeTest_sound_4 48 01
cert_leafTest_4 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
