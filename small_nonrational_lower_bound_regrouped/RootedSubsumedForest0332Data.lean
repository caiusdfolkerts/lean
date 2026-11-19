module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSixBase00GrowthCacheData
public import RootedSixBase00FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0332Packed000
public import RootedSubsumedForest0332Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0332
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 21976
abbrev nodeCount : Nat := 10669
abbrev leafCount : Nat := 5
cert_widths_3 15 14 7 3
cert_blocks_10
cert_counterTable_11
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 2
 (.branch 1
 (.leaf [0,1,96,215,383,639,815,1097,1241,1452,1717])
 (.leaf [0,1,66,215,359,638,840,1204,1518,1716,1825]))
 (.branch 3
 (.leaf [0,16,86,130,251,639,841,1030,1046,1261,1515,1850])
 (.branch 4
 (.leaf [0,15,125,143,203,686,831,1025,1045,1214,1533,1699])
 (.leaf [0,15,65,131,215,674,842,1030,1205,1482,1825]))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 0 0 0 0 0 0 2 7
cert_nodeTest_5 96 00
cert_nodeTest_sound_4 96 00
cert_leafTest_4 00
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0332
