module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSixBase00GrowthCacheData
public import RootedSixBase00FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0308Packed000
public import RootedSubsumedForest0308Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 21976
abbrev nodeCount : Nat := 12098
abbrev leafCount : Nat := 4
cert_widths_3 15 14 7 2
cert_blocks_10
cert_counterTable_11
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 2
 (.branch 1
 (.leaf [0,1,15,203,627,816,1077,1245,1528,1715,21821])
 (.leaf [0,2,5,276,360,666,795,1101,1532,1711,21946]))
 (.branch 3
 (.leaf [0,1,6,276,365,638,818,1233,1522,1823,21874])
 (.leaf [0,2,45,202,395,625,1105,1243,1496,1715,21917])))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 1 0 0 0 0 0 3 5
cert_nodeTest_5 96 00
cert_nodeTest_sound_4 96 00
cert_leafTest_4 00
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
