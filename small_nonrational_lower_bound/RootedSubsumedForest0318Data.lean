module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0318Packed000
public import RootedSubsumedForest0318Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0318
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 9817
abbrev leafCount : Nat := 21
cert_widths_3 13 14 6 5
cert_blocks_10
cert_counterTable_11
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf [0,2,60,223,331,529,599,677,1044,1335])
 (.leaf [0,7,61,169,333,481,528,610,656,1042]))
 (.branch 3
 (.leaf [0,6,60,141,332,483,528,664,1056,1333])
 (.branch 4
 (.leaf [0,56,60,138,235,332,528,665,1056,1333])
 (.leaf [0,7,62,163,332,530,682,1058]))))
 (.branch 7
 (.branch 6
 (.leaf [0,6,74,151,331,530,660,854,944,1050])
 (.leaf [0,6,92,151,331,530,685,765,944,1029]))
 (.branch 8
 (.leaf [0,56,74,163,210,332,530,670,943,1046])
 (.branch 9
 (.leaf [0,18,56,151,214,332,530,682,946,1058])
 (.leaf [0,18,74,163,212,331,530,682,950,1058])))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf [0,19,69,139,225,333,529,655,954,1135])
 (.leaf [0,2,86,211,331,528,684,850,1040]))
 (.branch 13
 (.leaf [0,6,154,333,482,530,660,854,1051])
 (.branch 14
 (.leaf [0,6,141,332,483,672,961,1053,8052])
 (.leaf [0,6,38,139,331,850,959,1038,8056]))))
 (.branch 18
 (.branch 16
 (.leaf [0,2,18,217,332,961,1058,7994,8052])
 (.branch 17
 (.leaf [0,3,57,188,330,335,611,682,1076,8055,8080])
 (.leaf [0,6,12,169,333,488,655,1055,8058])))
 (.branch 19
 (.leaf [0,6,38,142,497,850,1039,7900,8056])
 (.branch 20
 (.leaf [0,2,37,179,366,475,563,828,1003,7901,8057])
 (.leaf [0,1,67,177,371,589,630,1098,1311,7898,8058]))))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 2 0 0 0 0 0 4 3
cert_nodeTest_5 48 02
cert_nodeTest_sound_4 48 02
cert_leafTest_4 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0318
