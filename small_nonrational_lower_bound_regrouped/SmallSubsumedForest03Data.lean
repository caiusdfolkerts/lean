module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import RootedSmallCacheData
public import RootedSmallGeneratorWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import SmallSubsumedForest03Packed000
public import SmallSubsumedForest03Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 10402
abbrev leafCount : Nat := 5
cert_widths_4 14 3
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 50
 nodeBlocks000
 nodeBlocks001)
def counterTable : Table Nat :=
(.branch 50
 nodeCounters000
 nodeCounters001)
cert_codes_4
cert_counters_4
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)
def leafTable : Table (List Nat) :=
(.branch 2
 (.branch 1
 (.leaf [0,1,404,462,631,822,1638,1832,2571,3035,3068])
 (.leaf [0,1,336,687,822,1124,1706,1841,2161,3148,3273]))
 (.branch 3
 (.leaf [0,1,336,631,822,1548,1638,1841,2568,3050,3159])
 (.branch 4
 (.leaf [0,61,180,312,679,843,1686,1858,2486,2497,3142])
 (.leaf [0,41,214,410,675,810,1551,1717,1857,3143,3191]))))
def rawLeaves := leafTable.get
cert_leaves_4
cert_quota_5 1 2 7
cert_nodeTest_6
cert_nodeTest_sound_5
cert_leafTest_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest03
