module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public meta import CertificateNumbers
public import RootedSevenPure029GrowthCacheData
public import IdentityRawMaps
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0063
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 406
abbrev nodeCount : Nat := 322
abbrev leafCount : Nat := 18
cert_widths_2 9 9 5
cert_blocks_3
cert_counterTable_2
cert_codes_2
cert_counters_2
cert_rawNodes_2
def leafTable : Table (List Nat) :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,4,37,62,87,106,153,193,250,335])
 (.leaf [0,16,37,63,86,106,152,181,238,336]))
 (.branch 3
 (.leaf [0,2,37,61,107,132,153,191,257,328])
 (.leaf [0,5,37,62,87,107,132,188,260,338])))
 (.branch 6
 (.branch 5
 (.leaf [0,14,37,61,108,131,152,179,258,316])
 (.leaf [0,17,37,63,86,108,131,176,259,337]))
 (.branch 7
 (.leaf [0,6,38,61,87,106,132,200,248,326])
 (.branch 8
 (.leaf [0,1,38,62,106,132,153,203,245,340])
 (.leaf [0,3,38,61,87,107,153,205,262,323])))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf [0,28,38,63,85,107,151,180,237,324])
 (.leaf [0,26,38,62,108,130,151,178,246,315]))
 (.branch 12
 (.leaf [0,29,38,63,85,108,130,177,247,325])
 (.leaf [0,18,39,61,86,106,131,201,236,314])))
 (.branch 15
 (.branch 14
 (.leaf [0,13,39,63,106,131,152,202,233,339])
 (.leaf [0,30,39,62,85,107,130,189,235,313]))
 (.branch 16
 (.leaf [0,25,39,63,107,130,151,190,234,327])
 (.branch 17
 (.leaf [0,15,39,61,86,108,152,204,261,311])
 (.leaf [0,27,39,62,85,108,151,192,249,312]))))))
cert_rawLeaves_2
cert_leaves_2
cert_quota_2 0 0 4 5
cert_nodeTest_2 029
cert_nodeTest_sound_2 029
cert_leafTest_2 029
end Papers.RationalityTen.RootedForests.RootedRawForest0063
