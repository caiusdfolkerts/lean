module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0304Packed000
public import RootedSubsumedForest0304Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0304
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 12127
abbrev leafCount : Nat := 20
cert_widths_3 14 14 6 5
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
 (.leaf [0,6,71,171,412,578,626,762,765,775,979])
 (.leaf [0,6,35,173,403,724,765,796,1028,1133,1440]))
 (.branch 3
 (.leaf [0,7,88,160,390,614,765,776,1017,1145,1420])
 (.branch 4
 (.leaf [0,7,72,185,415,662,766,838,1015])
 (.leaf [0,1,5,345,622,765,1017,1185,1365,1420,1550]))))
 (.branch 7
 (.branch 6
 (.leaf [0,5,71,174,296,412,557,614,765,979,1365])
 (.leaf [0,5,35,119,401,537,765,1028,1133,1365,1440]))
 (.branch 8
 (.leaf [0,45,71,184,236,414,626,765,948,979,1478])
 (.branch 9
 (.leaf [0,45,71,176,244,400,626,765,948,967,1369])
 (.leaf [0,16,52,175,247,638,767,819,983,1061,1139])))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf [0,2,16,225,666,767,934,1017,1178,1464])
 (.leaf [0,15,57,117,213,652,768,903,995,1151,1206]))
 (.branch 13
 (.leaf [0,16,60,153,237,676,768,1005,1189,1466])
 (.branch 14
 (.leaf [0,53,87,162,213,275,361,614,768,995,1151])
 (.leaf [0,36,100,160,249,390,768,920,1019,1175]))))
 (.branch 17
 (.branch 16
 (.leaf [0,51,61,176,220,376,650,765,947,1123,1368])
 (.leaf [0,59,62,129,197,353,676,766,882,1122,1248]))
 (.branch 18
 (.leaf [0,57,61,152,208,364,666,765,890,1147,1367])
 (.branch 19
 (.leaf [0,16,36,157,257,579,768,920,1019,1175])
 (.leaf [0,31,53,135,385,632,768,1011,1156,1545,1619,14496]))))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 0 0 1 0 0 0 5 3
cert_nodeTest_5 48 01
cert_nodeTest_sound_4 48 01
cert_leafTest_4 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0304
