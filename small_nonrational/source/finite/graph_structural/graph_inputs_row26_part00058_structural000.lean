module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00058Frames
public import GraphInputsRow26Part00058Leaves
public import GraphInputsRow26Part00058Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00058.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1b8751b49713cb49d26ab1a66a5a719a6399969595635a4e8791e17ad16c5a9666594e4b9694e565655355352d64d4b61d4745d0f6c368ce3a4d9394cd362e4b8ad2b2ae1b46c9b16d8791cc749ca719e1745c9715e0f43c4f07d2c471a24a9264382e944d1864550b41d90cc328e0b0ac4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36da6d36da6db6da69b69b6da4db4924926d269249b6d24936d2491249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 31), (facetIndex 40), (facetIndex 49), (facetIndex 80), (facetIndex 85)]))
 (.leaf ([(facetIndex 23), (facetIndex 53), (facetIndex 55), (facetIndex 72), (facetIndex 88)])))
 (.branch 3
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 39), (facetIndex 48)]))
 (.leaf ([(facetIndex 45), (facetIndex 59), (facetIndex 60), (facetIndex 66), (facetIndex 70)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 24), (facetIndex 38), (facetIndex 41), (facetIndex 42)]))
 (.leaf ([(facetIndex 21), (facetIndex 51), (facetIndex 52), (facetIndex 54)])))
 (.branch 7
 (.leaf ([(facetIndex 25), (facetIndex 32), (facetIndex 33), (facetIndex 44), (facetIndex 50)]))
 (.leaf ([(facetIndex 22)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "10000000000010c00c000360034db8201e1205000360900343e8000000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 35), (facetIndex 56)]))
 (.leaf ([(facetIndex 71), (facetIndex 73), (facetIndex 74)])))
 (.branch 3
 (.leaf ([(facetIndex 77), (facetIndex 82), (facetIndex 89)]))
 (.branch 4
 (.leaf ([(facetIndex 26), (facetIndex 34), (facetIndex 57), (facetIndex 62), (facetIndex 81)]))
 (.leaf ([(facetIndex 43), (facetIndex 58), (facetIndex 64)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 61), (facetIndex 75), (facetIndex 79), (facetIndex 90), (facetIndex 91)]))
 (.leaf ([(facetIndex 65), (facetIndex 67), (facetIndex 92)])))
 (.branch 8
 (.leaf ([(facetIndex 27), (facetIndex 36), (facetIndex 47), (facetIndex 76), (facetIndex 78), (facetIndex 84)]))
 (.branch 9
 (.leaf ([(facetIndex 37), (facetIndex 83), (facetIndex 86), (facetIndex 87)]))
 (.leaf ([(facetIndex 46), (facetIndex 63), (facetIndex 68), (facetIndex 69)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "6552088078230572751101099606493500430000000007900400000870300000073z1a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00058.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":2}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00058.record001" 52

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00058.record001" "{\"ridges\":[[4,522],[11,536],[24,522],[32,194],[38,536],[41,522],[42,522],[45,592],[51,28],[54,536],[56,588],[59,208],[66,536],[72,28],[74,588],[84,786],[89,28]],\"owners\":[[4,522,[73,74,82,84],[24,38,41,42]],[24,522,[82,84],[4,38,41,42,73,74]],[41,522,[73,74,82,84],[4,24,38,42]],[42,522,[73,84],[4,24,38,41,74,82]],[32,194,[86,87],[6,44,48,50,75,79,81]],[11,536,[73,82,84,89],[38,54,66]],[38,536,[89],[11,54,66,73,82,84]],[54,536,[82,84],[11,38,66,73,89]],[66,536,[73,84],[11,38,54,82,89]],[59,208,[86,87],[12,44,70,75,91]],[45,592,[89],[13,60,66,70,77,82,87]],[56,588,[74,89],[]],[74,588,[56,89],[]],[84,786,[],[]]],\"edges\":[[29,[4,11,24,38,41,42,54,56,66,73,74,82,84,89]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00058.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00058.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-4,-3],[-6,-3],[-6,-4],[-10,-3],[-11,-3],[-11,-4],[-12,-4],[-16,-4],[-16,-5],[-17,-4],[-18,-16],[-19,-9],[-20,-16],[-21,-3],[-21,-16],[-22,-17],[-23,-17],[-23,-19],[-24,-17],[-24,-19],[-25,-15],[-25,-17],[-27,-3],[-27,-26],[-28,-4],[-28,-17],[-28,-19],[-29,-26],[-30,-4],[-30,-7],[-30,-13],[-30,-26],[-32,-30],[-33,-30],[-34,-16],[-35,-4],[-35,-17],[-35,-19],[-1,27,28,30,31],[-6,30,31],[-11,27,28,30,31],[-12,27,31],[-8,32,33],[-16,-26,-35],[-2,27,30,31,35],[-10,35],[-19,30,31],[-24,27,31],[-22,32,33],[-14,35],[-21,28,35],[-28,21,35],[-31],[-36,5,18,20,26,34],[-37,14,22,23,24,25],[-38,6,10,11,12],[-39,3,16,17,19],[-40,7,8,9,13,15],[-41,4],[-42,36],[-43,37],[-44,42],[-44,43],[-45,38,39],[-46,38],[-46,39],[-47,40,41],[-48,41],[-49,45],[-49,46,48],[-49,47],[-50,48],[-51,44,50],[-51,49],[51],[-52,29,30,35],[-30,52],[-35,52],[1,2,6,10,11,12,19,21,24,27,28,30,31,35]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":22,\"b\":21},{\"tag\":\"incompatible\",\"a\":24,\"b\":21},{\"tag\":\"incompatible\",\"a\":24,\"b\":22},{\"tag\":\"incompatible\",\"a\":38,\"b\":21},{\"tag\":\"incompatible\",\"a\":41,\"b\":21},{\"tag\":\"incompatible\",\"a\":41,\"b\":22},{\"tag\":\"incompatible\",\"a\":42,\"b\":22},{\"tag\":\"incompatible\",\"a\":51,\"b\":22},{\"tag\":\"incompatible\",\"a\":51,\"b\":23},{\"tag\":\"incompatible\",\"a\":52,\"b\":22},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":33},{\"tag\":\"incompatible\",\"a\":55,\"b\":51},{\"tag\":\"incompatible\",\"a\":56,\"b\":21},{\"tag\":\"incompatible\",\"a\":56,\"b\":51},{\"tag\":\"incompatible\",\"a\":59,\"b\":52},{\"tag\":\"incompatible\",\"a\":60,\"b\":52},{\"tag\":\"incompatible\",\"a\":60,\"b\":54},{\"tag\":\"incompatible\",\"a\":66,\"b\":52},{\"tag\":\"incompatible\",\"a\":66,\"b\":54},{\"tag\":\"incompatible\",\"a\":70,\"b\":50},{\"tag\":\"incompatible\",\"a\":70,\"b\":52},{\"tag\":\"incompatible\",\"a\":73,\"b\":21},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":22},{\"tag\":\"incompatible\",\"a\":74,\"b\":52},{\"tag\":\"incompatible\",\"a\":74,\"b\":54},{\"tag\":\"incompatible\",\"a\":77,\"b\":72},{\"tag\":\"incompatible\",\"a\":82,\"b\":22},{\"tag\":\"incompatible\",\"a\":82,\"b\":25},{\"tag\":\"incompatible\",\"a\":82,\"b\":44},{\"tag\":\"incompatible\",\"a\":82,\"b\":72},{\"tag\":\"incompatible\",\"a\":86,\"b\":82},{\"tag\":\"incompatible\",\"a\":87,\"b\":82},{\"tag\":\"incompatible\",\"a\":88,\"b\":51},{\"tag\":\"incompatible\",\"a\":89,\"b\":22},{\"tag\":\"incompatible\",\"a\":89,\"b\":52},{\"tag\":\"incompatible\",\"a\":89,\"b\":54},{\"tag\":\"mate\",\"ridge\":522,\"a\":4,\"owners\":[73,74,82,84]},{\"tag\":\"mate\",\"ridge\":522,\"a\":24,\"owners\":[82,84]},{\"tag\":\"mate\",\"ridge\":522,\"a\":41,\"owners\":[73,74,82,84]},{\"tag\":\"mate\",\"ridge\":522,\"a\":42,\"owners\":[73,84]},{\"tag\":\"mate\",\"ridge\":194,\"a\":32,\"owners\":[86,87]},{\"tag\":\"three\",\"ridge\":28,\"vertices\":[51,72,89]},{\"tag\":\"mate\",\"ridge\":536,\"a\":11,\"owners\":[73,82,84,89]},{\"tag\":\"mate\",\"ridge\":536,\"a\":38,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":536,\"a\":54,\"owners\":[82,84]},{\"tag\":\"mate\",\"ridge\":536,\"a\":66,\"owners\":[73,84]},{\"tag\":\"mate\",\"ridge\":208,\"a\":59,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":592,\"a\":45,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":588,\"a\":56,\"owners\":[74,89]},{\"tag\":\"mate\",\"ridge\":588,\"a\":74,\"owners\":[56,89]},{\"tag\":\"mate\",\"ridge\":786,\"a\":84,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[23,53,55,72,88],\"full_literals\":[-36,5,18,20,26,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[45,59,60,66,70],\"full_literals\":[-37,14,22,23,24,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[24,38,41,42],\"full_literals\":[-38,6,10,11,12]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[21,51,52,54],\"full_literals\":[-39,3,16,17,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[25,32,33,44,50],\"full_literals\":[-40,7,8,9,13,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[22],\"full_literals\":[-41,4]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-42,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-44,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,38,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,40,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-49,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,46,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-51,44,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-51,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[77,82,89],\"full_literals\":[-52,29,30,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":82,\"full_literals\":[-30,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":89,\"full_literals\":[-35,52]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[4,11,24,38,41,42,54,56,66,73,74,82,84,89]}]}"
  "p cnf 52 79\n-4 -3 0\n-6 -3 0\n-6 -4 0\n-10 -3 0\n-11 -3 0\n-11 -4 0\n-12 -4 0\n-16 -4 0\n-16 -5 0\n-17 -4 0\n-18 -16 0\n-19 -9 0\n-20 -16 0\n-21 -3 0\n-21 -16 0\n-22 -17 0\n-23 -17 0\n-23 -19 0\n-24 -17 0\n-24 -19 0\n-25 -15 0\n-25 -17 0\n-27 -3 0\n-27 -26 0\n-28 -4 0\n-28 -17 0\n-28 -19 0\n-29 -26 0\n-30 -4 0\n-30 -7 0\n-30 -13 0\n-30 -26 0\n-32 -30 0\n-33 -30 0\n-34 -16 0\n-35 -4 0\n-35 -17 0\n-35 -19 0\n-1 27 28 30 31 0\n-6 30 31 0\n-11 27 28 30 31 0\n-12 27 31 0\n-8 32 33 0\n-16 -26 -35 0\n-2 27 30 31 35 0\n-10 35 0\n-19 30 31 0\n-24 27 31 0\n-22 32 33 0\n-14 35 0\n-21 28 35 0\n-28 21 35 0\n-31 0\n-36 5 18 20 26 34 0\n-37 14 22 23 24 25 0\n-38 6 10 11 12 0\n-39 3 16 17 19 0\n-40 7 8 9 13 15 0\n-41 4 0\n-42 36 0\n-43 37 0\n-44 42 0\n-44 43 0\n-45 38 39 0\n-46 38 0\n-46 39 0\n-47 40 41 0\n-48 41 0\n-49 45 0\n-49 46 48 0\n-49 47 0\n-50 48 0\n-51 44 50 0\n-51 49 0\n51 0\n-52 29 30 35 0\n-30 52 0\n-35 52 0\n1 2 6 10 11 12 19 21 24 27 28 30 31 35 0\n"
  "80 49 0 75 74 0\n81 45 0 80 69 0\n82 47 0 80 71 0\n83 1 2 6 10 11 12 19 21 24 27 28 30 35 0 53 79 0\n84 27 28 52 0 53 78 51 46 77 47 40 39 41 42 48 45 83 0\n85 -28 35 0 80 25 26 27 52 59 14 15 68 57 70 66 0\n86 -3 -38 10 0 53 2 5 23 56 42 0\n87 -26 35 0 85 24 28 32 84 76 0\n88 -16 -36 26 0 9 11 13 35 54 0\n89 48 19 35 0 80 75 87 50 46 72 70 73 65 66 62 63 60 61 86 88 57 16 17 22 55 19 0\n90 19 35 0 81 46 89 68 59 1 3 6 7 8 10 56 57 64 0\n91 35 0 53 82 75 50 90 12 18 20 47 29 30 31 33 34 59 43 49 68 67 72 58 73 21 63 55 61 0\n92 -4 0 91 36 0\n93 -17 0 91 37 0\n94 -19 0 91 38 0\n95 -41 0 92 59 0\n96 -48 0 95 68 0\n97 -50 0 96 72 0\n98 46 0 96 80 70 0\n99 44 0 97 75 73 0\n100 38 0 98 65 0\n101 39 0 98 66 0\n102 42 0 99 62 0\n103 36 0 102 60 0\n104 -3 0 100 4 86 0\n105 16 0 104 94 93 101 57 0\n106 -26 0 105 91 44 0\n107 0 105 106 103 88 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00058.record001
