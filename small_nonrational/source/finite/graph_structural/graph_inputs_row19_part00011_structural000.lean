module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00011Frames
public import GraphInputsRow19Part00011Leaves
public import GraphInputsRow19Part00011Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00011.record085
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "cb0dcca8dac98d62d876c38ce8b92e2785eca4d9c94d58d4b51d70da364d3362d4b49d1772334d332cc73c2d8b52ccb8ad2b26c5bc1cc789d2729c6783d0f0bc1f258560d88e13b21c2625254550d60d2344d48c9314c3342c8b12c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6da49a6d24d2492492692492492692692492489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 61), (facetIndex 63)]))
 (.leaf ([(facetIndex 26), (facetIndex 64), (facetIndex 65), (facetIndex 70), (facetIndex 71), (facetIndex 72)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 38), (facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 43)]))
 (.leaf ([(facetIndex 32), (facetIndex 44), (facetIndex 45), (facetIndex 46)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 29), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56)]))
 (.leaf ([(facetIndex 27), (facetIndex 30), (facetIndex 31), (facetIndex 33), (facetIndex 59)])))
 (.branch 7
 (.leaf ([(facetIndex 34), (facetIndex 47), (facetIndex 60), (facetIndex 68)]))
 (.branch 8
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 57), (facetIndex 58)]))
 (.leaf ([(facetIndex 36), (facetIndex 37)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "11106001100065774444407706333222202880653554251z1a;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 62)]))
 (.branch 2
 (.leaf ([(facetIndex 74)]))
 (.leaf ([(facetIndex 76)]))))
 (.branch 4
 (.leaf ([(facetIndex 35), (facetIndex 39), (facetIndex 51)]))
 (.branch 5
 (.leaf ([(facetIndex 66), (facetIndex 67), (facetIndex 69)]))
 (.leaf ([(facetIndex 73), (facetIndex 75), (facetIndex 77)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2aa680209000000000006000000006006z1a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
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
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1, 2]
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [1, 2]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [3, 4, 5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00011.record085" "{\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00011.record085" 69

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00011.record085" "{\"ridges\":[[5,67],[6,131],[9,81],[10,145],[12,69],[13,133],[44,81],[45,145],[62,216],[74,216],[76,216]],\"owners\":[[5,67,[3,9,30,34,44,47],[40,41]],[12,69,[3,16,30,34,57,60],[53,54]],[6,131,[4,10,31,34,45,47],[40,42]],[13,133,[4,17,31,34,58,60],[53,55]],[9,81,[16,49,57,60,62],[36,44,47]],[44,81,[16,49,60,62],[9,36,47,57]],[10,145,[17,50,58,60,62],[37,45,47]],[45,145,[17,50,60,62],[10,37,47,58]],[62,216,[74,76],[]],[74,216,[62,76],[]],[76,216,[62,74],[]]],\"edges\":[[5,[3,5,9,12,16,30,34,36,40,41,44,47,49,53,54,57,60,62]],[6,[4,6,10,13,17,31,34,37,40,42,45,47,50,53,55,58,60,62]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00011.record085" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00011.record085\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-12,-1],[-12,-2],[-15,-12],[-21,-12],[-22,-12],[-25,-12],[-30,-12],[-31,-12],[-32,-10],[-32,-13],[-32,-16],[-32,-23],[-33,-9],[-33,-14],[-33,-16],[-33,-24],[-33,-32],[-34,-32],[-34,-33],[-36,-11],[-36,-17],[-36,-18],[-36,-19],[-36,-26],[-36,-27],[-36,-28],[-36,-35],[-37,-36],[-38,-36],[-39,-36],[-40,-13],[-40,-23],[-40,-32],[-41,-14],[-41,-24],[-41,-33],[-42,-36],[-43,-11],[-43,-17],[-43,-18],[-43,-19],[-43,-20],[-43,-26],[-43,-27],[-43,-28],[-43,-29],[-43,-35],[-43,-37],[-43,-38],[-43,-39],[-43,-42],[-3,1,5,13,17,23,26],[-7,1,9,13,17,32,35],[-4,2,6,14,17,24,26],[-8,2,10,14,17,33,35],[-5,9,27,32,35,36],[-23,9,27,35,36],[-6,10,28,33,35,36],[-24,10,28,35,36],[-36,43,44],[-43,36,44],[-44,36,43],[-45,11,37,38,40,41,42],[-46,15,23,24,25],[-47,12,13,14,16,34],[-48,17,26,35,39],[-49,27,28,32,33],[-50,18,19],[-51,45],[-52,46],[-53,51],[-53,52],[-54,47],[-55,49,50],[-56,50],[-57,48,55],[-58,48,56],[-59,54,58],[-59,57],[-60,58],[-61,53,60],[-61,59],[61],[-62,36],[-36,62],[-63,43],[-43,63],[-64,44],[-44,64],[-65,63,64],[-64,65],[-66,63],[-63,65],[-63,-64,66],[-67,62,65],[-68,62,66],[-66,68],[-62,-65,68],[-69,67],[69],[1,3,5,7,9,13,17,18,20,21,23,26,27,29,30,32,35,36],[2,4,6,8,10,14,17,19,20,22,24,26,28,29,31,33,35,36]],\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":27,\"b\":3},{\"tag\":\"incompatible\",\"a\":27,\"b\":4},{\"tag\":\"incompatible\",\"a\":32,\"b\":27},{\"tag\":\"incompatible\",\"a\":41,\"b\":27},{\"tag\":\"incompatible\",\"a\":42,\"b\":27},{\"tag\":\"incompatible\",\"a\":46,\"b\":27},{\"tag\":\"incompatible\",\"a\":54,\"b\":27},{\"tag\":\"incompatible\",\"a\":55,\"b\":27},{\"tag\":\"incompatible\",\"a\":57,\"b\":17},{\"tag\":\"incompatible\",\"a\":57,\"b\":30},{\"tag\":\"incompatible\",\"a\":57,\"b\":33},{\"tag\":\"incompatible\",\"a\":57,\"b\":44},{\"tag\":\"incompatible\",\"a\":58,\"b\":16},{\"tag\":\"incompatible\",\"a\":58,\"b\":31},{\"tag\":\"incompatible\",\"a\":58,\"b\":33},{\"tag\":\"incompatible\",\"a\":58,\"b\":45},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":26},{\"tag\":\"incompatible\",\"a\":62,\"b\":34},{\"tag\":\"incompatible\",\"a\":62,\"b\":36},{\"tag\":\"incompatible\",\"a\":62,\"b\":37},{\"tag\":\"incompatible\",\"a\":62,\"b\":47},{\"tag\":\"incompatible\",\"a\":62,\"b\":49},{\"tag\":\"incompatible\",\"a\":62,\"b\":50},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":62},{\"tag\":\"incompatible\",\"a\":68,\"b\":62},{\"tag\":\"incompatible\",\"a\":70,\"b\":30},{\"tag\":\"incompatible\",\"a\":70,\"b\":44},{\"tag\":\"incompatible\",\"a\":70,\"b\":57},{\"tag\":\"incompatible\",\"a\":71,\"b\":31},{\"tag\":\"incompatible\",\"a\":71,\"b\":45},{\"tag\":\"incompatible\",\"a\":71,\"b\":58},{\"tag\":\"incompatible\",\"a\":72,\"b\":62},{\"tag\":\"incompatible\",\"a\":74,\"b\":26},{\"tag\":\"incompatible\",\"a\":74,\"b\":34},{\"tag\":\"incompatible\",\"a\":74,\"b\":36},{\"tag\":\"incompatible\",\"a\":74,\"b\":37},{\"tag\":\"incompatible\",\"a\":74,\"b\":40},{\"tag\":\"incompatible\",\"a\":74,\"b\":47},{\"tag\":\"incompatible\",\"a\":74,\"b\":49},{\"tag\":\"incompatible\",\"a\":74,\"b\":50},{\"tag\":\"incompatible\",\"a\":74,\"b\":53},{\"tag\":\"incompatible\",\"a\":74,\"b\":60},{\"tag\":\"incompatible\",\"a\":74,\"b\":64},{\"tag\":\"incompatible\",\"a\":74,\"b\":65},{\"tag\":\"incompatible\",\"a\":74,\"b\":68},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"mate\",\"ridge\":67,\"a\":5,\"owners\":[3,9,30,34,44,47]},{\"tag\":\"mate\",\"ridge\":69,\"a\":12,\"owners\":[3,16,30,34,57,60]},{\"tag\":\"mate\",\"ridge\":131,\"a\":6,\"owners\":[4,10,31,34,45,47]},{\"tag\":\"mate\",\"ridge\":133,\"a\":13,\"owners\":[4,17,31,34,58,60]},{\"tag\":\"mate\",\"ridge\":81,\"a\":9,\"owners\":[16,49,57,60,62]},{\"tag\":\"mate\",\"ridge\":81,\"a\":44,\"owners\":[16,49,60,62]},{\"tag\":\"mate\",\"ridge\":145,\"a\":10,\"owners\":[17,50,58,60,62]},{\"tag\":\"mate\",\"ridge\":145,\"a\":45,\"owners\":[17,50,60,62]},{\"tag\":\"mate\",\"ridge\":216,\"a\":62,\"owners\":[74,76]},{\"tag\":\"mate\",\"ridge\":216,\"a\":74,\"owners\":[62,76]},{\"tag\":\"mate\",\"ridge\":216,\"a\":76,\"owners\":[62,74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[26,64,65,70,71,72],\"full_literals\":[-45,11,37,38,40,41,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[32,44,45,46],\"full_literals\":[-46,15,23,24,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[27,30,31,33,59],\"full_literals\":[-47,12,13,14,16,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[34,47,60,68],\"full_literals\":[-48,17,26,35,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[49,50,57,58],\"full_literals\":[-49,27,28,32,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[36,37],\"full_literals\":[-50,18,19]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-53,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,49,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,48,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,48,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,54,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-61,53,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-61,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[62],\"full_literals\":[-62,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":62,\"full_literals\":[-36,62]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[74],\"full_literals\":[-63,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":74,\"full_literals\":[-43,63]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[76],\"full_literals\":[-64,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":76,\"full_literals\":[-44,64]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,63,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,62,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,62,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-62,-65,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-69,67,false],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":5,\"owners\":[3,5,9,12,16,30,34,36,40,41,44,47,49,53,54,57,60,62]},{\"tag\":\"edge\",\"edge\":6,\"owners\":[4,6,10,13,17,31,34,37,40,42,45,47,50,53,55,58,60,62]}]}"
  "p cnf 69 102\n-12 -1 0\n-12 -2 0\n-15 -12 0\n-21 -12 0\n-22 -12 0\n-25 -12 0\n-30 -12 0\n-31 -12 0\n-32 -10 0\n-32 -13 0\n-32 -16 0\n-32 -23 0\n-33 -9 0\n-33 -14 0\n-33 -16 0\n-33 -24 0\n-33 -32 0\n-34 -32 0\n-34 -33 0\n-36 -11 0\n-36 -17 0\n-36 -18 0\n-36 -19 0\n-36 -26 0\n-36 -27 0\n-36 -28 0\n-36 -35 0\n-37 -36 0\n-38 -36 0\n-39 -36 0\n-40 -13 0\n-40 -23 0\n-40 -32 0\n-41 -14 0\n-41 -24 0\n-41 -33 0\n-42 -36 0\n-43 -11 0\n-43 -17 0\n-43 -18 0\n-43 -19 0\n-43 -20 0\n-43 -26 0\n-43 -27 0\n-43 -28 0\n-43 -29 0\n-43 -35 0\n-43 -37 0\n-43 -38 0\n-43 -39 0\n-43 -42 0\n-3 1 5 13 17 23 26 0\n-7 1 9 13 17 32 35 0\n-4 2 6 14 17 24 26 0\n-8 2 10 14 17 33 35 0\n-5 9 27 32 35 36 0\n-23 9 27 35 36 0\n-6 10 28 33 35 36 0\n-24 10 28 35 36 0\n-36 43 44 0\n-43 36 44 0\n-44 36 43 0\n-45 11 37 38 40 41 42 0\n-46 15 23 24 25 0\n-47 12 13 14 16 34 0\n-48 17 26 35 39 0\n-49 27 28 32 33 0\n-50 18 19 0\n-51 45 0\n-52 46 0\n-53 51 0\n-53 52 0\n-54 47 0\n-55 49 50 0\n-56 50 0\n-57 48 55 0\n-58 48 56 0\n-59 54 58 0\n-59 57 0\n-60 58 0\n-61 53 60 0\n-61 59 0\n61 0\n-62 36 0\n-36 62 0\n-63 43 0\n-43 63 0\n-64 44 0\n-44 64 0\n-65 63 64 0\n-64 65 0\n-66 63 0\n-63 65 0\n-63 -64 66 0\n-67 62 65 0\n-68 62 66 0\n-66 68 0\n-62 -65 68 0\n-69 67 0\n69 0\n1 3 5 7 9 13 17 18 20 21 23 26 27 29 30 32 35 36 0\n2 4 6 8 10 14 17 19 20 22 24 26 28 29 31 33 35 36 0\n"
  "103 59 0 83 82 0\n104 57 0 103 79 0\n105 67 0 100 99 0\n106 -64 36 66 0 88 94 62 87 0\n107 -65 68 0 97 98 85 106 89 90 61 86 0\n108 65 0 105 91 93 95 89 87 84 60 0\n109 68 0 108 107 0\n110 -32 -36 0 103 83 22 23 68 75 27 24 21 30 66 77 80 81 72 70 71 69 78 73 37 29 28 20 10 11 12 18 33 63 34 35 65 3 6 64 0\n111 -36 0 104 103 83 20 21 22 23 24 25 26 27 28 29 30 37 68 66 75 76 77 74 80 78 81 73 71 72 69 70 110 67 14 15 16 19 36 63 31 32 65 3 6 64 0\n112 -62 0 111 84 0\n113 66 0 112 109 96 0\n114 63 0 113 92 0\n115 43 0 114 86 0\n116 -11 0 115 38 0\n117 -17 0 115 39 0\n118 -18 0 115 40 0\n119 -19 0 115 41 0\n120 -20 0 115 42 0\n121 -26 0 115 43 0\n122 -27 0 115 44 0\n123 -28 0 115 45 0\n124 -29 0 115 46 0\n125 -35 0 115 47 0\n126 -37 0 115 48 0\n127 -38 0 115 49 0\n128 -39 0 115 50 0\n129 -42 0 115 51 0\n130 -50 0 119 118 68 0\n131 -48 0 128 117 121 125 66 0\n132 -56 0 130 75 0\n133 55 0 131 104 76 0\n134 -58 0 131 132 77 0\n135 49 0 133 130 74 0\n136 -60 0 134 80 0\n137 54 0 134 103 78 0\n138 53 0 136 83 81 0\n139 47 0 137 73 0\n140 51 0 138 71 0\n141 45 0 140 69 0\n142 -33 0 129 141 127 126 116 139 111 125 122 124 121 120 118 117 13 14 15 17 19 36 57 56 63 31 65 1 4 7 53 52 101 0\n143 32 0 142 122 123 135 67 0\n144 -10 0 143 9 0\n145 -13 0 143 10 0\n146 -16 0 143 11 0\n147 -34 0 143 18 0\n148 -40 0 143 33 0\n149 -6 0 144 123 142 125 111 58 0\n150 -24 0 144 123 125 111 59 0\n151 41 0 148 116 126 127 141 129 63 0\n152 -14 0 151 34 0\n153 12 0 152 145 146 147 139 65 0\n154 -2 0 153 2 0\n155 -22 0 153 5 0\n156 -31 0 153 8 0\n157 -8 0 154 152 144 117 142 125 55 0\n158 -4 0 154 149 152 117 150 121 54 0\n159 0 156 154 144 158 149 157 152 117 119 120 155 150 121 124 123 142 125 111 102 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00011.record085
