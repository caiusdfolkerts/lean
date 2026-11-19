module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00019Frames
public import GraphInputsRow19Part00019Leaves
public import GraphInputsRow19Part00019Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00019.record031
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2b29693ab1966a5a562d94e4b85e0fab196539b1565a56552d54d4b45d0f743b0ea368d63a4e538cd332ce4b4ae1b46c5b0ee8791d4731d2719e1725c5743c8f0bd4a298361381e524a50d44d0768390d4348ca384c3342c4b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6d26936db6d2692492492492492492492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 55), (facetIndex 60)]))
 (.leaf ([(facetIndex 62), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 58), (facetIndex 63)]))
 (.branch 4
 (.leaf ([(facetIndex 59), (facetIndex 64)]))
 (.leaf ([(facetIndex 72)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 74)]))
 (.leaf ([(facetIndex 70), (facetIndex 75)])))
 (.branch 8
 (.leaf ([(facetIndex 71), (facetIndex 76)]))
 (.branch 9
 (.leaf ([(facetIndex 61)]))
 (.leaf ([(facetIndex 73)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "7659476001003218032z3a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3, 4]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0013 : List Nat := [6]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8, 9]
def grouped3_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [8, 9]
def grouped3_0018 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00019.record031" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00019.record031" 58

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00019.record031" "{\"ridges\":[[9,529],[9,530],[11,289],[13,578],[14,642],[30,529],[32,289],[35,578],[36,642],[40,529],[40,530],[41,289],[42,578],[44,289],[45,529],[45,530],[46,529],[46,530],[46,577],[47,529],[47,530],[47,641],[48,290],[49,289],[50,641],[50,642],[51,578],[51,642],[52,578],[58,596],[59,660],[61,708],[63,600],[64,688],[70,596],[71,660],[72,356],[73,708],[74,312],[75,600],[76,688]],\"owners\":[[9,529,[58,59,63,64],[30,40,45,46,47]],[30,529,[63,64],[9,40,45,46,47,58,59]],[40,529,[58,59,64],[9,30,45,46,47,63]],[45,529,[58,59,63],[9,30,40,46,47,64]],[46,529,[59,64],[9,30,40,45,47,58,63]],[47,529,[58,63],[9,30,40,45,46,59,64]],[9,530,[70,71,75,76],[30,40,45,46,47]],[40,530,[70,71,76],[9,30,45,46,47,75]],[45,530,[70,71,75],[9,30,40,46,47,76]],[46,530,[71,76],[9,30,40,45,47,70,75]],[47,530,[70,75],[9,30,40,45,46,71,76]],[11,289,[55,60,62],[32,41,44,48,49]],[32,289,[62],[11,41,44,48,49,55,60]],[41,289,[60],[11,32,44,48,49,55,62]],[44,289,[55,60],[11,32,41,48,49,62]],[49,289,[55,60,62],[11,32,41,44,48]],[48,290,[67,74],[11,32,41,44,49,72]],[46,577,[61],[13,35,42,51,52,58,63]],[13,578,[70,73,75],[35,42,46,51,52]],[35,578,[75],[13,42,46,51,52,70,73]],[42,578,[70,73],[13,35,46,51,52,75]],[51,578,[70,75],[13,35,42,46,52,73]],[52,578,[70,73,75],[13,35,42,46,51]],[47,641,[61],[14,36,50,51,59,64]],[50,641,[59,61],[14,36,47,51,64]],[14,642,[71,73,76],[36,47,50,51]],[36,642,[76],[14,47,50,51,71,73]],[50,642,[71,73],[14,36,47,51,76]],[51,642,[71,76],[14,36,47,50,73]],[58,596,[70],[]],[70,596,[58],[]],[59,660,[71],[]],[71,660,[59],[]],[72,356,[60],[]],[61,708,[73],[]],[73,708,[61],[]],[74,312,[62],[]],[63,600,[75],[]],[75,600,[63],[]],[64,688,[76],[]],[76,688,[64],[]]],\"edges\":[[34,[9,30,40,45,46,47,58,59,63,64,70,71,75,76]],[37,[11,32,41,44,48,49,55,60,62,67,72,74]],[41,[13,35,42,46,51,52,58,61,63,70,73,75]],[43,[14,36,47,50,51,59,61,64,71,73,76]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00019.record031" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00019.record031\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-25,-5],[-25,-22],[-25,-23],[-30,-8],[-30,-23],[-30,-25],[-31,-30],[-1,22,23,27,28],[-5,27,28],[-9,22,23,28],[-13,22,23,27],[-14,23,28],[-15,22,27],[-1,30,31,35,36],[-9,30,31,36],[-13,30,31,35],[-14,31,36],[-15,30,35],[-2,21,24,26],[-6,26],[-10,24],[-12,21,24],[-17,21,24,26],[-16,29,34],[-14,25],[-3,30,33,35],[-7,35],[-11,30,33],[-19,30,35],[-20,30,33,35],[-15,25],[-18,23,25],[-4,31,33,36],[-8,36],[-18,31,33],[-19,31,36],[-22,30],[-30,22],[-23,31],[-31,23],[-32,24],[-25,33],[-33,25],[-34,26],[-27,35],[-35,27],[-28,36],[-36,28],[-21,37],[-24,37],[-26,38],[-29,38],[-22,39],[-27,39],[-23,40],[-28,40],[-30,41],[-35,41],[-31,42],[-36,42],[-43,25],[-25,43],[-33,44],[-38,45],[-37,45],[-40,46],[-46,47],[-39,47],[-39,-46,48],[-45,-47,49],[-45,-48,50],[-41,51],[-52,43],[-43,-44,52],[-52,54],[-42,53],[-42,-52,55],[-55,57],[-51,-53,56],[-51,-54,57],[-49,-57,58],[-50,-56,58],[-58],[1,5,9,13,14,15,22,23,27,28,30,31,35,36],[2,6,10,12,16,17,21,24,26,29,32,34],[3,7,11,14,19,20,22,25,27,30,33,35],[4,8,15,18,19,23,25,28,31,33,36]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":61,\"b\":30},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":59},{\"tag\":\"incompatible\",\"a\":70,\"b\":36},{\"tag\":\"incompatible\",\"a\":70,\"b\":59},{\"tag\":\"incompatible\",\"a\":70,\"b\":61},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"mate\",\"ridge\":529,\"a\":9,\"owners\":[58,59,63,64]},{\"tag\":\"mate\",\"ridge\":529,\"a\":30,\"owners\":[63,64]},{\"tag\":\"mate\",\"ridge\":529,\"a\":40,\"owners\":[58,59,64]},{\"tag\":\"mate\",\"ridge\":529,\"a\":45,\"owners\":[58,59,63]},{\"tag\":\"mate\",\"ridge\":529,\"a\":46,\"owners\":[59,64]},{\"tag\":\"mate\",\"ridge\":529,\"a\":47,\"owners\":[58,63]},{\"tag\":\"mate\",\"ridge\":530,\"a\":9,\"owners\":[70,71,75,76]},{\"tag\":\"mate\",\"ridge\":530,\"a\":40,\"owners\":[70,71,76]},{\"tag\":\"mate\",\"ridge\":530,\"a\":45,\"owners\":[70,71,75]},{\"tag\":\"mate\",\"ridge\":530,\"a\":46,\"owners\":[71,76]},{\"tag\":\"mate\",\"ridge\":530,\"a\":47,\"owners\":[70,75]},{\"tag\":\"mate\",\"ridge\":289,\"a\":11,\"owners\":[55,60,62]},{\"tag\":\"mate\",\"ridge\":289,\"a\":32,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":289,\"a\":41,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":289,\"a\":44,\"owners\":[55,60]},{\"tag\":\"mate\",\"ridge\":289,\"a\":49,\"owners\":[55,60,62]},{\"tag\":\"mate\",\"ridge\":290,\"a\":48,\"owners\":[67,74]},{\"tag\":\"mate\",\"ridge\":577,\"a\":46,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":578,\"a\":13,\"owners\":[70,73,75]},{\"tag\":\"mate\",\"ridge\":578,\"a\":35,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":578,\"a\":42,\"owners\":[70,73]},{\"tag\":\"mate\",\"ridge\":578,\"a\":51,\"owners\":[70,75]},{\"tag\":\"mate\",\"ridge\":578,\"a\":52,\"owners\":[70,73,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":47,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":641,\"a\":50,\"owners\":[59,61]},{\"tag\":\"mate\",\"ridge\":642,\"a\":14,\"owners\":[71,73,76]},{\"tag\":\"mate\",\"ridge\":642,\"a\":36,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":642,\"a\":50,\"owners\":[71,73]},{\"tag\":\"mate\",\"ridge\":642,\"a\":51,\"owners\":[71,76]},{\"tag\":\"mate\",\"ridge\":596,\"a\":58,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":596,\"a\":70,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":660,\"a\":59,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":660,\"a\":71,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":356,\"a\":72,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":708,\"a\":61,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":708,\"a\":73,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":312,\"a\":74,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":600,\"a\":63,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":600,\"a\":75,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":688,\"a\":64,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":688,\"a\":76,\"owners\":[64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":55,\"full_literals\":[-21,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":60,\"full_literals\":[-24,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":62,\"full_literals\":[-26,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-29,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":58,\"full_literals\":[-22,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":63,\"full_literals\":[-27,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":59,\"full_literals\":[-23,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":64,\"full_literals\":[-28,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":70,\"full_literals\":[-30,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-35,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":71,\"full_literals\":[-31,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":76,\"full_literals\":[-36,42]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[61],\"full_literals\":[-43,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":61,\"full_literals\":[-25,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":73,\"full_literals\":[-33,44]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-46,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-47,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-45,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,43,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-44,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-42,-52,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-53,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-51,-54,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-49,-57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-50,-56,58],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[9,30,40,45,46,47,58,59,63,64,70,71,75,76]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[11,32,41,44,48,49,55,60,62,67,72,74]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[13,35,42,46,51,52,58,61,63,70,73,75]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[14,36,47,50,51,59,61,64,71,73,76]}]}"
  "88 45 0 64 65 51 52 49 50 20 44 24 19 22 23 21 41 85 0\n89 47 0 67 68 66 53 54 55 56 38 46 11 13 8 40 48 9 10 12 84 0\n90 49 0 89 88 70 0\n91 -57 0 90 83 81 0\n92 -55 0 91 78 0\n93 -52 0 92 91 73 75 77 61 80 59 60 1 2 3 6 72 47 15 17 58 45 14 16 18 84 0\n94 -43 0 93 61 74 42 63 0\n95 -25 0 94 62 0\n96 -14 0 95 25 0\n97 -15 0 95 31 0\n98 -33 0 95 43 0\n99 30 35 0 96 95 98 29 37 26 28 30 27 45 86 0\n100 41 0 57 58 99 0\n101 51 0 100 72 0\n102 36 28 19 18 8 23 31 0 98 97 95 87 33 0\n103 36 19 -30 0 95 5 32 7 4 47 102 0\n104 -36 -39 0 101 83 88 48 60 56 76 66 79 69 82 71 0\n105 -30 0 7 38 53 104 36 103 0\n106 35 0 105 99 0\n107 27 0 106 46 0\n108 39 0 107 54 0\n109 -36 0 108 104 0\n110 -8 0 109 34 0\n111 -28 0 109 47 0\n112 31 19 0 98 110 111 109 35 39 102 0\n113 -31 0 101 108 83 88 40 59 55 76 66 79 69 82 71 0\n114 -19 0 113 109 36 0\n115 0 113 114 112 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00019.record031_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00019.record031
