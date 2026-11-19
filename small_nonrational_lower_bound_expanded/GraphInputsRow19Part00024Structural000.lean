module
prelude
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00024Frames
public import GraphInputsRow19Part00024Leaves
public import GraphInputsRow19Part00024Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00024.record018
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2e83d15c3caaa3a8e6358b61da8e638ce4785eb86c9aa6693a559395551d68d534cd4745da8ce38cd331cf0ba2ccb8acab1ad1b16e8731ca719c570de0f23c4f07ccca8a8a4590e23871454554344d88d130ce0b42d0705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db69b6da4936db6da4d24934924d369b6da492449249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 60), (facetIndex 66)]))
 (.leaf ([(facetIndex 23), (facetIndex 37), (facetIndex 38), (facetIndex 39)])))
 (.branch 3
 (.leaf ([(facetIndex 24), (facetIndex 42), (facetIndex 47), (facetIndex 48)]))
 (.leaf ([(facetIndex 19), (facetIndex 30), (facetIndex 43), (facetIndex 57)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 22), (facetIndex 33), (facetIndex 36)]))
 (.leaf ([(facetIndex 21), (facetIndex 41), (facetIndex 44)])))
 (.branch 7
 (.leaf ([(facetIndex 20), (facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 45)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "d9800000243d6a824c0200c000232e600000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018_matrix_checked

def leafCount : Nat := 1
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 11), (facetIndex 18), (facetIndex 36), (facetIndex 38), (facetIndex 41), (facetIndex 45), (facetIndex 47), (facetIndex 52), (facetIndex 57), (facetIndex 60), (facetIndex 63), (facetIndex 67), (facetIndex 70)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.leaf (leaf0000))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00024.record018" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00024.record018" 61

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00024.record018" "{\"ridges\":[[18,76],[23,7],[24,7],[28,645],[41,545],[41,672],[45,76],[47,84],[47,112],[56,76],[57,276],[58,196],[60,140],[66,648]],\"owners\":[[23,7,[0,2,20,21,22,27,28],[1,24,25,26]],[24,7,[0,2,21,22,26,28],[1,20,23,25,27]],[41,545,[52],[7,33,39,53,55]],[47,84,[56,63,68],[10,24,42,48,61,69]],[57,276,[11,48],[15,43,68]],[47,112,[67],[12,37,61,69]],[60,140,[18,44],[13,21,46,59]],[66,648,[46,54],[16,35,53,60,70]],[41,672,[70],[17,53,55,66]],[58,196,[49,69],[18,27,44,63,64]],[28,645,[46],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00024.record018" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00024.record018\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-7,-6],[-16,-15],[-17,-6],[-17,-14],[-21,-11],[-21,-12],[-21,-15],[-21,-16],[-21,-20],[-24,-6],[-24,-16],[-25,-1],[-25,-5],[-25,-6],[-25,-7],[-25,-8],[-25,-22],[-25,-23],[-25,-24],[-26,-24],[-26,-25],[-27,-18],[-28,-25],[-29,-21],[-31,-24],[-33,-2],[-34,-7],[-34,-10],[-34,-24],[-34,-32],[-35,-7],[-35,-33],[-36,-7],[-36,-8],[-36,-34],[-36,-35],[-37,-34],[-38,-15],[-38,-21],[-40,-25],[-41,-27],[-9,1,2,6,7,8,12,13],[-10,1,2,7,8,11,13],[-21,30],[-4,-25,-32],[-27,32,37,40],[-33,3,28],[-27,39],[-36,4,24],[-38,26,31],[-21,42],[-34,29,41],[-13,26],[-43,16,36,38],[-44,9,18,19,20],[-45,10,22,27,28],[-46,5,14,23,33],[-47,8,15,17],[-48,7,21,24],[-49,6,34,35],[-50,25],[-51,43],[-51,44],[-52,45],[-52,46],[-53,51,52],[-54,51],[-54,52],[-55,47,48],[-56,47],[-56,48],[-57,49,50],[-58,49],[-58,50],[-59,55],[-59,56,58],[-60,56],[-59,57],[-60,58],[-61,53],[-61,54,60],[-61,59],[61],[-3,-4,-17,-19,-21,-25,-27,-30,-33,-36,-37,-39,-42]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":21,\"b\":20},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":36,\"b\":20},{\"tag\":\"incompatible\",\"a\":36,\"b\":30},{\"tag\":\"incompatible\",\"a\":41,\"b\":26},{\"tag\":\"incompatible\",\"a\":41,\"b\":27},{\"tag\":\"incompatible\",\"a\":41,\"b\":33},{\"tag\":\"incompatible\",\"a\":41,\"b\":35},{\"tag\":\"incompatible\",\"a\":41,\"b\":39},{\"tag\":\"incompatible\",\"a\":44,\"b\":20},{\"tag\":\"incompatible\",\"a\":44,\"b\":35},{\"tag\":\"incompatible\",\"a\":45,\"b\":0},{\"tag\":\"incompatible\",\"a\":45,\"b\":19},{\"tag\":\"incompatible\",\"a\":45,\"b\":20},{\"tag\":\"incompatible\",\"a\":45,\"b\":21},{\"tag\":\"incompatible\",\"a\":45,\"b\":22},{\"tag\":\"incompatible\",\"a\":45,\"b\":42},{\"tag\":\"incompatible\",\"a\":45,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":47,\"b\":37},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":41},{\"tag\":\"incompatible\",\"a\":54,\"b\":44},{\"tag\":\"incompatible\",\"a\":57,\"b\":2},{\"tag\":\"incompatible\",\"a\":58,\"b\":21},{\"tag\":\"incompatible\",\"a\":58,\"b\":24},{\"tag\":\"incompatible\",\"a\":58,\"b\":44},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":59,\"b\":21},{\"tag\":\"incompatible\",\"a\":59,\"b\":57},{\"tag\":\"incompatible\",\"a\":60,\"b\":21},{\"tag\":\"incompatible\",\"a\":60,\"b\":22},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":58},{\"tag\":\"incompatible\",\"a\":66,\"b\":33},{\"tag\":\"incompatible\",\"a\":66,\"b\":41},{\"tag\":\"incompatible\",\"a\":68,\"b\":45},{\"tag\":\"incompatible\",\"a\":69,\"b\":47},{\"tag\":\"mate\",\"ridge\":7,\"a\":23,\"owners\":[0,2,20,21,22,27,28]},{\"tag\":\"mate\",\"ridge\":7,\"a\":24,\"owners\":[0,2,21,22,26,28]},{\"tag\":\"mate\",\"ridge\":545,\"a\":41,\"owners\":[52]},{\"tag\":\"three\",\"ridge\":76,\"vertices\":[18,45,56]},{\"tag\":\"mate\",\"ridge\":84,\"a\":47,\"owners\":[56,63,68]},{\"tag\":\"mate\",\"ridge\":276,\"a\":57,\"owners\":[11,48]},{\"tag\":\"mate\",\"ridge\":112,\"a\":47,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":140,\"a\":60,\"owners\":[18,44]},{\"tag\":\"mate\",\"ridge\":648,\"a\":66,\"owners\":[46,54]},{\"tag\":\"mate\",\"ridge\":672,\"a\":41,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":196,\"a\":58,\"owners\":[49,69]},{\"tag\":\"mate\",\"ridge\":645,\"a\":28,\"owners\":[46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[35,60,66],\"full_literals\":[-43,16,36,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[23,37,38,39],\"full_literals\":[-44,9,18,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[24,42,47,48],\"full_literals\":[-45,10,22,27,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[19,30,43,57],\"full_literals\":[-46,5,14,23,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[22,33,36],\"full_literals\":[-47,8,15,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[21,41,44],\"full_literals\":[-48,7,21,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[20,58,59],\"full_literals\":[-49,6,34,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[45],\"full_literals\":[-50,25]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,51,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-54,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,47,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,49,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,56,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-60,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-61,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-61,54,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-61,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[11,18,36,38,41,45,47,52,57,60,63,67,70]}]}"
  "85 53 0 83 80 0\n86 59 0 83 82 0\n87 55 0 86 75 0\n88 57 0 86 78 0\n89 -21 36 -43 0 8 39 54 0\n90 -24 50 0 88 83 74 79 81 67 62 72 10 11 20 25 29 50 60 54 36 0\n91 -36 50 0 88 86 90 74 76 71 70 72 33 34 35 36 59 60 7 3 58 0\n92 50 0 88 86 83 74 72 79 76 81 71 67 62 90 91 89 59 1 27 31 60 0\n93 25 0 92 61 0\n94 -1 0 93 12 0\n95 -5 0 93 13 0\n96 -6 0 93 14 0\n97 -7 0 93 15 0\n98 -8 0 93 16 0\n99 -22 0 93 17 0\n100 -23 0 93 18 0\n101 -24 0 93 19 0\n102 -26 0 93 21 0\n103 -28 0 93 23 0\n104 -40 0 93 40 0\n105 -13 0 102 53 0\n106 58 36 0 86 83 101 97 79 76 81 71 67 59 62 89 0\n107 52 36 0 85 83 101 97 68 66 81 62 77 89 71 59 0\n108 -21 36 0 83 100 95 105 98 97 94 96 103 99 107 65 64 106 73 5 7 24 89 62 67 81 77 70 58 4 57 26 32 43 60 56 52 41 0\n109 -34 -45 0 103 99 104 28 30 37 56 46 0\n110 36 0 101 97 87 83 96 100 95 98 106 73 107 64 65 108 59 71 69 77 81 67 62 109 60 32 57 4 58 2 38 54 0\n111 -34 0 110 35 0\n112 -35 0 110 36 0\n113 4 0 110 101 49 0\n114 -49 0 112 111 96 60 0\n115 -32 0 113 93 45 0\n116 -58 0 114 73 0\n117 -60 0 116 79 0\n118 56 0 116 86 76 0\n119 54 0 117 83 81 0\n120 47 0 118 70 0\n121 48 0 118 71 0\n122 51 0 119 67 0\n123 52 0 119 68 0\n124 21 0 121 97 101 59 0\n125 44 0 122 63 0\n126 45 0 123 64 0\n127 46 0 123 65 0\n128 -11 0 124 5 0\n129 -15 0 124 7 0\n130 -20 0 124 9 0\n131 30 0 124 44 0\n132 42 0 124 51 0\n133 17 0 129 120 98 58 0\n134 -14 0 133 4 0\n135 33 0 134 127 95 100 57 0\n136 -2 0 135 26 0\n137 3 0 135 103 47 0\n138 -10 0 136 94 97 98 128 105 43 0\n139 27 0 138 126 99 103 56 0\n140 -18 0 139 22 0\n141 37 0 139 104 115 46 0\n142 39 0 139 48 0\n143 -19 0 139 133 113 124 93 137 131 135 110 141 142 132 84 0\n144 9 0 143 125 140 130 55 0\n145 -12 0 124 6 0\n146 0 144 136 94 96 97 98 145 105 42 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018.l) :=
(.leaf (⟨0, by decide⟩))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018.g)) :=
(.leaf ([]))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00024.record018
