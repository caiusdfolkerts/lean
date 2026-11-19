module
prelude
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00026Frames
public import GraphInputsRow26Part00026Leaves
public import GraphInputsRow26Part00026Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00026.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "31c3723cc68da4eb16358b6c38ce1ba1e4789e178d98e539c5695356352d70d934cd8b46d4749d1771364cd34ccb3c2d4b32d2b1ae1b26c5bc1ca719e1745c5783d0f23f188703c4683a318960d84e0b81ec4709865190e4c5854950d60d1342d074c344c930cd0b12c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9a4d349a4924d249249249249249249249a492491249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 46), (facetIndex 47), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52)]))
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 48), (facetIndex 54), (facetIndex 55), (facetIndex 57), (facetIndex 58)])))
 (.branch 3
 (.leaf ([(facetIndex 39), (facetIndex 59), (facetIndex 60), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65)]))
 (.branch 4
 (.leaf ([(facetIndex 61), (facetIndex 67), (facetIndex 68), (facetIndex 70), (facetIndex 71)]))
 (.leaf ([(facetIndex 43), (facetIndex 79), (facetIndex 80)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 40), (facetIndex 44), (facetIndex 82), (facetIndex 83)]))
 (.branch 7
 (.leaf ([(facetIndex 72), (facetIndex 85), (facetIndex 87)]))
 (.leaf ([(facetIndex 73), (facetIndex 88), (facetIndex 90)]))))
 (.branch 9
 (.leaf ([(facetIndex 56), (facetIndex 69), (facetIndex 75)]))
 (.branch 10
 (.leaf ([(facetIndex 53), (facetIndex 66)]))
 (.leaf ([(facetIndex 76), (facetIndex 77), (facetIndex 78)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "707606055044aaa8076338339222232211811900001000541152z27;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 45)]))
 (.branch 2
 (.leaf ([(facetIndex 74)]))
 (.leaf ([(facetIndex 81)]))))
 (.branch 4
 (.leaf ([(facetIndex 84)]))
 (.branch 5
 (.leaf ([(facetIndex 86)]))
 (.leaf ([(facetIndex 89)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2810301000004z37;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6, 7]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [6, 7]
def grouped2_0015 : List Nat := [7]
def grouped2_0016 : List Nat := [8]
def grouped2_0017 : List Nat := [8, 9, 10]
def grouped2_0018 : List Nat := [9]
def grouped2_0019 : List Nat := [9, 10]
def grouped2_0020 : List Nat := [10]
def grouped3_0021 : List Nat := [0]
def grouped3_0022 : List Nat := [0, 1, 2]
def grouped3_0024 : List Nat := [1]
def grouped3_0025 : List Nat := [1, 2]
def grouped3_0026 : List Nat := [2]
def grouped3_0027 : List Nat := [3]
def grouped3_0028 : List Nat := [3, 4, 5]
def grouped3_0029 : List Nat := [4]
def grouped3_0030 : List Nat := [4, 5]
def grouped3_0031 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00026.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group\",\"kind\":2,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0014\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0014\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0019\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00026.record008" 76

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00026.record008" "{\"ridges\":[[45,774],[57,274],[70,532],[74,216],[81,774],[84,274],[84,532],[84,774],[85,274],[86,216],[88,532],[89,216]],\"owners\":[[84,774,[45,81],[]],[74,216,[86,89],[]],[86,216,[74,89],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00026.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00026.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-5,-4],[-6,-4],[-6,-5],[-8,-6],[-9,-5],[-15,-6],[-16,-5],[-22,-15],[-22,-21],[-23,-1],[-23,-7],[-23,-11],[-23,-18],[-23,-21],[-23,-22],[-24,-23],[-25,-23],[-26,-6],[-27,-6],[-29,-23],[-30,-8],[-30,-15],[-30,-24],[-30,-26],[-30,-27],[-30,-28],[-32,-23],[-33,-2],[-33,-3],[-33,-8],[-33,-13],[-33,-15],[-33,-20],[-33,-25],[-33,-26],[-33,-27],[-33,-31],[-34,-10],[-35,-1],[-35,-11],[-35,-18],[-35,-24],[-35,-25],[-35,-26],[-35,-29],[-35,-32],[-35,-34],[-36,-6],[-36,-30],[-36,-33],[-37,-14],[-37,-17],[-37,-24],[-37,-25],[-37,-26],[-37,-27],[-38,-27],[-38,-37],[-39,-6],[-39,-30],[-39,-33],[-12,-33,-34],[-19,-33,-37],[-33,6,30],[-6,-30,-33],[-23,35,38],[-35,23,38],[-23,-35,-38],[-40,2,3,7,9,10,12,13],[-41,14,16,17,19,20],[-42,4,28,29],[-43,1,5,31,32],[-44,21,34,36],[-45,22,37,39],[-46,11,18,24],[-47,8,15],[-48,25,26,27],[-49,40],[-50,41],[-50,42],[-51,50],[-52,49],[-52,51],[-53,44,45],[-54,44],[-54,45],[-55,43,54],[-55,53],[-56,54],[-57,47,48],[-58,46,57],[-59,55,58],[-60,56,58],[-61,52,60],[-61,59],[61],[-62,6],[-63,23],[-64,30],[-65,33],[-66,35],[-67,38],[-68,63,64],[-69,63],[-69,64],[-70,62,69],[-71,62],[-70,68],[-71,69],[-72,66,67],[-73,66],[-73,67],[-74,65,73],[-75,65],[-74,72],[-75,73],[-76,70,75],[-76,71,74],[76]],\"atoms\":[{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":44,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":53,\"b\":45},{\"tag\":\"incompatible\",\"a\":54,\"b\":44},{\"tag\":\"incompatible\",\"a\":66,\"b\":45},{\"tag\":\"incompatible\",\"a\":67,\"b\":44},{\"tag\":\"incompatible\",\"a\":73,\"b\":66},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":40},{\"tag\":\"incompatible\",\"a\":74,\"b\":48},{\"tag\":\"incompatible\",\"a\":74,\"b\":56},{\"tag\":\"incompatible\",\"a\":74,\"b\":69},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":76,\"b\":74},{\"tag\":\"incompatible\",\"a\":77,\"b\":45},{\"tag\":\"incompatible\",\"a\":78,\"b\":45},{\"tag\":\"incompatible\",\"a\":80,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":53},{\"tag\":\"incompatible\",\"a\":81,\"b\":66},{\"tag\":\"incompatible\",\"a\":81,\"b\":75},{\"tag\":\"incompatible\",\"a\":81,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":78},{\"tag\":\"incompatible\",\"a\":81,\"b\":79},{\"tag\":\"incompatible\",\"a\":83,\"b\":74},{\"tag\":\"incompatible\",\"a\":84,\"b\":41},{\"tag\":\"incompatible\",\"a\":84,\"b\":42},{\"tag\":\"incompatible\",\"a\":84,\"b\":53},{\"tag\":\"incompatible\",\"a\":84,\"b\":58},{\"tag\":\"incompatible\",\"a\":84,\"b\":66},{\"tag\":\"incompatible\",\"a\":84,\"b\":71},{\"tag\":\"incompatible\",\"a\":84,\"b\":76},{\"tag\":\"incompatible\",\"a\":84,\"b\":77},{\"tag\":\"incompatible\",\"a\":84,\"b\":78},{\"tag\":\"incompatible\",\"a\":84,\"b\":82},{\"tag\":\"incompatible\",\"a\":85,\"b\":55},{\"tag\":\"incompatible\",\"a\":86,\"b\":40},{\"tag\":\"incompatible\",\"a\":86,\"b\":56},{\"tag\":\"incompatible\",\"a\":86,\"b\":69},{\"tag\":\"incompatible\",\"a\":86,\"b\":75},{\"tag\":\"incompatible\",\"a\":86,\"b\":76},{\"tag\":\"incompatible\",\"a\":86,\"b\":77},{\"tag\":\"incompatible\",\"a\":86,\"b\":80},{\"tag\":\"incompatible\",\"a\":86,\"b\":83},{\"tag\":\"incompatible\",\"a\":86,\"b\":85},{\"tag\":\"incompatible\",\"a\":87,\"b\":45},{\"tag\":\"incompatible\",\"a\":87,\"b\":81},{\"tag\":\"incompatible\",\"a\":87,\"b\":84},{\"tag\":\"incompatible\",\"a\":88,\"b\":61},{\"tag\":\"incompatible\",\"a\":88,\"b\":68},{\"tag\":\"incompatible\",\"a\":88,\"b\":75},{\"tag\":\"incompatible\",\"a\":88,\"b\":76},{\"tag\":\"incompatible\",\"a\":88,\"b\":77},{\"tag\":\"incompatible\",\"a\":88,\"b\":78},{\"tag\":\"incompatible\",\"a\":89,\"b\":78},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":90,\"b\":45},{\"tag\":\"incompatible\",\"a\":90,\"b\":81},{\"tag\":\"incompatible\",\"a\":90,\"b\":84},{\"tag\":\"three\",\"ridge\":274,\"vertices\":[57,84,85]},{\"tag\":\"three\",\"ridge\":532,\"vertices\":[70,84,88]},{\"tag\":\"mate\",\"ridge\":774,\"a\":84,\"owners\":[45,81]},{\"tag\":\"three\",\"ridge\":774,\"vertices\":[45,81,84]},{\"tag\":\"mate\",\"ridge\":216,\"a\":74,\"owners\":[86,89]},{\"tag\":\"mate\",\"ridge\":216,\"a\":86,\"owners\":[74,89]},{\"tag\":\"three\",\"ridge\":216,\"vertices\":[74,86,89]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[41,42,48,54,55,57,58],\"full_literals\":[-40,2,3,7,9,10,12,13]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[61,67,68,70,71],\"full_literals\":[-41,14,16,17,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[43,79,80],\"full_literals\":[-42,4,28,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[40,44,82,83],\"full_literals\":[-43,1,5,31,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[72,85,87],\"full_literals\":[-44,21,34,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[73,88,90],\"full_literals\":[-45,22,37,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[56,69,75],\"full_literals\":[-46,11,18,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[53,66],\"full_literals\":[-47,8,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":10,\"members\":[76,77,78],\"full_literals\":[-48,25,26,27]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-52,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-52,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0013\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0014\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,44,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0013\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0014\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0013\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0014\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,43,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0018\",\"right_name\":\"grouped2_0020\",\"joined_name\":\"grouped2_0019\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,47,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,46,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,55,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,56,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-61,52,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[45],\"full_literals\":[-62,6]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[74],\"full_literals\":[-63,23]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[81],\"full_literals\":[-64,30]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[84],\"full_literals\":[-65,33]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[86],\"full_literals\":[-66,35]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[89],\"full_literals\":[-67,38]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,63,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-69,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-70,62,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-71,62,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-70,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,66,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,66,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-74,65,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-75,65,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-75,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-76,70,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-76,71,74],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true}]}"
  "120 59 0 96 95 0\n121 -54 -75 0 116 112 102 58 111 101 47 114 100 61 50 85 86 73 74 9 0\n122 -75 0 120 96 114 116 100 111 30 32 34 35 36 37 101 76 77 39 40 41 42 45 46 90 75 91 92 121 89 87 93 72 94 1 83 81 80 3 71 64 26 0\n123 70 0 122 119 117 0\n124 68 0 123 108 0\n125 -22 56 0 124 123 119 96 8 15 98 104 103 109 106 99 118 97 21 23 24 25 26 2 65 76 100 113 111 101 40 41 43 45 75 77 71 90 80 91 81 93 83 94 0\n126 -74 -37 54 56 0 120 96 58 102 112 55 56 54 77 53 52 51 115 113 110 100 101 30 32 33 37 63 39 40 41 46 76 75 90 91 92 93 87 94 72 83 7 81 70 79 0\n127 -37 54 56 0 119 96 53 54 55 56 77 126 118 107 109 97 104 105 2 4 6 98 99 76 12 13 20 26 90 75 71 91 80 93 81 94 83 0\n128 -39 0 123 59 60 97 99 106 105 0\n129 -71 -44 38 0 107 109 97 104 48 98 14 66 73 47 0\n130 -37 56 0 119 58 127 102 85 112 129 118 115 113 110 100 101 50 47 67 73 14 0\n131 -35 -23 -74 45 0 120 16 12 13 75 17 14 44 47 68 102 112 113 100 30 32 36 50 76 77 73 90 84 91 88 92 0\n132 -23 -74 56 0 128 120 96 125 130 74 86 10 11 12 13 14 16 17 27 75 131 66 101 57 111 113 100 28 29 30 31 32 35 37 50 76 77 90 91 92 93 88 87 94 84 72 82 73 5 78 38 62 69 0\n133 -74 56 0 96 123 124 132 98 104 103 106 99 97 21 22 23 24 25 26 2 65 76 100 113 111 101 40 41 43 45 75 77 71 90 80 91 81 93 83 94 0\n134 56 0 119 96 133 118 107 109 97 104 105 2 4 6 18 19 98 99 76 12 13 16 17 20 26 75 77 71 90 80 91 81 93 83 94 0\n135 54 0 134 89 0\n136 44 0 135 85 0\n137 45 0 135 86 0\n138 -71 0 136 137 128 109 129 104 58 98 74 15 0\n139 74 0 138 119 118 0\n140 -23 0 137 128 139 136 14 15 74 58 102 66 112 47 113 73 100 50 0\n141 -63 0 140 98 0\n142 -69 0 141 104 0\n143 64 0 141 124 103 0\n144 62 0 142 123 106 0\n145 30 0 143 99 0\n146 6 0 144 97 0\n147 -36 0 145 49 0\n148 -33 0 145 146 65 0\n149 -65 0 148 100 0\n150 73 0 149 139 113 0\n151 66 0 150 111 0\n152 67 0 150 112 0\n153 35 0 151 101 0\n154 38 0 152 102 0\n155 -34 0 153 47 0\n156 -37 0 154 58 0\n157 21 0 155 136 147 73 0\n158 22 0 156 128 137 74 0\n159 0 158 157 9 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00026.record008
