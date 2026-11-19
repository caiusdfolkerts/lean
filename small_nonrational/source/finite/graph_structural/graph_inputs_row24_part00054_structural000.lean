module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00054Frames
public import GraphInputsRow24Part00054Leaves
public import GraphInputsRow24Part00054Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1e47316c4f1e2b29ca5a87a719a6598e6a5a8e6394e3392e1ba1e0f9e1e26c9725694e479715a5594e5a5535a358d534cd4b46d8751d0f6c370da358ce3a4e331ce8b62e4b52ccb4ac6b16c3ba1d8751cc749ca719e1725e0f43c8f13c2f86836079c15854986585494354341da0cc318e130ce0b12c1b21c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6db6db6db6926d26d24da6934d249349249a49a492692492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 30), (facetIndex 37), (facetIndex 57), (facetIndex 78)]))
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 47), (facetIndex 48)])))
 (.branch 3
 (.leaf ([(facetIndex 56), (facetIndex 59), (facetIndex 62), (facetIndex 64), (facetIndex 68)]))
 (.leaf ([(facetIndex 61), (facetIndex 67), (facetIndex 69), (facetIndex 72), (facetIndex 73), (facetIndex 76)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 44), (facetIndex 46), (facetIndex 49), (facetIndex 54)]))
 (.leaf ([(facetIndex 25), (facetIndex 40), (facetIndex 42), (facetIndex 43), (facetIndex 50)])))
 (.branch 7
 (.leaf ([(facetIndex 24), (facetIndex 29), (facetIndex 55), (facetIndex 77)]))
 (.branch 8
 (.leaf ([(facetIndex 27), (facetIndex 33), (facetIndex 36), (facetIndex 51), (facetIndex 53)]))
 (.leaf ([(facetIndex 26), (facetIndex 31), (facetIndex 32), (facetIndex 34)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "630033003230020230200264707541140455051107087880607856z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 63), (facetIndex 65)]))
 (.leaf ([(facetIndex 84), (facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 41), (facetIndex 58), (facetIndex 70), (facetIndex 71)]))
 (.branch 4
 (.leaf ([(facetIndex 79), (facetIndex 80), (facetIndex 90), (facetIndex 95)]))
 (.leaf ([(facetIndex 45), (facetIndex 60), (facetIndex 74), (facetIndex 75)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 81), (facetIndex 83), (facetIndex 93)]))
 (.branch 7
 (.leaf ([(facetIndex 35), (facetIndex 52), (facetIndex 66)]))
 (.leaf ([(facetIndex 82), (facetIndex 86), (facetIndex 88)]))))
 (.branch 9
 (.leaf ([(facetIndex 87), (facetIndex 94), (facetIndex 98)]))
 (.branch 10
 (.leaf ([(facetIndex 89), (facetIndex 96), (facetIndex 97)]))
 (.leaf ([(facetIndex 91), (facetIndex 92)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "899385aa39787115753300044002200060000040200000600000040002000006z23;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7, 8]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8]
def grouped2_0014 : List Nat := [8]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0017 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0019 : List Nat := [1]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [2, 3, 4]
def grouped3_0022 : List Nat := [3]
def grouped3_0023 : List Nat := [3, 4]
def grouped3_0024 : List Nat := [4]
def grouped3_0025 : List Nat := [5]
def grouped3_0026 : List Nat := [5, 6, 7]
def grouped3_0027 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0028 : List Nat := [6]
def grouped3_0029 : List Nat := [6, 7]
def grouped3_0030 : List Nat := [7]
def grouped3_0031 : List Nat := [8]
def grouped3_0032 : List Nat := [8, 9, 10]
def grouped3_0033 : List Nat := [9]
def grouped3_0034 : List Nat := [9, 10]
def grouped3_0035 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0029\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0034\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0032\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record000" 100

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record000" "{\"ridges\":[[11,641],[11,642],[13,268],[15,292],[16,388],[18,328],[19,352],[20,448],[27,268],[31,98],[32,134],[33,289],[33,292],[36,388],[37,641],[37,642],[43,328],[46,642],[49,641],[49,642],[51,352],[53,194],[53,448],[54,642],[56,268],[59,268],[59,292],[61,268],[61,328],[62,268],[62,388],[64,292],[67,292],[67,352],[68,292],[69,388],[69,448],[72,328],[72,352],[73,328],[73,448],[74,712],[75,904],[76,352],[89,326],[93,712],[96,108],[97,204],[98,228]],\"owners\":[[32,134,[81,83,84,85,89],[3,26,29,34,36,37,86,88]],[31,98,[90,91,94],[9,40,47,50,51,79,86,87]],[53,194,[81,86,93],[10,34,42,50,54,89,92,94]],[11,641,[63,65,74,75],[37,46,49,54]],[37,641,[74,75],[11,46,49,54,63,65]],[49,641,[63,74,75],[11,37,46,54,65]],[11,642,[84,85,93],[37,46,49,54]],[37,642,[93],[11,46,49,54,84,85]],[46,642,[85],[11,37,49,54,84,93]],[49,642,[84,93],[11,37,46,54,85]],[54,642,[84,85],[11,37,46,49,93]],[13,268,[80,82,83,95,96,97],[27,56,59,61,62]],[27,268,[95,96,97],[13,56,59,61,62,80,82,83]],[56,268,[80,82,83,96,97],[13,27,59,61,62,95]],[59,268,[82,83,97],[13,27,56,61,62,80,95,96]],[61,268,[80,83,95],[13,27,56,59,62,82,96,97]],[62,268,[80,82,95,96],[13,27,56,59,61,83,97]],[33,289,[19,71,72,76],[15,41,51,52,59,64,68]],[15,292,[80,87,88,95,96,98],[33,59,64,67,68]],[33,292,[95,96,98],[15,59,64,67,68,80,87,88]],[59,292,[87,88,98],[15,33,64,67,68,80,95,96]],[64,292,[80,87,88,96,98],[15,33,59,67,68,95]],[67,292,[80,88,95],[15,33,59,64,68,87,96,98]],[68,292,[80,87,95,96],[15,33,59,64,67,88,98]],[16,388,[83,88,89,97,98],[36,62,68,69]],[36,388,[97,98],[16,62,68,69,83,88,89]],[62,388,[88,89,98],[16,36,68,69,83,97]],[69,388,[83,88],[16,36,62,68,89,97,98]],[18,328,[82,91,92,96,97],[43,61,72,73]],[43,328,[96,97],[18,61,72,73,82,91,92]],[61,328,[91,92],[18,43,72,73,82,96,97]],[72,328,[82,92,97],[18,43,61,73,91,96]],[73,328,[82,91,96],[18,43,61,72,92,97]],[19,352,[87,91,94,96,98],[51,67,72,76]],[51,352,[96,98],[19,67,72,76,87,91,94]],[67,352,[91,94],[19,51,72,76,87,96,98]],[72,352,[87,94,98],[19,51,67,76,91,96]],[76,352,[87,91,96],[19,51,67,72,94,98]],[20,448,[89,92,94,97,98],[53,69,73,76]],[53,448,[97,98],[20,69,73,76,89,92,94]],[69,448,[92,94],[20,53,73,76,89,97,98]],[73,448,[89,94,98],[20,53,69,76,92,97]],[89,326,[35,82,87],[]],[96,108,[58,79],[]],[97,204,[60,81],[]],[98,228,[66,86],[]],[74,712,[93],[]],[93,712,[74],[]],[75,904,[],[]]],\"edges\":[[22,[13,15,16,27,33,35,36,56,59,61,62,64,67,68,69,80,82,83,87,88,89,95,96,97,98]],[28,[13,18,27,41,43,45,56,59,61,62,71,72,73,75,80,82,83,91,92,95,96,97]],[40,[18,19,20,35,43,51,53,61,67,69,72,73,76,82,87,89,91,92,94,96,97,98]],[43,[11,37,46,49,54,63,65,74,75,84,85,93]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-22,-13],[-53,-9],[-53,-18],[-53,-20],[-53,-30],[-53,-46],[-57,-53],[-58,-53],[-59,-8],[-59,-19],[-59,-21],[-59,-25],[-59,-47],[-59,-49],[-62,-53],[-63,-53],[-11,47,49,50,51,55],[-10,56,57,60],[-24,47,52,59],[-1,32,34,42,43],[-16,42,43],[-22,32,42,43],[-1,50,51,59],[-16,59],[-21,51],[-22,50,59],[-25,50,51],[-2,46,48,49,61,62,63],[-9,61,62,63],[-26,46,48,49,62,63],[-28,48,49,63],[-30,46,49,61],[-31,46,48,61,62],[-12,6,39,40,44],[-3,46,53,54,61,62,64],[-12,61,62,64],[-28,53,54,64],[-33,46,53,54,62,64],[-36,46,54,61],[-37,46,53,61,62],[-4,49,54,55,63,64],[-15,63,64],[-31,54,55,64],[-38,49,54],[-5,48,57,58,62,63],[-18,62,63],[-30,57,58],[-40,48,58,63],[-41,48,57,62],[-6,53,57,60,62,64],[-23,62,64],[-36,57,60],[-40,53,60,64],[-44,53,57,62],[-7,55,58,60,63,64],[-24,63,64],[-38,58,60],[-41,55,60,64],[-55,14,48,53],[-62,27,45],[-63,29,47],[-64,35,52],[-42,59],[-59,42],[-43],[-65,30,36,38,40,41,44],[-66,19,21,22,25],[-67,9,12,15,23,24],[-68,8,10,11,13],[-69,65],[-70,69],[-71,66],[-72,67],[-72,68],[-73,72],[-74,71],[-74,73],[-75,70,74],[75],[-32,76],[-34,76],[-50,77],[-51,77],[-17,78],[-27,78],[-39,78],[-45,79],[-46,79],[-56,79],[-61,79],[-29,80],[-42,80],[-47,81],[-49,81],[-59,81],[-14,82],[-35,82],[-48,83],[-52,83],[-54,83],[-53,84],[-60,84],[-64,84],[-55,85],[-62,85],[-63,85],[-57,86],[-58,86],[-77,87],[-76,87],[-80,88],[-79,88],[-79,-80,89],[-88,90],[-89,91],[-78,90],[-90,92],[-91,93],[-87,92],[-87,-90,93],[-83,94],[-82,94],[-94,95],[-81,95],[-86,96],[-85,96],[-96,97],[-84,97],[-97,98],[-95,98],[-95,-97,99],[-92,-99,100],[-93,-98,100],[-100],[2,3,4,9,12,14,15,26,28,30,31,33,36,37,38,46,48,49,53,54,55,61,62,63,64],[2,5,9,17,18,20,26,28,30,31,39,40,41,43,46,48,49,57,58,61,62,63],[5,6,7,14,18,23,24,30,36,38,40,41,44,48,53,55,57,58,60,62,63,64],[1,16,21,22,25,32,34,42,43,50,51,59]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":49,\"b\":34},{\"tag\":\"incompatible\",\"a\":87,\"b\":27},{\"tag\":\"incompatible\",\"a\":87,\"b\":43},{\"tag\":\"incompatible\",\"a\":87,\"b\":45},{\"tag\":\"incompatible\",\"a\":87,\"b\":61},{\"tag\":\"incompatible\",\"a\":87,\"b\":80},{\"tag\":\"incompatible\",\"a\":91,\"b\":87},{\"tag\":\"incompatible\",\"a\":92,\"b\":87},{\"tag\":\"incompatible\",\"a\":93,\"b\":26},{\"tag\":\"incompatible\",\"a\":93,\"b\":44},{\"tag\":\"incompatible\",\"a\":93,\"b\":46},{\"tag\":\"incompatible\",\"a\":93,\"b\":54},{\"tag\":\"incompatible\",\"a\":93,\"b\":81},{\"tag\":\"incompatible\",\"a\":93,\"b\":83},{\"tag\":\"incompatible\",\"a\":96,\"b\":87},{\"tag\":\"incompatible\",\"a\":97,\"b\":87},{\"tag\":\"mate\",\"ridge\":134,\"a\":32,\"owners\":[81,83,84,85,89]},{\"tag\":\"mate\",\"ridge\":98,\"a\":31,\"owners\":[90,91,94]},{\"tag\":\"mate\",\"ridge\":194,\"a\":53,\"owners\":[81,86,93]},{\"tag\":\"mate\",\"ridge\":641,\"a\":11,\"owners\":[63,65,74,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":37,\"owners\":[74,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":49,\"owners\":[63,74,75]},{\"tag\":\"mate\",\"ridge\":642,\"a\":11,\"owners\":[84,85,93]},{\"tag\":\"mate\",\"ridge\":642,\"a\":37,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":642,\"a\":46,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":642,\"a\":49,\"owners\":[84,93]},{\"tag\":\"mate\",\"ridge\":642,\"a\":54,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":268,\"a\":13,\"owners\":[80,82,83,95,96,97]},{\"tag\":\"mate\",\"ridge\":268,\"a\":27,\"owners\":[95,96,97]},{\"tag\":\"mate\",\"ridge\":268,\"a\":56,\"owners\":[80,82,83,96,97]},{\"tag\":\"mate\",\"ridge\":268,\"a\":59,\"owners\":[82,83,97]},{\"tag\":\"mate\",\"ridge\":268,\"a\":61,\"owners\":[80,83,95]},{\"tag\":\"mate\",\"ridge\":268,\"a\":62,\"owners\":[80,82,95,96]},{\"tag\":\"mate\",\"ridge\":289,\"a\":33,\"owners\":[19,71,72,76]},{\"tag\":\"mate\",\"ridge\":292,\"a\":15,\"owners\":[80,87,88,95,96,98]},{\"tag\":\"mate\",\"ridge\":292,\"a\":33,\"owners\":[95,96,98]},{\"tag\":\"mate\",\"ridge\":292,\"a\":59,\"owners\":[87,88,98]},{\"tag\":\"mate\",\"ridge\":292,\"a\":64,\"owners\":[80,87,88,96,98]},{\"tag\":\"mate\",\"ridge\":292,\"a\":67,\"owners\":[80,88,95]},{\"tag\":\"mate\",\"ridge\":292,\"a\":68,\"owners\":[80,87,95,96]},{\"tag\":\"mate\",\"ridge\":388,\"a\":16,\"owners\":[83,88,89,97,98]},{\"tag\":\"mate\",\"ridge\":388,\"a\":36,\"owners\":[97,98]},{\"tag\":\"mate\",\"ridge\":388,\"a\":62,\"owners\":[88,89,98]},{\"tag\":\"mate\",\"ridge\":388,\"a\":69,\"owners\":[83,88]},{\"tag\":\"mate\",\"ridge\":328,\"a\":18,\"owners\":[82,91,92,96,97]},{\"tag\":\"mate\",\"ridge\":328,\"a\":43,\"owners\":[96,97]},{\"tag\":\"mate\",\"ridge\":328,\"a\":61,\"owners\":[91,92]},{\"tag\":\"mate\",\"ridge\":328,\"a\":72,\"owners\":[82,92,97]},{\"tag\":\"mate\",\"ridge\":328,\"a\":73,\"owners\":[82,91,96]},{\"tag\":\"mate\",\"ridge\":352,\"a\":19,\"owners\":[87,91,94,96,98]},{\"tag\":\"mate\",\"ridge\":352,\"a\":51,\"owners\":[96,98]},{\"tag\":\"mate\",\"ridge\":352,\"a\":67,\"owners\":[91,94]},{\"tag\":\"mate\",\"ridge\":352,\"a\":72,\"owners\":[87,94,98]},{\"tag\":\"mate\",\"ridge\":352,\"a\":76,\"owners\":[87,91,96]},{\"tag\":\"mate\",\"ridge\":448,\"a\":20,\"owners\":[89,92,94,97,98]},{\"tag\":\"mate\",\"ridge\":448,\"a\":53,\"owners\":[97,98]},{\"tag\":\"mate\",\"ridge\":448,\"a\":69,\"owners\":[92,94]},{\"tag\":\"mate\",\"ridge\":448,\"a\":73,\"owners\":[89,94,98]},{\"tag\":\"mate\",\"ridge\":326,\"a\":89,\"owners\":[35,82,87]},{\"tag\":\"mate\",\"ridge\":108,\"a\":96,\"owners\":[58,79]},{\"tag\":\"mate\",\"ridge\":204,\"a\":97,\"owners\":[60,81]},{\"tag\":\"mate\",\"ridge\":228,\"a\":98,\"owners\":[66,86]},{\"tag\":\"mate\",\"ridge\":712,\"a\":74,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":712,\"a\":93,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":904,\"a\":75,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[61,67,69,72,73,76],\"full_literals\":[-65,30,36,38,40,41,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[44,46,49,54],\"full_literals\":[-66,19,21,22,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[27,33,36,51,53],\"full_literals\":[-67,9,12,15,23,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[26,31,32,34],\"full_literals\":[-68,8,10,11,13]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-69,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-70,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,66,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-72,67,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-74,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-74,false,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-75,70,74],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-32,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":65,\"full_literals\":[-34,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":84,\"full_literals\":[-50,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-51,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":41,\"full_literals\":[-17,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":58,\"full_literals\":[-27,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":71,\"full_literals\":[-39,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":79,\"full_literals\":[-45,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":80,\"full_literals\":[-46,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":90,\"full_literals\":[-56,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":95,\"full_literals\":[-61,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":60,\"full_literals\":[-29,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-42,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-47,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-49,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":93,\"full_literals\":[-59,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":35,\"full_literals\":[-14,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":66,\"full_literals\":[-35,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":82,\"full_literals\":[-48,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-52,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":88,\"full_literals\":[-54,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":87,\"full_literals\":[-53,84]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":94,\"full_literals\":[-60,84]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":98,\"full_literals\":[-64,84]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":89,\"full_literals\":[-55,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":96,\"full_literals\":[-62,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":97,\"full_literals\":[-63,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":91,\"full_literals\":[-57,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":92,\"full_literals\":[-58,86]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-80,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-79,false,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-79,-80,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-88,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-89,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-90,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-91,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-87,false,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-87,-90,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0028\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0029\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0028\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0029\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-94,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0033\",\"right_name\":\"grouped3_0035\",\"joined_name\":\"grouped3_0034\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-86,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0033\",\"right_name\":\"grouped3_0035\",\"joined_name\":\"grouped3_0034\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0034\",\"joined_name\":\"grouped3_0032\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-96,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0034\",\"joined_name\":\"grouped3_0032\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-84,false,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0027\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-97,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-95,false,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-95,-97,99],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-92,-99,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-93,-98,100],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[13,15,16,27,33,35,36,56,59,61,62,64,67,68,69,80,82,83,87,88,89,95,96,97,98]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[13,18,27,41,43,45,56,59,61,62,71,72,73,75,80,82,83,91,92,95,96,97]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[18,19,20,35,43,51,53,61,67,69,72,73,76,82,87,89,91,92,94,96,97,98]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[11,37,46,49,54,63,65,74,75,84,85,93]}]}"
  "p cnf 100 138\n-22 -13 0\n-53 -9 0\n-53 -18 0\n-53 -20 0\n-53 -30 0\n-53 -46 0\n-57 -53 0\n-58 -53 0\n-59 -8 0\n-59 -19 0\n-59 -21 0\n-59 -25 0\n-59 -47 0\n-59 -49 0\n-62 -53 0\n-63 -53 0\n-11 47 49 50 51 55 0\n-10 56 57 60 0\n-24 47 52 59 0\n-1 32 34 42 43 0\n-16 42 43 0\n-22 32 42 43 0\n-1 50 51 59 0\n-16 59 0\n-21 51 0\n-22 50 59 0\n-25 50 51 0\n-2 46 48 49 61 62 63 0\n-9 61 62 63 0\n-26 46 48 49 62 63 0\n-28 48 49 63 0\n-30 46 49 61 0\n-31 46 48 61 62 0\n-12 6 39 40 44 0\n-3 46 53 54 61 62 64 0\n-12 61 62 64 0\n-28 53 54 64 0\n-33 46 53 54 62 64 0\n-36 46 54 61 0\n-37 46 53 61 62 0\n-4 49 54 55 63 64 0\n-15 63 64 0\n-31 54 55 64 0\n-38 49 54 0\n-5 48 57 58 62 63 0\n-18 62 63 0\n-30 57 58 0\n-40 48 58 63 0\n-41 48 57 62 0\n-6 53 57 60 62 64 0\n-23 62 64 0\n-36 57 60 0\n-40 53 60 64 0\n-44 53 57 62 0\n-7 55 58 60 63 64 0\n-24 63 64 0\n-38 58 60 0\n-41 55 60 64 0\n-55 14 48 53 0\n-62 27 45 0\n-63 29 47 0\n-64 35 52 0\n-42 59 0\n-59 42 0\n-43 0\n-65 30 36 38 40 41 44 0\n-66 19 21 22 25 0\n-67 9 12 15 23 24 0\n-68 8 10 11 13 0\n-69 65 0\n-70 69 0\n-71 66 0\n-72 67 0\n-72 68 0\n-73 72 0\n-74 71 0\n-74 73 0\n-75 70 74 0\n75 0\n-32 76 0\n-34 76 0\n-50 77 0\n-51 77 0\n-17 78 0\n-27 78 0\n-39 78 0\n-45 79 0\n-46 79 0\n-56 79 0\n-61 79 0\n-29 80 0\n-42 80 0\n-47 81 0\n-49 81 0\n-59 81 0\n-14 82 0\n-35 82 0\n-48 83 0\n-52 83 0\n-54 83 0\n-53 84 0\n-60 84 0\n-64 84 0\n-55 85 0\n-62 85 0\n-63 85 0\n-57 86 0\n-58 86 0\n-77 87 0\n-76 87 0\n-80 88 0\n-79 88 0\n-79 -80 89 0\n-88 90 0\n-89 91 0\n-78 90 0\n-90 92 0\n-91 93 0\n-87 92 0\n-87 -90 93 0\n-83 94 0\n-82 94 0\n-94 95 0\n-81 95 0\n-86 96 0\n-85 96 0\n-96 97 0\n-84 97 0\n-97 98 0\n-95 98 0\n-95 -97 99 0\n-92 -99 100 0\n-93 -98 100 0\n-100 0\n2 3 4 9 12 14 15 26 28 30 31 33 36 37 38 46 48 49 53 54 55 61 62 63 64 0\n2 5 9 17 18 20 26 28 30 31 39 40 41 43 46 48 49 57 58 61 62 63 0\n5 6 7 14 18 23 24 30 36 38 40 41 44 48 53 55 57 58 60 62 63 64 0\n1 16 21 22 25 32 34 42 43 50 51 59 0\n"
  "139 2 5 9 17 18 20 26 28 30 31 39 40 41 46 48 49 57 58 61 62 63 0 65 136 0\n140 1 16 21 22 25 32 34 42 50 51 59 0 65 138 0\n141 92 0 65 117 119 114 109 110 111 82 83 80 81 92 27 25 20 21 64 22 140 0\n142 -99 0 141 134 132 0\n143 90 53 95 0 123 122 97 121 99 62 100 98 96 59 43 37 124 94 44 93 114 116 111 112 85 91 87 88 90 61 60 28 30 32 35 38 39 40 29 36 42 41 135 0\n144 87 59 0 63 24 109 110 82 83 80 81 27 26 23 25 140 0\n145 95 93 0 123 124 121 94 95 98 144 120 114 116 143 112 84 86 2 3 4 5 6 7 8 15 16 90 28 30 33 45 49 48 31 139 0\n146 90 97 0 79 127 126 105 128 101 125 107 54 103 102 104 58 52 108 57 47 53 66 70 71 78 77 75 73 106 56 42 51 50 114 116 112 86 90 34 29 68 0\n147 93 0 142 79 118 115 145 131 127 128 125 126 101 102 103 107 108 104 105 53 47 52 54 57 58 66 70 71 78 76 77 72 75 74 146 120 109 144 82 83 9 10 11 12 13 14 64 17 67 92 1 113 69 89 18 0\n148 -98 0 147 134 133 0\n149 -97 0 148 129 0\n150 -95 0 148 130 0\n151 -96 0 149 127 0\n152 -84 0 149 128 0\n153 -94 0 150 123 0\n154 -81 0 150 124 0\n155 -86 0 151 125 0\n156 -85 0 151 126 0\n157 -53 0 152 101 0\n158 -60 0 152 102 0\n159 -64 0 152 103 0\n160 -83 0 153 121 0\n161 -82 0 153 122 0\n162 -47 0 154 93 0\n163 -49 0 154 94 0\n164 -59 0 154 95 0\n165 -57 0 155 107 0\n166 -58 0 155 108 0\n167 -55 0 156 104 0\n168 -62 0 156 105 0\n169 -63 0 156 106 0\n170 -40 0 157 158 159 53 0\n171 -48 0 160 98 0\n172 -52 0 160 99 0\n173 -54 0 160 100 0\n174 -14 0 161 96 0\n175 -24 0 162 172 164 19 0\n176 -38 0 163 173 44 0\n177 -30 0 165 166 47 0\n178 -36 0 165 158 52 0\n179 -6 0 165 157 158 168 159 50 0\n180 -44 0 165 157 168 54 0\n181 -41 0 167 158 159 58 0\n182 -18 0 168 169 46 0\n183 -23 0 168 159 51 0\n184 -7 0 169 166 158 167 159 55 0\n185 -5 0 171 165 166 168 169 45 0\n186 0 174 171 185 179 182 183 175 177 178 176 170 181 180 184 157 167 165 166 158 168 169 159 137 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5d13c789727299a4eac61da8e33a1e0f9e15c789725994e6c5595554d475a354d3352d8751d0f6c370da358ce364d534cc7362d4b32d2b86d1b26c3ba1e4731e2785c5723c4f0be8a198368381e705614c68962519194358341da0cc318c3382c8b06e0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db49a4924934d24db4924d26d24d3492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 49), (facetIndex 63), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 29), (facetIndex 35), (facetIndex 39), (facetIndex 59), (facetIndex 74)])))
 (.branch 3
 (.leaf ([(facetIndex 43), (facetIndex 66), (facetIndex 67), (facetIndex 68)]))
 (.branch 4
 (.leaf ([(facetIndex 27), (facetIndex 30), (facetIndex 71), (facetIndex 75)]))
 (.leaf ([(facetIndex 33), (facetIndex 41), (facetIndex 48), (facetIndex 51), (facetIndex 52)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 36), (facetIndex 53), (facetIndex 54), (facetIndex 61), (facetIndex 65)]))
 (.leaf ([(facetIndex 28), (facetIndex 31), (facetIndex 55), (facetIndex 72)])))
 (.branch 8
 (.leaf ([(facetIndex 32), (facetIndex 34)]))
 (.branch 9
 (.leaf ([(facetIndex 37), (facetIndex 38)]))
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 60)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3106300222500059100065544004009920401885174763163z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 57), (facetIndex 64)]))
 (.branch 2
 (.leaf ([(facetIndex 73), (facetIndex 76)]))
 (.leaf ([(facetIndex 56), (facetIndex 58), (facetIndex 62)]))))
 (.branch 4
 (.leaf ([(facetIndex 82), (facetIndex 83)]))
 (.branch 5
 (.leaf ([(facetIndex 40), (facetIndex 42), (facetIndex 46), (facetIndex 47), (facetIndex 50)]))
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 80), (facetIndex 81)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6edb69008000000080082000100900104z1e;"⟩
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
def grouped2_0007 : List Nat := [3, 4]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6]
def grouped2_0010 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0011 : List Nat := [6]
def grouped2_0012 : List Nat := [7, 8, 9]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1, 2]
def grouped3_0016 : List Nat := [1]
def grouped3_0017 : List Nat := [1, 2]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [3]
def grouped3_0020 : List Nat := [3, 4, 5]
def grouped3_0021 : List Nat := [4]
def grouped3_0022 : List Nat := [4, 5]
def grouped3_0023 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record002" 53

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record002" "{\"ridges\":[[16,280],[17,392],[19,304],[20,352],[21,385],[21,448],[38,280],[40,298],[42,330],[43,392],[45,304],[47,402],[49,352],[51,448],[54,280],[58,332],[61,304],[63,352],[65,280],[66,280],[66,392],[67,392],[67,448],[68,392],[69,304],[70,448],[78,402],[79,330],[82,300],[83,340]],\"owners\":[[16,280,[77,78,82],[38,54,65,66]],[38,280,[82],[16,54,65,66,77,78]],[54,280,[77,78],[16,38,65,66,82]],[65,280,[78],[16,38,54,66,77,82]],[66,280,[77,82],[16,38,54,65,78]],[21,385,[17,43,47,50,66,68],[51,70]],[17,392,[78,79],[43,66,67,68]],[43,392,[],[17,66,67,68,78,79]],[66,392,[79],[17,43,67,68,78]],[67,392,[78],[17,43,66,68,79]],[68,392,[78,79],[17,43,66,67]],[19,304,[77,80,82,83],[45,61,65,69]],[45,304,[82,83],[19,61,65,69,77,80]],[61,304,[77,80],[19,45,65,69,82,83]],[69,304,[77,82],[19,45,61,65,80,83]],[20,352,[80,81,83],[49,63,69,70]],[49,352,[83],[20,63,69,70,80,81]],[63,352,[80,81],[20,49,69,70,83]],[21,448,[79,81],[51,67,70]],[51,448,[],[21,67,70,79,81]],[67,448,[81],[21,51,70,79]],[70,448,[79],[21,51,67,81]],[40,298,[77],[]],[42,330,[79],[]],[79,330,[42],[]],[47,402,[78],[]],[78,402,[47],[]],[82,300,[56],[]],[58,332,[],[]],[83,340,[62],[]]],\"edges\":[[28,[16,17,38,40,42,43,54,56,58,65,66,67,68,77,78,79,82]],[33,[16,19,38,45,46,47,54,61,62,65,66,69,77,78,80,82,83]],[40,[20,21,42,46,49,51,58,62,63,67,69,70,79,80,81,83]],[42,[17,21,43,47,50,51,66,67,68,70,78,79,81]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-19,-6],[-19,-17],[-19,-18],[-21,-19],[-23,-19],[-28,-19],[-30,-15],[-31,-12],[-31,-30],[-32,-12],[-32,-13],[-32,-30],[-32,-31],[-33,-31],[-33,-32],[-34,-30],[-34,-31],[-36,-19],[-1,30,31,35],[-7,35],[-18,30,31],[-24,31],[-25,30,35],[-5,2,10,13,15,25,27],[-2,31,32],[-10],[-25,32],[-26,31],[-27,31,32],[-3,30,33,35,36],[-11,35,36],[-21,30,33],[-28,30,35],[-4,33,34,36],[-14,36],[-23,33,34],[-5,32,34],[-16],[-26,34],[-29,32],[-8,30],[-9,32],[-32,9],[-13,31],[-31,13],[-35,19],[-20],[-36,22],[-37,14,23,28,29],[-38,10,25,26,27],[-39,6,17,18,21,24],[-40,37],[-41,38],[-42,40,41],[-43,39],[-44,43],[-45,42,44],[45],[-19,46],[-22,46],[-9,47],[-13,47],[-31,48],[-32,48],[-46,49],[-49,50],[-47,-48,51],[-51,52],[-50,-52,53],[-53],[1,2,7,8,9,10,18,19,20,24,25,26,27,30,31,32,35],[1,3,7,11,12,13,18,21,22,24,25,28,30,31,33,35,36],[4,5,9,12,14,16,20,22,23,26,28,29,32,33,34,36],[2,5,10,13,15,16,25,26,27,29,31,32,34]],\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":56,\"b\":36},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":61,\"b\":56},{\"tag\":\"incompatible\",\"a\":63,\"b\":56},{\"tag\":\"incompatible\",\"a\":69,\"b\":56},{\"tag\":\"incompatible\",\"a\":77,\"b\":50},{\"tag\":\"incompatible\",\"a\":78,\"b\":46},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":46},{\"tag\":\"incompatible\",\"a\":79,\"b\":47},{\"tag\":\"incompatible\",\"a\":79,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"incompatible\",\"a\":81,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":78},{\"tag\":\"incompatible\",\"a\":83,\"b\":56},{\"tag\":\"mate\",\"ridge\":280,\"a\":16,\"owners\":[77,78,82]},{\"tag\":\"mate\",\"ridge\":280,\"a\":38,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":280,\"a\":54,\"owners\":[77,78]},{\"tag\":\"mate\",\"ridge\":280,\"a\":65,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":280,\"a\":66,\"owners\":[77,82]},{\"tag\":\"mate\",\"ridge\":385,\"a\":21,\"owners\":[17,43,47,50,66,68]},{\"tag\":\"mate\",\"ridge\":392,\"a\":17,\"owners\":[78,79]},{\"tag\":\"mate\",\"ridge\":392,\"a\":43,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":392,\"a\":66,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":392,\"a\":67,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":392,\"a\":68,\"owners\":[78,79]},{\"tag\":\"mate\",\"ridge\":304,\"a\":19,\"owners\":[77,80,82,83]},{\"tag\":\"mate\",\"ridge\":304,\"a\":45,\"owners\":[82,83]},{\"tag\":\"mate\",\"ridge\":304,\"a\":61,\"owners\":[77,80]},{\"tag\":\"mate\",\"ridge\":304,\"a\":69,\"owners\":[77,82]},{\"tag\":\"mate\",\"ridge\":352,\"a\":20,\"owners\":[80,81,83]},{\"tag\":\"mate\",\"ridge\":352,\"a\":49,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":352,\"a\":63,\"owners\":[80,81]},{\"tag\":\"mate\",\"ridge\":448,\"a\":21,\"owners\":[79,81]},{\"tag\":\"mate\",\"ridge\":448,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":448,\"a\":67,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":448,\"a\":70,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":298,\"a\":40,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":330,\"a\":42,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":330,\"a\":79,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":402,\"a\":47,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":402,\"a\":78,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":300,\"a\":82,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":332,\"a\":58,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":340,\"a\":83,\"owners\":[62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[49,63,69,70],\"full_literals\":[-37,14,23,28,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[43,66,67,68],\"full_literals\":[-38,10,25,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[36,53,54,61,65],\"full_literals\":[-39,6,17,18,21,24]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-41,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-42,40,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-44,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-45,42,44],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":56,\"full_literals\":[-19,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":62,\"full_literals\":[-22,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":42,\"full_literals\":[-9,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":47,\"full_literals\":[-13,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-31,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-32,48]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-48,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-50,-52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":28,\"owners\":[16,17,38,40,42,43,54,56,58,65,66,67,68,77,78,79,82]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[16,19,38,45,46,47,54,61,62,65,66,69,77,78,80,82,83]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[20,21,42,46,49,51,58,62,63,67,69,70,79,80,81,83]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[17,21,43,47,50,51,66,67,68,70,78,79,81]}]}"
  "p cnf 53 74\n-19 -6 0\n-19 -17 0\n-19 -18 0\n-21 -19 0\n-23 -19 0\n-28 -19 0\n-30 -15 0\n-31 -12 0\n-31 -30 0\n-32 -12 0\n-32 -13 0\n-32 -30 0\n-32 -31 0\n-33 -31 0\n-33 -32 0\n-34 -30 0\n-34 -31 0\n-36 -19 0\n-1 30 31 35 0\n-7 35 0\n-18 30 31 0\n-24 31 0\n-25 30 35 0\n-5 2 10 13 15 25 27 0\n-2 31 32 0\n-10 0\n-25 32 0\n-26 31 0\n-27 31 32 0\n-3 30 33 35 36 0\n-11 35 36 0\n-21 30 33 0\n-28 30 35 0\n-4 33 34 36 0\n-14 36 0\n-23 33 34 0\n-5 32 34 0\n-16 0\n-26 34 0\n-29 32 0\n-8 30 0\n-9 32 0\n-32 9 0\n-13 31 0\n-31 13 0\n-35 19 0\n-20 0\n-36 22 0\n-37 14 23 28 29 0\n-38 10 25 26 27 0\n-39 6 17 18 21 24 0\n-40 37 0\n-41 38 0\n-42 40 41 0\n-43 39 0\n-44 43 0\n-45 42 44 0\n45 0\n-19 46 0\n-22 46 0\n-9 47 0\n-13 47 0\n-31 48 0\n-32 48 0\n-46 49 0\n-49 50 0\n-47 -48 51 0\n-51 52 0\n-50 -52 53 0\n-53 0\n1 2 7 8 9 10 18 19 20 24 25 26 27 30 31 32 35 0\n1 3 7 11 12 13 18 21 22 24 25 28 30 31 33 35 36 0\n4 5 9 12 14 16 20 22 23 26 28 29 32 33 34 36 0\n2 5 10 13 15 16 25 26 27 29 31 32 34 0\n"
  "75 -38 25 26 27 0 26 50 0\n76 1 2 7 8 9 18 19 24 25 26 27 30 31 32 35 0 26 47 71 0\n77 4 5 9 12 14 22 23 26 28 29 32 33 34 36 0 38 47 73 0\n78 2 5 13 15 25 26 27 29 31 32 34 0 26 38 74 0\n79 30 31 32 19 0 29 28 25 22 42 27 46 20 41 19 21 76 0\n80 15 34 2 13 25 26 27 29 31 32 0 26 78 24 0\n81 31 32 19 0 40 27 25 28 29 44 79 7 16 80 0\n82 32 46 0 60 48 35 59 46 40 42 81 8 9 14 17 33 34 36 39 37 77 0\n83 46 0 59 60 46 48 20 31 82 10 11 12 13 15 23 33 19 21 22 30 32 72 0\n84 49 0 83 65 0\n85 50 0 84 66 0\n86 -52 0 85 70 69 0\n87 -51 0 86 68 0\n88 -32 0 87 43 64 61 67 0\n89 -25 0 88 27 0\n90 -29 0 88 40 0\n91 31 0 88 89 90 58 22 28 29 81 75 1 2 3 4 5 6 18 53 51 35 55 49 56 52 57 54 0\n92 13 0 91 45 0\n93 48 0 91 63 0\n94 47 0 92 62 0\n95 0 94 93 87 67 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record021
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5d13c729aa36ac6719661da2e4ba1e0f971e25c96a55936539e16c571565555351d70d8b52d8751d0f6c370da358cd31cd8b52ccb8ad2b2ae1b26c5ba1d8791d4731e2749c6785e0f43c2f07e8a0e8560d9c1a25894a4395152515435a0cc314c3382c8b0ac1b81c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6d36d349369b4924da6d24da49a492493492492691249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 69), (facetIndex 70), (facetIndex 71)]))
 (.leaf ([(facetIndex 34), (facetIndex 61), (facetIndex 62), (facetIndex 63)])))
 (.branch 3
 (.leaf ([(facetIndex 25), (facetIndex 47), (facetIndex 73), (facetIndex 77)]))
 (.leaf ([(facetIndex 26), (facetIndex 42), (facetIndex 53), (facetIndex 56), (facetIndex 66)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 33), (facetIndex 44), (facetIndex 48), (facetIndex 51), (facetIndex 52)]))
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 43)])))
 (.branch 7
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 59), (facetIndex 60)]))
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 32), (facetIndex 35), (facetIndex 37)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "100100000c024ec0301c804404aedb78e67dbf0dz13;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 36), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 45), (facetIndex 67), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 79), (facetIndex 80)]))
 (.branch 4
 (.leaf ([(facetIndex 81), (facetIndex 83)]))
 (.leaf ([(facetIndex 49), (facetIndex 72)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 54), (facetIndex 85)]))
 (.leaf ([(facetIndex 27), (facetIndex 55), (facetIndex 57), (facetIndex 58), (facetIndex 84)])))
 (.branch 8
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 76)]))
 (.branch 9
 (.leaf ([(facetIndex 50), (facetIndex 78)]))
 (.leaf ([(facetIndex 82)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "56393228077704000110000000066065000840001z11;6z1b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6, 7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1]
def grouped3_0009 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0011 : List Nat := [1]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [2, 3, 4]
def grouped3_0014 : List Nat := [3]
def grouped3_0015 : List Nat := [3, 4]
def grouped3_0016 : List Nat := [4]
def grouped3_0017 : List Nat := [5]
def grouped3_0018 : List Nat := [5, 6]
def grouped3_0019 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0020 : List Nat := [6]
def grouped3_0021 : List Nat := [7]
def grouped3_0022 : List Nat := [7, 8, 9]
def grouped3_0023 : List Nat := [8]
def grouped3_0024 : List Nat := [8, 9]
def grouped3_0025 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record021" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record021" 52

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record021" "{\"ridges\":[[14,292],[17,296],[31,292],[33,194],[42,296],[44,194],[48,194],[49,354],[51,448],[52,194],[56,296],[60,292],[62,292],[66,296],[69,296],[72,368],[79,390],[80,708],[81,216],[83,330]],\"owners\":[[33,194,[81,83],[10,44,48,51,52,79,80]],[44,194,[79,80],[10,33,48,51,52,81,83]],[48,194,[79,80,83],[10,33,44,51,52,81]],[52,194,[79,81,83],[10,33,44,48,51,80]],[14,292,[75,78,84,85],[31,56,60,62]],[31,292,[84,85],[14,56,60,62,75,78]],[60,292,[75,78],[14,31,56,62,84,85]],[62,292,[75,84],[14,31,56,60,78,85]],[17,296,[75,82,84],[42,56,66,69]],[42,296,[84],[17,56,66,69,75,82]],[56,296,[82],[17,42,66,69,75,84]],[66,296,[75,82],[17,42,56,69,84]],[69,296,[75,84],[17,42,56,66,82]],[51,448,[],[20,63,70,79,83]],[79,390,[36],[]],[83,330,[45],[]],[49,354,[78],[]],[80,708,[64],[]],[81,216,[67],[]],[72,368,[85],[]]],\"edges\":[[37,[14,17,31,42,49,50,56,60,62,66,69,72,75,78,82,84,85]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record021" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record021\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-4,26,28],[-7,24,25],[-9,24,25,28],[-13,24,26,28],[-1,22,23,29,30],[-3,29,30],[-15,22,23],[-16,22,29],[-2,22,27,29],[-6,29],[-14,27],[-18,22,27],[-20,22,29],[-12],[-24,5],[-28,8],[-10,23],[-25,17],[-26,19],[-21,30],[-31,4,7,9,12,13],[-32,31],[-33,32],[-34,33],[34],[-5,35],[-17,35],[-8,36],[-19,36],[-24,37],[-25,37],[-26,38],[-28,38],[-30,39],[-29,40],[-22,41],[-11,42],[-23,42],[-27,43],[-36,44],[-35,44],[-38,45],[-45,46],[-37,46],[-44,-46,47],[-40,48],[-39,48],[-43,49],[-42,49],[-49,50],[-41,50],[-50,51],[-48,51],[-47,-51,52],[-52],[1,2,3,6,10,11,14,15,16,18,20,21,22,23,27,29,30]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":194,\"a\":33,\"owners\":[81,83]},{\"tag\":\"mate\",\"ridge\":194,\"a\":44,\"owners\":[79,80]},{\"tag\":\"mate\",\"ridge\":194,\"a\":48,\"owners\":[79,80,83]},{\"tag\":\"mate\",\"ridge\":194,\"a\":52,\"owners\":[79,81,83]},{\"tag\":\"mate\",\"ridge\":292,\"a\":14,\"owners\":[75,78,84,85]},{\"tag\":\"mate\",\"ridge\":292,\"a\":31,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":292,\"a\":60,\"owners\":[75,78]},{\"tag\":\"mate\",\"ridge\":292,\"a\":62,\"owners\":[75,84]},{\"tag\":\"mate\",\"ridge\":296,\"a\":17,\"owners\":[75,82,84]},{\"tag\":\"mate\",\"ridge\":296,\"a\":42,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":296,\"a\":56,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":296,\"a\":66,\"owners\":[75,82]},{\"tag\":\"mate\",\"ridge\":296,\"a\":69,\"owners\":[75,84]},{\"tag\":\"mate\",\"ridge\":448,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":390,\"a\":79,\"owners\":[36]},{\"tag\":\"mate\",\"ridge\":330,\"a\":83,\"owners\":[45]},{\"tag\":\"mate\",\"ridge\":354,\"a\":49,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":708,\"a\":80,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":216,\"a\":81,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":368,\"a\":72,\"owners\":[85]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[33,44,48,51,52],\"full_literals\":[-31,4,7,9,12,13]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-32,31,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-33,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-34,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":36,\"full_literals\":[-5,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":64,\"full_literals\":[-17,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":45,\"full_literals\":[-8,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-19,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":79,\"full_literals\":[-24,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":80,\"full_literals\":[-25,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":81,\"full_literals\":[-26,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-28,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-30,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-29,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":75,\"full_literals\":[-22,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":50,\"full_literals\":[-11,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":78,\"full_literals\":[-23,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":82,\"full_literals\":[-27,43]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[14,17,31,42,49,50,56,60,62,66,69,72,75,78,82,84,85]}]}"
  "p cnf 52 56\n-4 26 28 0\n-7 24 25 0\n-9 24 25 28 0\n-13 24 26 28 0\n-1 22 23 29 30 0\n-3 29 30 0\n-15 22 23 0\n-16 22 29 0\n-2 22 27 29 0\n-6 29 0\n-14 27 0\n-18 22 27 0\n-20 22 29 0\n-12 0\n-24 5 0\n-28 8 0\n-10 23 0\n-25 17 0\n-26 19 0\n-21 30 0\n-31 4 7 9 12 13 0\n-32 31 0\n-33 32 0\n-34 33 0\n34 0\n-5 35 0\n-17 35 0\n-8 36 0\n-19 36 0\n-24 37 0\n-25 37 0\n-26 38 0\n-28 38 0\n-30 39 0\n-29 40 0\n-22 41 0\n-11 42 0\n-23 42 0\n-27 43 0\n-36 44 0\n-35 44 0\n-38 45 0\n-45 46 0\n-37 46 0\n-44 -46 47 0\n-40 48 0\n-39 48 0\n-43 49 0\n-42 49 0\n-49 50 0\n-41 50 0\n-50 51 0\n-48 51 0\n-47 -51 52 0\n-52 0\n1 2 3 6 10 11 14 15 16 18 20 21 22 23 27 29 30 0\n"
  "57 -31 4 7 9 13 0 14 21 0\n58 33 0 25 24 0\n59 32 0 58 23 0\n60 31 0 59 22 0\n61 46 0 60 43 44 42 30 31 32 33 2 4 1 3 57 0\n62 44 0 60 40 41 28 29 26 27 16 19 15 18 3 1 2 4 57 0\n63 47 0 62 61 45 0\n64 -51 0 63 55 54 0\n65 -50 0 64 52 0\n66 -48 0 64 53 0\n67 -49 0 65 50 0\n68 -41 0 65 51 0\n69 -40 0 66 46 0\n70 -39 0 66 47 0\n71 -43 0 67 48 0\n72 -42 0 67 49 0\n73 -22 0 68 36 0\n74 -29 0 69 35 0\n75 -30 0 70 34 0\n76 -27 0 71 39 0\n77 -11 0 72 37 0\n78 -23 0 72 38 0\n79 -3 0 74 75 6 0\n80 -6 0 74 10 0\n81 -16 0 74 73 8 0\n82 -20 0 74 73 13 0\n83 -21 0 75 20 0\n84 -14 0 76 11 0\n85 -2 0 76 73 74 9 0\n86 -18 0 76 73 12 0\n87 -10 0 78 17 0\n88 -1 0 78 73 74 75 5 0\n89 -15 0 78 73 7 0\n90 0 80 85 88 79 87 77 84 89 81 86 82 83 73 78 76 74 75 56 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record021_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record022
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "174e315c4f172e295a4eb86b19c669966558d64d876c3a8e6394e8b92e8791e1783eb15c56956535475a358d5362d4b61d176c370da358cd31ce8b62d4b8ad2b86c5ba1d8791d4731e2749ca719e1725c570de0f43c8f13c2f07dc44b03c7092a0e839a14c5154358342d0768330c530ce0b0ac1b"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36d36d369b6db6db69b6926d24da4924da49b4924db4db6da49b691249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 26), (facetIndex 41), (facetIndex 43), (facetIndex 46)]))
 (.leaf ([(facetIndex 35), (facetIndex 39), (facetIndex 52), (facetIndex 65)])))
 (.branch 3
 (.leaf ([(facetIndex 22), (facetIndex 66), (facetIndex 70), (facetIndex 85), (facetIndex 89)]))
 (.leaf ([(facetIndex 28), (facetIndex 40), (facetIndex 47), (facetIndex 48)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 42), (facetIndex 51), (facetIndex 55), (facetIndex 64)]))
 (.leaf ([(facetIndex 53), (facetIndex 60), (facetIndex 61)])))
 (.branch 7
 (.leaf ([(facetIndex 21), (facetIndex 27), (facetIndex 82)]))
 (.leaf ([(facetIndex 54), (facetIndex 56), (facetIndex 59)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1001018000000008008c02de079e9803600103200200003c000bz10;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 24), (facetIndex 45), (facetIndex 87)]))
 (.leaf ([(facetIndex 58), (facetIndex 73), (facetIndex 91)])))
 (.branch 3
 (.leaf ([(facetIndex 68), (facetIndex 86), (facetIndex 88)]))
 (.leaf ([(facetIndex 77), (facetIndex 90), (facetIndex 92)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 25), (facetIndex 44), (facetIndex 49), (facetIndex 50)]))
 (.leaf ([(facetIndex 33), (facetIndex 57), (facetIndex 62), (facetIndex 63)])))
 (.branch 7
 (.leaf ([(facetIndex 23), (facetIndex 29), (facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 34), (facetIndex 36), (facetIndex 37), (facetIndex 74), (facetIndex 75), (facetIndex 79)]))
 (.branch 8
 (.leaf ([(facetIndex 38), (facetIndex 67), (facetIndex 69), (facetIndex 71), (facetIndex 76), (facetIndex 78), (facetIndex 81), (facetIndex 83), (facetIndex 84)]))
 (.leaf ([(facetIndex 72), (facetIndex 80)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3130202077078673766187072700055000150000004400004000007660656666000406z17;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4, 5]
def grouped2_0003 : List Nat := [4, 5, 6, 7]
def grouped2_0004 : List Nat := [6]
def grouped2_0005 : List Nat := [6, 7]
def grouped2_0006 : List Nat := [7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1]
def grouped3_0009 : List Nat := [0, 1, 2, 3]
def grouped3_0011 : List Nat := [1]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [2, 3]
def grouped3_0014 : List Nat := [3]
def grouped3_0015 : List Nat := [4, 5]
def grouped3_0016 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0017 : List Nat := [6]
def grouped3_0018 : List Nat := [6, 7, 8]
def grouped3_0019 : List Nat := [7, 8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record022" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record022" 49

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record022" "{\"ridges\":[[4,82],[11,84],[28,84],[40,82],[47,82],[48,82],[53,84],[54,524],[56,524],[59,524],[60,84],[61,84],[69,534],[71,550],[74,142],[86,344],[88,368],[90,344],[92,368]],\"owners\":[[4,82,[67,76,78,79,86,88],[28,40,47,48]],[40,82,[76,78,79,88],[4,28,47,48,67,86]],[47,82,[67,78,79,86],[4,28,40,48,76,88]],[48,82,[67,76,79,86,88],[4,28,40,47,78]],[54,524,[71,74,75,91],[9,26,56,59,69]],[56,524,[69,74,75,91],[9,26,54,59,71]],[59,524,[69,71,75],[9,26,54,56,74,91]],[11,84,[67,76,78,79,90,92],[28,53,60,61]],[28,84,[90,92],[11,53,60,61,67,76,78,79]],[53,84,[76,78,79,92],[11,28,60,61,67,90]],[60,84,[67,78,79,90],[11,28,53,61,76,92]],[61,84,[67,76,79,90,92],[11,28,53,60,78]],[74,142,[24,73],[]],[69,534,[30],[]],[71,550,[34],[]],[86,344,[90],[]],[90,344,[86],[]],[88,368,[92],[]],[92,368,[88],[]]],\"edges\":[[31,[4,11,28,40,47,48,53,60,61,67,76,78,79,86,88,90,92]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record022" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record022\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-18,-3],[-18,-5],[-24,-3],[-24,-5],[-25,-3],[-25,-5],[-26,-3],[-26,-5],[-27,-18],[-27,-24],[-27,-25],[-27,-26],[-1,18,24,25,26,28,29],[-9,24,25,26,29],[-10,18,25,26,28],[-11,18,24,26,28,29],[-13,20,22,23,31],[-14,19,22,23,31],[-15,19,20,23],[-2,18,24,25,26,30,32],[-6,30,32],[-12,24,25,26,32],[-16,18,25,26,30],[-17,18,24,26,30,32],[-22,4,21],[-19,7],[-20,8],[-28,30],[-30,28],[-29,32],[-32,29],[-33,3,5,27],[-34,13,14,15],[-35,33],[-35,34],[-36,35],[-37,36],[37],[-4,38],[-21,39],[-31,39],[-28,40],[-29,40],[-30,41],[-32,41],[-7,42],[-8,42],[-23,42],[-39,43],[-38,43],[-40,-41,44],[-44,45],[-43,-44,46],[-42,47],[-47,48],[-45,-48,49],[-46,49],[-49],[1,2,6,9,10,11,12,16,17,18,24,25,26,28,29,30,32]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":67,\"b\":21},{\"tag\":\"incompatible\",\"a\":67,\"b\":27},{\"tag\":\"incompatible\",\"a\":76,\"b\":21},{\"tag\":\"incompatible\",\"a\":76,\"b\":27},{\"tag\":\"incompatible\",\"a\":78,\"b\":21},{\"tag\":\"incompatible\",\"a\":78,\"b\":27},{\"tag\":\"incompatible\",\"a\":79,\"b\":21},{\"tag\":\"incompatible\",\"a\":79,\"b\":27},{\"tag\":\"incompatible\",\"a\":82,\"b\":67},{\"tag\":\"incompatible\",\"a\":82,\"b\":76},{\"tag\":\"incompatible\",\"a\":82,\"b\":78},{\"tag\":\"incompatible\",\"a\":82,\"b\":79},{\"tag\":\"mate\",\"ridge\":82,\"a\":4,\"owners\":[67,76,78,79,86,88]},{\"tag\":\"mate\",\"ridge\":82,\"a\":40,\"owners\":[76,78,79,88]},{\"tag\":\"mate\",\"ridge\":82,\"a\":47,\"owners\":[67,78,79,86]},{\"tag\":\"mate\",\"ridge\":82,\"a\":48,\"owners\":[67,76,79,86,88]},{\"tag\":\"mate\",\"ridge\":524,\"a\":54,\"owners\":[71,74,75,91]},{\"tag\":\"mate\",\"ridge\":524,\"a\":56,\"owners\":[69,74,75,91]},{\"tag\":\"mate\",\"ridge\":524,\"a\":59,\"owners\":[69,71,75]},{\"tag\":\"mate\",\"ridge\":84,\"a\":11,\"owners\":[67,76,78,79,90,92]},{\"tag\":\"mate\",\"ridge\":84,\"a\":28,\"owners\":[90,92]},{\"tag\":\"mate\",\"ridge\":84,\"a\":53,\"owners\":[76,78,79,92]},{\"tag\":\"mate\",\"ridge\":84,\"a\":60,\"owners\":[67,78,79,90]},{\"tag\":\"mate\",\"ridge\":84,\"a\":61,\"owners\":[67,76,79,90,92]},{\"tag\":\"mate\",\"ridge\":142,\"a\":74,\"owners\":[24,73]},{\"tag\":\"mate\",\"ridge\":534,\"a\":69,\"owners\":[30]},{\"tag\":\"mate\",\"ridge\":550,\"a\":71,\"owners\":[34]},{\"tag\":\"mate\",\"ridge\":344,\"a\":86,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":344,\"a\":90,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":368,\"a\":88,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":368,\"a\":92,\"owners\":[88]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[21,27,82],\"full_literals\":[-33,3,5,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[54,56,59],\"full_literals\":[-34,13,14,15]},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0005\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0005\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-35,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-36,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-37,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":24,\"full_literals\":[-4,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-21,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":91,\"full_literals\":[-31,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":86,\"full_literals\":[-28,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":88,\"full_literals\":[-29,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":90,\"full_literals\":[-30,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":92,\"full_literals\":[-32,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":30,\"full_literals\":[-7,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":34,\"full_literals\":[-8,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-23,42]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-41,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-43,-44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":31,\"owners\":[4,11,28,40,47,48,53,60,61,67,76,78,79,86,88,90,92]}]}"
  "p cnf 49 59\n-18 -3 0\n-18 -5 0\n-24 -3 0\n-24 -5 0\n-25 -3 0\n-25 -5 0\n-26 -3 0\n-26 -5 0\n-27 -18 0\n-27 -24 0\n-27 -25 0\n-27 -26 0\n-1 18 24 25 26 28 29 0\n-9 24 25 26 29 0\n-10 18 25 26 28 0\n-11 18 24 26 28 29 0\n-13 20 22 23 31 0\n-14 19 22 23 31 0\n-15 19 20 23 0\n-2 18 24 25 26 30 32 0\n-6 30 32 0\n-12 24 25 26 32 0\n-16 18 25 26 30 0\n-17 18 24 26 30 32 0\n-22 4 21 0\n-19 7 0\n-20 8 0\n-28 30 0\n-30 28 0\n-29 32 0\n-32 29 0\n-33 3 5 27 0\n-34 13 14 15 0\n-35 33 0\n-35 34 0\n-36 35 0\n-37 36 0\n37 0\n-4 38 0\n-21 39 0\n-31 39 0\n-28 40 0\n-29 40 0\n-30 41 0\n-32 41 0\n-7 42 0\n-8 42 0\n-23 42 0\n-39 43 0\n-38 43 0\n-40 -41 44 0\n-44 45 0\n-43 -44 46 0\n-42 47 0\n-47 48 0\n-45 -48 49 0\n-46 49 0\n-49 0\n1 2 6 9 10 11 12 16 17 18 24 25 26 28 29 30 32 0\n"
  "60 36 0 38 37 0\n61 35 0 60 36 0\n62 33 0 61 34 0\n63 34 0 61 35 0\n64 -46 0 58 57 0\n65 42 43 0 63 50 39 49 40 25 41 46 47 48 26 27 19 18 17 33 0\n66 -27 30 32 0 28 21 30 9 10 11 12 20 23 24 13 15 16 22 14 59 0\n67 18 24 25 26 30 32 0 30 14 22 28 21 20 23 24 13 15 16 59 0\n68 -18 27 0 62 1 2 32 0\n69 -24 27 0 62 3 4 32 0\n70 -25 27 0 62 5 6 32 0\n71 30 32 0 62 66 68 69 70 67 7 8 32 0\n72 -44 0 64 58 52 53 56 65 55 54 0\n73 -30 0 72 29 44 42 51 0\n74 32 0 73 71 0\n75 29 0 74 31 0\n76 41 0 74 45 0\n77 40 0 75 43 0\n78 0 77 76 72 51 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record022_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record051
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "7c9caaaa6a3a1e9c6a9966a59568d876638ae1b89e1783e9c6a9a66391e5c5a9565a55558d475634ad1b49d1743de0dc3a8e6358e9394d538cc73a2d8b8acab1ae1b26c5b0ee8731e2749ca785d1725c3743c4f61946198562382e07985514651548d0b41da0d8350e2318e1314c8b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db69a69a49249b6da69a692492492492492492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 67), (facetIndex 69), (facetIndex 71)]))
 (.branch 2
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 77), (facetIndex 85)]))
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 92)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 87), (facetIndex 89)]))
 (.leaf ([(facetIndex 91), (facetIndex 95)])))
 (.branch 6
 (.leaf ([(facetIndex 93), (facetIndex 94)]))
 (.leaf ([(facetIndex 96)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "696a81860800000a448z36;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [3, 4, 5, 6]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record051" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record051" 45

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record051" "{\"ridges\":[[10,529],[10,530],[12,545],[15,641],[15,642],[35,529],[35,530],[38,545],[38,546],[40,641],[40,642],[44,529],[44,530],[47,545],[49,642],[51,529],[51,530],[51,545],[53,529],[53,530],[54,529],[54,641],[54,642],[56,545],[57,545],[57,641],[57,642],[59,641],[59,642],[67,564],[69,660],[71,676],[74,568],[75,664],[76,641],[76,680],[77,624],[85,564],[89,676],[92,568],[93,664],[94,680],[95,624]],\"owners\":[[10,529,[67,69,74,75,77],[35,44,51,53,54]],[35,529,[74,75,77],[10,44,51,53,54,67,69]],[44,529,[67,69,77],[10,35,51,53,54,74,75]],[51,529,[69,75],[10,35,44,53,54,67,74,77]],[53,529,[67,69,74,75],[10,35,44,51,54,77]],[54,529,[67,74,77],[10,35,44,51,53,69,75]],[10,530,[85,87,92,93,95],[35,44,51,53,54]],[35,530,[92,93,95],[10,44,51,53,54,85,87]],[44,530,[85,87,95],[10,35,51,53,54,92,93]],[51,530,[87,93],[10,35,44,53,54,85,92,95]],[53,530,[85,87,92,93],[10,35,44,51,54,95]],[12,545,[67,71,74,76,77],[38,47,51,56,57]],[38,545,[74,76,77],[12,47,51,56,57,67,71]],[47,545,[67,71,77],[12,38,51,56,57,74,76]],[51,545,[71,76],[12,38,47,56,57,67,74,77]],[56,545,[67,71,74,76],[12,38,47,51,57,77]],[57,545,[67,74,77],[12,38,47,51,56,71,76]],[38,546,[92,94,95],[12,47,51,56,57,85,89]],[15,641,[69,71,75,76],[40,49,54,57,59]],[40,641,[75,76],[15,49,54,57,59,69,71]],[54,641,[71,76],[15,40,49,57,59,69,75]],[57,641,[69,75],[15,40,49,54,59,71,76]],[59,641,[69,71,75,76],[15,40,49,54,57]],[76,641,[15,40,54,59,69],[49,57,71,75]],[15,642,[87,89,93,94],[40,49,54,57,59]],[40,642,[93,94],[15,49,54,57,59,87,89]],[49,642,[87,89],[15,40,54,57,59,93,94]],[54,642,[89,94],[15,40,49,57,59,87,93]],[57,642,[87,93],[15,40,49,54,59,89,94]],[59,642,[87,89,93,94],[15,40,49,54,57]],[67,564,[85],[]],[85,564,[67],[]],[69,660,[87],[]],[71,676,[89],[]],[89,676,[71],[]],[74,568,[92],[]],[92,568,[74],[]],[75,664,[93],[]],[93,664,[75],[]],[76,680,[94],[]],[94,680,[76],[]],[77,624,[95],[]],[95,624,[77],[]]],\"edges\":[[34,[10,35,44,51,53,54,67,69,74,75,77,85,87,92,93,95]],[38,[12,38,47,51,56,57,67,71,74,76,77,85,89,92,94,95]],[43,[15,40,49,54,57,59,69,71,75,76,87,89,93,94]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record051" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record051\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-3],[-10,-6],[-15,-10],[-21,-20],[-24,-16],[-24,-18],[-25,-16],[-25,-24],[-27,-21],[-1,16,17,19,20,22],[-4,19,20,22],[-7,16,17,22],[-10,17,20],[-11,16,17,19,20],[-12,16,19,22],[-1,23,24,26,27,29],[-4,26,27,29],[-7,23,24,29],[-10,24,27],[-11,23,24,26,27],[-2,16,18,19,21,22],[-5,19,21,22],[-8,16,18,22],[-10,18,21],[-13,16,18,19,21],[-14,16,19,22],[-5,26,28,29],[-3,17,18,20,21],[-6,20,21],[-12,18,21],[-14,17,20],[-15,17,18,20,21],[-21,3,6,12,15,17],[-3,24,25,27,28],[-6,27,28],[-9,24,25],[-12,25,28],[-14,24,27],[-15,24,25,27,28],[-16,23],[-23,16],[-17,24],[-18,25],[-25,18],[-19,26],[-26,19],[-20,27],[-27,20],[-21,28],[-28,21],[-22,29],[-29,22],[-30,16,17,18],[-16,30],[-17,30],[-18,30],[-19,31],[-22,31],[-23,31],[-20,32],[-21,32],[-26,32],[-33,24,25],[-24,33],[-25,33],[-29,34],[-27,35],[-28,35],[-32,36],[-31,36],[-31,-32,37],[-38,30,36],[-36,38],[-37,39],[-30,38],[-30,-36,39],[-33,40],[-33,-34,41],[-35,42],[-42,43],[-40,43],[-40,-42,44],[-41,44],[-38,-44,45],[-39,-43,45],[-45],[1,4,7,10,11,12,16,17,19,20,22,23,24,26,27,29],[2,5,8,10,13,14,16,18,19,21,22,23,25,26,28,29],[3,6,9,12,14,15,17,18,20,21,24,25,27,28]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":51,\"b\":15},{\"tag\":\"incompatible\",\"a\":51,\"b\":40},{\"tag\":\"incompatible\",\"a\":59,\"b\":51},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":87,\"b\":67},{\"tag\":\"incompatible\",\"a\":87,\"b\":71},{\"tag\":\"incompatible\",\"a\":89,\"b\":67},{\"tag\":\"incompatible\",\"a\":89,\"b\":87},{\"tag\":\"incompatible\",\"a\":93,\"b\":76},{\"tag\":\"mate\",\"ridge\":529,\"a\":10,\"owners\":[67,69,74,75,77]},{\"tag\":\"mate\",\"ridge\":529,\"a\":35,\"owners\":[74,75,77]},{\"tag\":\"mate\",\"ridge\":529,\"a\":44,\"owners\":[67,69,77]},{\"tag\":\"mate\",\"ridge\":529,\"a\":51,\"owners\":[69,75]},{\"tag\":\"mate\",\"ridge\":529,\"a\":53,\"owners\":[67,69,74,75]},{\"tag\":\"mate\",\"ridge\":529,\"a\":54,\"owners\":[67,74,77]},{\"tag\":\"mate\",\"ridge\":530,\"a\":10,\"owners\":[85,87,92,93,95]},{\"tag\":\"mate\",\"ridge\":530,\"a\":35,\"owners\":[92,93,95]},{\"tag\":\"mate\",\"ridge\":530,\"a\":44,\"owners\":[85,87,95]},{\"tag\":\"mate\",\"ridge\":530,\"a\":51,\"owners\":[87,93]},{\"tag\":\"mate\",\"ridge\":530,\"a\":53,\"owners\":[85,87,92,93]},{\"tag\":\"mate\",\"ridge\":545,\"a\":12,\"owners\":[67,71,74,76,77]},{\"tag\":\"mate\",\"ridge\":545,\"a\":38,\"owners\":[74,76,77]},{\"tag\":\"mate\",\"ridge\":545,\"a\":47,\"owners\":[67,71,77]},{\"tag\":\"mate\",\"ridge\":545,\"a\":51,\"owners\":[71,76]},{\"tag\":\"mate\",\"ridge\":545,\"a\":56,\"owners\":[67,71,74,76]},{\"tag\":\"mate\",\"ridge\":545,\"a\":57,\"owners\":[67,74,77]},{\"tag\":\"mate\",\"ridge\":546,\"a\":38,\"owners\":[92,94,95]},{\"tag\":\"mate\",\"ridge\":641,\"a\":15,\"owners\":[69,71,75,76]},{\"tag\":\"mate\",\"ridge\":641,\"a\":40,\"owners\":[75,76]},{\"tag\":\"mate\",\"ridge\":641,\"a\":54,\"owners\":[71,76]},{\"tag\":\"mate\",\"ridge\":641,\"a\":57,\"owners\":[69,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":59,\"owners\":[69,71,75,76]},{\"tag\":\"mate\",\"ridge\":641,\"a\":76,\"owners\":[15,40,54,59,69]},{\"tag\":\"mate\",\"ridge\":642,\"a\":15,\"owners\":[87,89,93,94]},{\"tag\":\"mate\",\"ridge\":642,\"a\":40,\"owners\":[93,94]},{\"tag\":\"mate\",\"ridge\":642,\"a\":49,\"owners\":[87,89]},{\"tag\":\"mate\",\"ridge\":642,\"a\":54,\"owners\":[89,94]},{\"tag\":\"mate\",\"ridge\":642,\"a\":57,\"owners\":[87,93]},{\"tag\":\"mate\",\"ridge\":642,\"a\":59,\"owners\":[87,89,93,94]},{\"tag\":\"mate\",\"ridge\":564,\"a\":67,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":564,\"a\":85,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":660,\"a\":69,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":676,\"a\":71,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":676,\"a\":89,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":568,\"a\":74,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":568,\"a\":92,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":664,\"a\":75,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":664,\"a\":93,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":680,\"a\":76,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":680,\"a\":94,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":624,\"a\":77,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":624,\"a\":95,\"owners\":[77]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[67,69,71],\"full_literals\":[-30,16,17,18]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":67,\"full_literals\":[-16,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":69,\"full_literals\":[-17,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":71,\"full_literals\":[-18,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":74,\"full_literals\":[-19,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-22,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-23,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-20,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":76,\"full_literals\":[-21,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":92,\"full_literals\":[-26,32]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[87,89],\"full_literals\":[-33,24,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":87,\"full_literals\":[-24,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-25,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":95,\"full_literals\":[-29,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":93,\"full_literals\":[-27,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":94,\"full_literals\":[-28,35]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-32,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,30,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-37,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-30,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-30,-36,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-33,-34,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-42,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-38,-44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[10,35,44,51,53,54,67,69,74,75,77,85,87,92,93,95]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[12,38,47,51,56,57,67,71,74,76,77,85,89,92,94,95]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[15,40,49,54,57,59,69,71,75,76,87,89,93,94]}]}"
  "p cnf 45 89\n-10 -3 0\n-10 -6 0\n-15 -10 0\n-21 -20 0\n-24 -16 0\n-24 -18 0\n-25 -16 0\n-25 -24 0\n-27 -21 0\n-1 16 17 19 20 22 0\n-4 19 20 22 0\n-7 16 17 22 0\n-10 17 20 0\n-11 16 17 19 20 0\n-12 16 19 22 0\n-1 23 24 26 27 29 0\n-4 26 27 29 0\n-7 23 24 29 0\n-10 24 27 0\n-11 23 24 26 27 0\n-2 16 18 19 21 22 0\n-5 19 21 22 0\n-8 16 18 22 0\n-10 18 21 0\n-13 16 18 19 21 0\n-14 16 19 22 0\n-5 26 28 29 0\n-3 17 18 20 21 0\n-6 20 21 0\n-12 18 21 0\n-14 17 20 0\n-15 17 18 20 21 0\n-21 3 6 12 15 17 0\n-3 24 25 27 28 0\n-6 27 28 0\n-9 24 25 0\n-12 25 28 0\n-14 24 27 0\n-15 24 25 27 28 0\n-16 23 0\n-23 16 0\n-17 24 0\n-18 25 0\n-25 18 0\n-19 26 0\n-26 19 0\n-20 27 0\n-27 20 0\n-21 28 0\n-28 21 0\n-22 29 0\n-29 22 0\n-30 16 17 18 0\n-16 30 0\n-17 30 0\n-18 30 0\n-19 31 0\n-22 31 0\n-23 31 0\n-20 32 0\n-21 32 0\n-26 32 0\n-33 24 25 0\n-24 33 0\n-25 33 0\n-29 34 0\n-27 35 0\n-28 35 0\n-32 36 0\n-31 36 0\n-31 -32 37 0\n-38 30 36 0\n-36 38 0\n-37 39 0\n-30 38 0\n-30 -36 39 0\n-33 40 0\n-33 -34 41 0\n-35 42 0\n-42 43 0\n-40 43 0\n-40 -42 44 0\n-41 44 0\n-38 -44 45 0\n-39 -43 45 0\n-45 0\n1 4 7 10 11 12 16 17 19 20 22 23 24 26 27 29 0\n2 5 8 10 13 14 16 18 19 21 22 23 25 26 28 29 0\n3 6 9 12 14 15 17 18 20 21 24 25 27 28 0\n"
  "90 38 0 73 75 69 70 54 55 56 60 61 62 57 58 59 21 23 25 13 44 31 50 22 52 88 0\n91 -44 0 90 86 84 0\n92 -41 0 91 83 0\n93 36 33 0 90 65 43 64 42 70 72 59 53 40 0\n94 -10 12 33 0 65 43 64 42 1 2 3 24 33 0\n95 -21 10 19 16 24 29 0 51 15 46 41 42 12 4 9 11 10 14 87 0\n96 19 16 29 33 0 41 51 65 43 23 64 46 26 15 94 95 50 22 21 25 88 0\n97 -19 37 0 45 57 62 71 0\n98 33 39 0 74 97 64 65 93 36 42 43 76 54 96 52 58 71 60 61 29 48 31 28 32 50 30 89 0\n99 24 16 39 0 91 92 98 78 66 51 74 97 15 41 46 77 82 79 67 17 47 42 19 16 20 18 87 0\n100 16 39 0 91 92 98 78 66 74 97 46 77 82 79 68 27 49 51 41 26 99 6 8 24 21 25 23 88 0\n101 39 0 98 100 5 7 63 0\n102 -43 0 101 86 85 0\n103 -42 0 102 80 0\n104 -40 0 102 81 0\n105 -35 0 103 79 0\n106 -33 0 104 77 0\n107 -27 0 105 67 0\n108 -28 0 105 68 0\n109 -24 0 106 64 0\n110 -25 0 106 65 0\n111 -6 0 107 108 35 0\n112 -20 0 107 47 0\n113 -21 0 108 49 0\n114 -17 0 109 42 0\n115 -14 0 109 107 38 0\n116 -3 0 109 110 107 108 34 0\n117 -15 0 109 110 107 108 39 0\n118 -18 0 110 43 0\n119 -12 0 110 108 37 0\n120 -9 0 110 109 36 0\n121 0 116 117 111 120 119 115 114 118 112 113 109 110 107 108 89 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00054.record051_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00054.record051
