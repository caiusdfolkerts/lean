module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00090Frames
public import GraphInputsRow24Part00090Leaves
public import GraphInputsRow24Part00090Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ae1745b29cac972aaa6aa6a3a2e966a59564d876a38ce1ba1e2783eac571aa569a66392e565655554d475534cd4b46d2743da8d63a4d538cd332cc73a2ccb8acab86c9b0ed4731d2719d1715c370bc1fa4a32a2a2a1a8962384e585311a545454952344d18c930cc8b12c2b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6d34926d36d24d369a6da49349a4da4d249249a493492489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 46), (facetIndex 56)]))
 (.leaf ([(facetIndex 37), (facetIndex 49), (facetIndex 61)])))
 (.branch 3
 (.leaf ([(facetIndex 62), (facetIndex 65), (facetIndex 79)]))
 (.branch 4
 (.leaf ([(facetIndex 63), (facetIndex 67), (facetIndex 89)]))
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 76)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 78), (facetIndex 84), (facetIndex 88)]))
 (.leaf ([(facetIndex 50), (facetIndex 53)])))
 (.branch 8
 (.leaf ([(facetIndex 68), (facetIndex 70)]))
 (.branch 9
 (.leaf ([(facetIndex 86)]))
 (.leaf ([(facetIndex 87)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "35980500002504440007073020321000000060061000000000001z25;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record002" 70

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record002" "{\"ridges\":[[14,324],[16,289],[17,352],[22,552],[24,560],[25,656],[34,324],[39,552],[44,304],[45,560],[46,338],[47,656],[48,352],[49,673],[50,60],[53,300],[55,324],[57,304],[58,324],[60,352],[64,352],[66,352],[68,60],[70,540],[77,656],[78,294],[80,552],[80,560],[81,656],[82,552],[83,552],[84,338],[85,560],[85,656],[86,540],[87,300],[88,116]],\"owners\":[[14,324,[76,78,87,88],[34,55,58,60]],[34,324,[87,88],[14,55,58,60,76,78]],[55,324,[76,78,88],[14,34,58,60,87]],[58,324,[78,87],[14,34,55,60,76,88]],[16,289,[17,32,48,53,60,64],[44,57]],[44,304,[88],[16,57,66,75,84]],[57,304,[84],[16,44,66,75,88]],[17,352,[78,84,87,88],[48,60,64,66]],[48,352,[87,88],[17,60,64,66,78,84]],[60,352,[84],[17,48,64,66,78,87,88]],[64,352,[78,84,88],[17,48,60,66,87]],[66,352,[78,87],[17,48,60,64,84,88]],[22,552,[62,65,89],[39,80,82,83]],[39,552,[89],[22,62,65,80,82,83]],[80,552,[65],[22,39,62,82,83,89]],[82,552,[62,65,89],[22,39,80,83]],[83,552,[62],[22,39,65,80,82,89]],[24,560,[62,67,89],[45,80,85]],[45,560,[89],[24,62,67,80,85]],[80,560,[67],[24,45,62,85,89]],[85,560,[62],[24,45,67,80,89]],[25,656,[63,67,86,89],[47,77,81,85]],[47,656,[86,89],[25,63,67,77,81,85]],[77,656,[63,67,89],[25,47,81,85,86]],[81,656,[67],[25,47,63,77,85,86,89]],[85,656,[63,86],[25,47,67,77,81,89]],[78,294,[32,75],[]],[46,338,[76,84],[]],[84,338,[46,76],[]],[49,673,[65,67],[]],[50,60,[68],[]],[68,60,[50],[]],[53,300,[87],[]],[87,300,[53],[]],[88,116,[56,74],[]],[70,540,[86],[]],[86,540,[70],[]]],\"edges\":[[34,[24,25,37,45,47,62,63,67,70,77,80,81,85,86,89]],[37,[16,17,32,44,48,53,57,60,64,66,75,78,84,87,88]],[38,[22,24,39,45,49,62,65,67,80,82,83,85,89]],[40,[14,17,34,46,48,55,58,60,64,66,76,78,84,87,88]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-34,-7],[-34,-33],[-1,34,36,44,45],[-8,44,45],[-19,34,36,45],[-22,36,44],[-2,3,7,15,18,23,26],[-11,45],[-21,41],[-3,36,41,44,45],[-15,44,45],[-23,41],[-26,36,41,45],[-28,36,44],[-4,24,27,46],[-10,46],[-37,27],[-39,24,27,46],[-40,24],[-5,24,29,46],[-12,46],[-37,29],[-42,24],[-6,25,29,43,46],[-14,43,46],[-35,25,29,46],[-38,29],[-42,25,43],[-36,7,33],[-13,34,41],[-41,13,34],[-16,27,29],[-17,30],[-30,17],[-18,44],[-44,18],[-45,20,32],[-31,43],[-43,31],[-7,47],[-13,47],[-20,47],[-9,48],[-16,48],[-24,49],[-27,49],[-25,50],[-29,50],[-46,50],[-32,51],[-33,51],[-34,51],[-52,36,41,45],[-36,52],[-41,52],[-45,52],[-53,17,18],[-17,53],[-18,53],[-54,30,31],[-30,54],[-31,54],[-55,43],[-43,55],[-56,44],[-44,56],[-48,57],[-47,57],[-51,58],[-50,58],[-50,-51,59],[-58,60],[-59,61],[-49,60],[-49,-58,61],[-60,62],[-61,63],[-57,62],[-57,-60,63],[-64,52,53],[-53,64],[-52,64],[-65,55,56],[-56,65],[-55,65],[-66,54,65],[-65,66],[-54,66],[-54,-65,67],[-68,64,66],[-67,69],[-64,68],[-64,-66,69],[-62,-69,70],[-63,-68,70],[-70],[5,6,9,12,14,24,25,29,31,35,37,38,42,43,46],[2,3,7,11,15,18,21,23,26,28,33,36,41,44,45],[4,5,10,12,16,24,27,29,37,39,40,42,46],[1,3,8,13,15,19,22,23,26,28,34,36,41,44,45]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":76,\"b\":32},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"mate\",\"ridge\":324,\"a\":14,\"owners\":[76,78,87,88]},{\"tag\":\"mate\",\"ridge\":324,\"a\":34,\"owners\":[87,88]},{\"tag\":\"mate\",\"ridge\":324,\"a\":55,\"owners\":[76,78,88]},{\"tag\":\"mate\",\"ridge\":324,\"a\":58,\"owners\":[78,87]},{\"tag\":\"mate\",\"ridge\":289,\"a\":16,\"owners\":[17,32,48,53,60,64]},{\"tag\":\"mate\",\"ridge\":304,\"a\":44,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":304,\"a\":57,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":352,\"a\":17,\"owners\":[78,84,87,88]},{\"tag\":\"mate\",\"ridge\":352,\"a\":48,\"owners\":[87,88]},{\"tag\":\"mate\",\"ridge\":352,\"a\":60,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":352,\"a\":64,\"owners\":[78,84,88]},{\"tag\":\"mate\",\"ridge\":352,\"a\":66,\"owners\":[78,87]},{\"tag\":\"mate\",\"ridge\":552,\"a\":22,\"owners\":[62,65,89]},{\"tag\":\"mate\",\"ridge\":552,\"a\":39,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":552,\"a\":80,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":552,\"a\":82,\"owners\":[62,65,89]},{\"tag\":\"mate\",\"ridge\":552,\"a\":83,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":560,\"a\":24,\"owners\":[62,67,89]},{\"tag\":\"mate\",\"ridge\":560,\"a\":45,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":560,\"a\":80,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":560,\"a\":85,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":656,\"a\":25,\"owners\":[63,67,86,89]},{\"tag\":\"mate\",\"ridge\":656,\"a\":47,\"owners\":[86,89]},{\"tag\":\"mate\",\"ridge\":656,\"a\":77,\"owners\":[63,67,89]},{\"tag\":\"mate\",\"ridge\":656,\"a\":81,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":656,\"a\":85,\"owners\":[63,86]},{\"tag\":\"mate\",\"ridge\":294,\"a\":78,\"owners\":[32,75]},{\"tag\":\"mate\",\"ridge\":338,\"a\":46,\"owners\":[76,84]},{\"tag\":\"mate\",\"ridge\":338,\"a\":84,\"owners\":[46,76]},{\"tag\":\"mate\",\"ridge\":673,\"a\":49,\"owners\":[65,67]},{\"tag\":\"mate\",\"ridge\":60,\"a\":50,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":60,\"a\":68,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":300,\"a\":53,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":300,\"a\":87,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":116,\"a\":88,\"owners\":[56,74]},{\"tag\":\"mate\",\"ridge\":540,\"a\":70,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":540,\"a\":86,\"owners\":[70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":32,\"full_literals\":[-7,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":46,\"full_literals\":[-13,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":56,\"full_literals\":[-20,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":37,\"full_literals\":[-9,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":49,\"full_literals\":[-16,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":62,\"full_literals\":[-24,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-27,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":63,\"full_literals\":[-25,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-29,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-46,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-32,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":75,\"full_literals\":[-33,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-34,51]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[78,84,88],\"full_literals\":[-52,36,41,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-36,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-41,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":88,\"full_literals\":[-45,52]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[50,53],\"full_literals\":[-53,17,18]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":50,\"full_literals\":[-17,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":53,\"full_literals\":[-18,53]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[68,70],\"full_literals\":[-54,30,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":68,\"full_literals\":[-30,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":70,\"full_literals\":[-31,54]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[86],\"full_literals\":[-55,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":86,\"full_literals\":[-43,55]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[87],\"full_literals\":[-56,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":87,\"full_literals\":[-44,56]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-51,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-58,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-60,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-66,54,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-66,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-62,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-68,70],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[24,25,37,45,47,62,63,67,70,77,80,81,85,86,89]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[16,17,32,44,48,53,57,60,64,66,75,78,84,87,88]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[22,24,39,45,49,62,65,67,80,82,83,85,89]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[14,17,34,46,48,55,58,60,64,66,76,78,84,87,88]}]}"
  "p cnf 70 100\n-34 -7 0\n-34 -33 0\n-1 34 36 44 45 0\n-8 44 45 0\n-19 34 36 45 0\n-22 36 44 0\n-2 3 7 15 18 23 26 0\n-11 45 0\n-21 41 0\n-3 36 41 44 45 0\n-15 44 45 0\n-23 41 0\n-26 36 41 45 0\n-28 36 44 0\n-4 24 27 46 0\n-10 46 0\n-37 27 0\n-39 24 27 46 0\n-40 24 0\n-5 24 29 46 0\n-12 46 0\n-37 29 0\n-42 24 0\n-6 25 29 43 46 0\n-14 43 46 0\n-35 25 29 46 0\n-38 29 0\n-42 25 43 0\n-36 7 33 0\n-13 34 41 0\n-41 13 34 0\n-16 27 29 0\n-17 30 0\n-30 17 0\n-18 44 0\n-44 18 0\n-45 20 32 0\n-31 43 0\n-43 31 0\n-7 47 0\n-13 47 0\n-20 47 0\n-9 48 0\n-16 48 0\n-24 49 0\n-27 49 0\n-25 50 0\n-29 50 0\n-46 50 0\n-32 51 0\n-33 51 0\n-34 51 0\n-52 36 41 45 0\n-36 52 0\n-41 52 0\n-45 52 0\n-53 17 18 0\n-17 53 0\n-18 53 0\n-54 30 31 0\n-30 54 0\n-31 54 0\n-55 43 0\n-43 55 0\n-56 44 0\n-44 56 0\n-48 57 0\n-47 57 0\n-51 58 0\n-50 58 0\n-50 -51 59 0\n-58 60 0\n-59 61 0\n-49 60 0\n-49 -58 61 0\n-60 62 0\n-61 63 0\n-57 62 0\n-57 -60 63 0\n-64 52 53 0\n-53 64 0\n-52 64 0\n-65 55 56 0\n-56 65 0\n-55 65 0\n-66 54 65 0\n-65 66 0\n-54 66 0\n-54 -65 67 0\n-68 64 66 0\n-67 69 0\n-64 68 0\n-64 -66 69 0\n-62 -69 70 0\n-63 -68 70 0\n-70 0\n5 6 9 12 14 24 25 29 31 35 37 38 42 43 46 0\n2 3 7 11 15 18 21 23 26 28 33 36 41 44 45 0\n4 5 10 12 16 24 27 29 37 39 40 42 46 0\n1 3 8 13 15 19 22 23 26 28 34 36 41 44 45 0\n"
  "101 62 0 76 78 72 74 67 70 45 46 44 48 49 18 19 23 17 15 20 16 21 99 0\n102 -69 0 101 96 94 0\n103 -67 0 102 91 0\n104 -65 56 0 103 83 89 63 62 39 0\n105 -66 0 102 93 81 58 59 34 36 65 104 85 86 64 60 38 0\n106 -65 0 105 87 0\n107 -54 0 105 88 0\n108 -56 0 106 84 0\n109 -55 0 106 85 0\n110 -30 0 107 61 0\n111 -31 0 107 62 0\n112 -44 0 108 66 0\n113 -43 0 109 64 0\n114 -17 0 110 33 0\n115 -18 0 112 35 0\n116 -53 0 114 115 57 0\n117 60 0 72 74 70 45 46 48 49 18 19 23 17 32 15 20 16 21 99 0\n118 51 -68 0 116 105 117 96 95 79 68 42 41 40 90 80 50 51 52 37 29 31 53 0\n119 -68 0 96 117 113 111 95 77 73 79 67 43 118 69 71 75 47 48 49 45 26 28 22 27 20 24 21 25 97 0\n120 -64 0 119 92 0\n121 -52 0 120 82 0\n122 -36 0 121 54 0\n123 -41 0 121 55 0\n124 -45 0 121 56 0\n125 -22 0 122 112 6 0\n126 -26 0 122 123 124 13 0\n127 -28 0 122 112 14 0\n128 -21 0 123 9 0\n129 -23 0 123 12 0\n130 -3 0 123 122 112 124 10 0\n131 -11 0 124 8 0\n132 -8 0 124 112 4 0\n133 -15 0 124 112 11 0\n134 34 0 124 112 123 122 129 127 126 125 130 133 132 5 30 3 100 0\n135 -7 0 134 1 0\n136 -33 0 134 2 0\n137 -2 0 135 130 133 115 129 126 7 0\n138 0 137 135 130 133 131 115 128 129 126 127 136 122 123 112 124 98 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5e1745b29c5713c1f1729aa9a1eaa659a96559361da8e1ba1e2785e0f9715a5594e479a9565655554d475a354d8b52d1b51d2745d0f6a358d5334d331ce8b8ac9b0ee8751e2749ca719d1715c3783c8f13e2c8a86a16a86898968382e079615446916525454950b41d18c9314c4b0ac1b21c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6d349a6da49249269a4936d24924d24d3492692492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 44), (facetIndex 50)]))
 (.leaf ([(facetIndex 59), (facetIndex 65)])))
 (.branch 3
 (.leaf ([(facetIndex 84)]))
 (.branch 4
 (.leaf ([(facetIndex 90)]))
 (.leaf ([(facetIndex 39), (facetIndex 46), (facetIndex 60)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 58), (facetIndex 67), (facetIndex 77)]))
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 87)])))
 (.branch 8
 (.leaf ([(facetIndex 81), (facetIndex 86), (facetIndex 92)]))
 (.branch 9
 (.leaf ([(facetIndex 88), (facetIndex 89)]))
 (.leaf ([(facetIndex 91), (facetIndex 93)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "9793886702007066500000000050100004150000000000040000004z27;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record003" 61

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record003" "{\"ridges\":[[17,336],[18,352],[24,642],[24,644],[39,326],[40,642],[40,644],[48,336],[49,352],[58,332],[62,336],[64,352],[68,336],[69,352],[70,352],[76,644],[79,326],[80,644],[81,326],[82,642],[82,644],[86,306],[88,312],[89,332],[91,332],[92,116],[93,312]],\"owners\":[[17,336,[79,86,89,92,93],[48,62,68,70]],[48,336,[89,92,93],[17,62,68,70,79,86]],[62,336,[86,93],[17,48,68,70,79,89,92]],[68,336,[79,86,92],[17,48,62,70,89,93]],[18,352,[81,86,91,92,93],[49,64,69,70]],[49,352,[91,92,93],[18,64,69,70,81,86]],[64,352,[86,93],[18,49,69,70,81,91,92]],[69,352,[81,86,92],[18,49,64,70,91,93]],[70,352,[81,91],[18,49,64,69,86,92,93]],[24,642,[44,50,84],[40,76,80,82]],[40,642,[84],[24,44,50,76,80,82]],[82,642,[44,84],[24,40,50,76,80]],[24,644,[59,65,90],[40,76,80,82]],[40,644,[90],[24,59,65,76,80,82]],[76,644,[65],[24,40,59,80,82,90]],[80,644,[59,65],[24,40,76,82,90]],[82,644,[59,90],[24,40,65,76,80]],[39,326,[79,81],[]],[79,326,[39,81],[]],[81,326,[39,79],[]],[86,306,[46,78],[]],[58,332,[89,91],[]],[89,332,[58,91],[]],[91,332,[58,89],[]],[92,116,[60,77,87],[]],[88,312,[67,93],[]],[93,312,[67,88],[]]],\"edges\":[[40,[17,18,39,48,49,58,62,64,68,69,70,79,81,86,89,91,92,93]],[43,[24,40,44,50,59,65,76,80,82,84,90]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,24,29,32,35,36],[-8,32,35,36],[-14,29,36],[-18,24,29,35],[-2,26,29,34,35,36],[-9,34,35,36],[-15,29,36],[-19,26,29,35],[-20,26,34],[-3,6,10,28],[-5,28],[-27,6,28],[-3,12,16,33],[-5,33],[-21,16],[-25,12,16],[-27,12,33],[-4,24,26],[-24,4,26],[-26,4,24],[-29,7,23],[-11,32,34],[-32,11,34],[-34,11,32],[-35,13,22,30],[-31,17,36],[-36,17,31],[-6,37],[-10,37],[-12,38],[-16,38],[-28,39],[-33,40],[-4,41],[-7,41],[-13,41],[-11,42],[-17,42],[-22,42],[-23,43],[-24,43],[-30,43],[-44,26,29,35],[-26,44],[-29,44],[-35,44],[-45,31,32],[-31,45],[-32,45],[-46,34,36],[-34,46],[-36,46],[-38,47],[-37,47],[-41,48],[-40,48],[-40,-41,49],[-48,50],[-49,51],[-39,50],[-39,-48,51],[-50,52],[-51,53],[-47,52],[-47,-50,53],[-43,54],[-42,54],[-55,45,46],[-46,55],[-45,55],[-45,-46,56],[-57,44,55],[-55,57],[-56,58],[-44,57],[-57,59],[-58,60],[-54,59],[-54,-57,60],[-52,-60,61],[-53,-59,61],[-61],[1,2,4,8,9,11,14,15,18,19,20,24,26,29,32,34,35,36],[3,5,6,10,12,16,21,25,27,28,33]],\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":336,\"a\":17,\"owners\":[79,86,89,92,93]},{\"tag\":\"mate\",\"ridge\":336,\"a\":48,\"owners\":[89,92,93]},{\"tag\":\"mate\",\"ridge\":336,\"a\":62,\"owners\":[86,93]},{\"tag\":\"mate\",\"ridge\":336,\"a\":68,\"owners\":[79,86,92]},{\"tag\":\"mate\",\"ridge\":352,\"a\":18,\"owners\":[81,86,91,92,93]},{\"tag\":\"mate\",\"ridge\":352,\"a\":49,\"owners\":[91,92,93]},{\"tag\":\"mate\",\"ridge\":352,\"a\":64,\"owners\":[86,93]},{\"tag\":\"mate\",\"ridge\":352,\"a\":69,\"owners\":[81,86,92]},{\"tag\":\"mate\",\"ridge\":352,\"a\":70,\"owners\":[81,91]},{\"tag\":\"mate\",\"ridge\":642,\"a\":24,\"owners\":[44,50,84]},{\"tag\":\"mate\",\"ridge\":642,\"a\":40,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":642,\"a\":82,\"owners\":[44,84]},{\"tag\":\"mate\",\"ridge\":644,\"a\":24,\"owners\":[59,65,90]},{\"tag\":\"mate\",\"ridge\":644,\"a\":40,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":644,\"a\":76,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":644,\"a\":80,\"owners\":[59,65]},{\"tag\":\"mate\",\"ridge\":644,\"a\":82,\"owners\":[59,90]},{\"tag\":\"mate\",\"ridge\":326,\"a\":39,\"owners\":[79,81]},{\"tag\":\"mate\",\"ridge\":326,\"a\":79,\"owners\":[39,81]},{\"tag\":\"mate\",\"ridge\":326,\"a\":81,\"owners\":[39,79]},{\"tag\":\"mate\",\"ridge\":306,\"a\":86,\"owners\":[46,78]},{\"tag\":\"mate\",\"ridge\":332,\"a\":58,\"owners\":[89,91]},{\"tag\":\"mate\",\"ridge\":332,\"a\":89,\"owners\":[58,91]},{\"tag\":\"mate\",\"ridge\":332,\"a\":91,\"owners\":[58,89]},{\"tag\":\"mate\",\"ridge\":116,\"a\":92,\"owners\":[60,77,87]},{\"tag\":\"mate\",\"ridge\":312,\"a\":88,\"owners\":[67,93]},{\"tag\":\"mate\",\"ridge\":312,\"a\":93,\"owners\":[67,88]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":44,\"full_literals\":[-6,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":50,\"full_literals\":[-10,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":59,\"full_literals\":[-12,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":65,\"full_literals\":[-16,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":84,\"full_literals\":[-28,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":90,\"full_literals\":[-33,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":39,\"full_literals\":[-4,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":46,\"full_literals\":[-7,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":60,\"full_literals\":[-13,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":58,\"full_literals\":[-11,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":67,\"full_literals\":[-17,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":77,\"full_literals\":[-22,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":78,\"full_literals\":[-23,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":79,\"full_literals\":[-24,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-30,43]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[81,86,92],\"full_literals\":[-44,26,29,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":81,\"full_literals\":[-26,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-29,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":92,\"full_literals\":[-35,44]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[88,89],\"full_literals\":[-45,31,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":88,\"full_literals\":[-31,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":89,\"full_literals\":[-32,45]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[91,93],\"full_literals\":[-46,34,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":91,\"full_literals\":[-34,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":93,\"full_literals\":[-36,46]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-41,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-48,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-51,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-50,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-46,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,44,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-56,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-57,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-52,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[17,18,39,48,49,58,62,64,68,69,70,79,81,86,89,91,92,93]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[24,40,44,50,59,65,76,80,82,84,90]}]}"
  "p cnf 61 84\n-1 24 29 32 35 36 0\n-8 32 35 36 0\n-14 29 36 0\n-18 24 29 35 0\n-2 26 29 34 35 36 0\n-9 34 35 36 0\n-15 29 36 0\n-19 26 29 35 0\n-20 26 34 0\n-3 6 10 28 0\n-5 28 0\n-27 6 28 0\n-3 12 16 33 0\n-5 33 0\n-21 16 0\n-25 12 16 0\n-27 12 33 0\n-4 24 26 0\n-24 4 26 0\n-26 4 24 0\n-29 7 23 0\n-11 32 34 0\n-32 11 34 0\n-34 11 32 0\n-35 13 22 30 0\n-31 17 36 0\n-36 17 31 0\n-6 37 0\n-10 37 0\n-12 38 0\n-16 38 0\n-28 39 0\n-33 40 0\n-4 41 0\n-7 41 0\n-13 41 0\n-11 42 0\n-17 42 0\n-22 42 0\n-23 43 0\n-24 43 0\n-30 43 0\n-44 26 29 35 0\n-26 44 0\n-29 44 0\n-35 44 0\n-45 31 32 0\n-31 45 0\n-32 45 0\n-46 34 36 0\n-34 46 0\n-36 46 0\n-38 47 0\n-37 47 0\n-41 48 0\n-40 48 0\n-40 -41 49 0\n-48 50 0\n-49 51 0\n-39 50 0\n-39 -48 51 0\n-50 52 0\n-51 53 0\n-47 52 0\n-47 -50 53 0\n-43 54 0\n-42 54 0\n-55 45 46 0\n-46 55 0\n-45 55 0\n-45 -46 56 0\n-57 44 55 0\n-55 57 0\n-56 58 0\n-44 57 0\n-57 59 0\n-58 60 0\n-54 59 0\n-54 -57 60 0\n-52 -60 61 0\n-53 -59 61 0\n-61 0\n1 2 4 8 9 11 14 15 18 19 20 24 26 29 32 34 35 36 0\n3 5 6 10 12 16 21 25 27 28 33 0\n"
  "85 52 0 62 64 58 60 53 54 56 32 30 31 28 29 33 11 12 10 15 16 84 0\n86 -60 0 85 82 80 0\n87 -58 0 86 77 0\n88 -56 0 87 74 0\n89 -46 42 0 88 38 37 71 48 49 27 24 50 0\n90 41 -57 0 86 79 67 89 37 51 23 38 52 26 47 68 72 39 66 42 41 40 34 35 36 20 21 25 43 0\n91 -41 53 0 63 59 55 57 58 61 33 65 32 14 53 54 30 31 28 29 17 15 16 13 84 0\n92 41 0 34 90 73 75 69 70 44 45 46 51 52 49 8 19 5 9 4 3 7 1 6 2 22 83 0\n93 53 0 92 91 0\n94 -59 0 93 82 81 0\n95 -57 0 94 76 0\n96 -54 0 94 78 0\n97 -55 0 95 73 0\n98 -44 0 95 75 0\n99 -43 0 96 66 0\n100 -42 0 96 67 0\n101 -46 0 97 69 0\n102 -45 0 97 70 0\n103 -26 0 98 44 0\n104 -29 0 98 45 0\n105 -35 0 98 46 0\n106 -24 0 99 41 0\n107 -11 0 100 37 0\n108 -34 0 101 51 0\n109 -36 0 101 52 0\n110 -32 0 102 49 0\n111 -19 0 103 104 105 8 0\n112 -4 0 103 106 18 0\n113 -2 0 103 104 108 105 109 5 0\n114 -20 0 103 108 9 0\n115 -18 0 104 106 105 4 0\n116 -14 0 104 109 3 0\n117 -15 0 104 109 7 0\n118 -1 0 104 106 110 105 109 1 0\n119 -9 0 105 108 109 6 0\n120 -8 0 105 110 109 2 0\n121 0 115 111 118 113 119 107 112 120 116 117 114 106 103 104 110 108 105 109 83 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ab29c8f16a5693aa9966a59568d936338ae1b89e17b31aa569a65598e539a9565a55554d68d3362d2b46d8749d176a358e9354e3352ccb4acab1ad1b26c5ba1d4731e2749ca719e1745c9715e340f1320e8362384e0b81e8c5310e685896150d48d1342d0754348d130cc8b12c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b4da6db4924926db4934d24924934d2492492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 56)]))
 (.leaf ([(facetIndex 66), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 72), (facetIndex 74)]))
 (.leaf ([(facetIndex 73), (facetIndex 75)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 84), (facetIndex 86)]))
 (.leaf ([(facetIndex 85), (facetIndex 87)])))
 (.branch 7
 (.leaf ([(facetIndex 89), (facetIndex 90)]))
 (.leaf ([(facetIndex 92), (facetIndex 93)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "3f1b0b2c00000069a00104z31;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record005" 41

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record005" "{\"ridges\":[[12,322],[20,641],[20,644],[42,322],[43,641],[43,644],[51,322],[53,322],[54,658],[55,322],[56,674],[64,641],[64,644],[66,340],[67,641],[67,644],[68,356],[69,641],[69,644],[72,344],[73,664],[74,360],[75,680],[85,658],[87,674],[92,664],[93,680]],\"owners\":[[12,322,[84,86,89,90],[42,51,53,55]],[42,322,[89,90],[12,51,53,55,84,86]],[51,322,[84,86],[12,42,53,55,89,90]],[53,322,[86,90],[12,42,51,55,84,89]],[55,322,[84,89],[12,42,51,53,86,90]],[20,641,[54,56,73,75],[43,64,67,69]],[43,641,[73,75],[20,54,56,64,67,69]],[64,641,[54,56],[20,43,67,69,73,75]],[67,641,[56,75],[20,43,54,64,69,73]],[69,641,[54,73],[20,43,56,64,67,75]],[20,644,[85,87,92,93],[43,64,67,69]],[43,644,[92,93],[20,64,67,69,85,87]],[64,644,[85,87],[20,43,67,69,92,93]],[67,644,[87,93],[20,43,64,69,85,92]],[69,644,[85,92],[20,43,64,67,87,93]],[54,658,[85],[]],[85,658,[54],[]],[56,674,[87],[]],[87,674,[56],[]],[66,340,[84],[]],[68,356,[86],[]],[72,344,[89],[]],[73,664,[92],[]],[92,664,[73],[]],[74,360,[90],[]],[75,680,[93],[]],[93,680,[75],[]]],\"edges\":[[40,[12,42,51,53,55,66,68,72,74,84,86,89,90]],[43,[20,43,54,56,64,67,69,73,75,85,87,92,93]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,19,21,23,24],[-3,23,24],[-5,19,21],[-6,21,24],[-8,19,23],[-2,7,9,16,18],[-4,16,18],[-10,7,9],[-12,9,18],[-14,7,16],[-2,20,22,25,26],[-4,25,26],[-10,20,22],[-12,22,26],[-14,20,25],[-7,20],[-20,7],[-9,22],[-22,9],[-11,19],[-13,21],[-15,23],[-16,25],[-25,16],[-17,24],[-18,26],[-26,18],[-7,27],[-9,27],[-16,28],[-18,28],[-19,29],[-21,29],[-20,30],[-22,30],[-23,31],[-24,31],[-25,32],[-26,32],[-27,33],[-28,34],[-34,35],[-33,35],[-30,36],[-29,36],[-29,-30,37],[-32,38],[-31,38],[-31,-32,39],[-39,40],[-36,-38,40],[-37,40],[-35,-40,41],[-41],[1,3,5,6,8,11,13,15,17,19,21,23,24],[2,4,7,9,10,12,14,16,18,20,22,25,26]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":322,\"a\":12,\"owners\":[84,86,89,90]},{\"tag\":\"mate\",\"ridge\":322,\"a\":42,\"owners\":[89,90]},{\"tag\":\"mate\",\"ridge\":322,\"a\":51,\"owners\":[84,86]},{\"tag\":\"mate\",\"ridge\":322,\"a\":53,\"owners\":[86,90]},{\"tag\":\"mate\",\"ridge\":322,\"a\":55,\"owners\":[84,89]},{\"tag\":\"mate\",\"ridge\":641,\"a\":20,\"owners\":[54,56,73,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":43,\"owners\":[73,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":64,\"owners\":[54,56]},{\"tag\":\"mate\",\"ridge\":641,\"a\":67,\"owners\":[56,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":69,\"owners\":[54,73]},{\"tag\":\"mate\",\"ridge\":644,\"a\":20,\"owners\":[85,87,92,93]},{\"tag\":\"mate\",\"ridge\":644,\"a\":43,\"owners\":[92,93]},{\"tag\":\"mate\",\"ridge\":644,\"a\":64,\"owners\":[85,87]},{\"tag\":\"mate\",\"ridge\":644,\"a\":67,\"owners\":[87,93]},{\"tag\":\"mate\",\"ridge\":644,\"a\":69,\"owners\":[85,92]},{\"tag\":\"mate\",\"ridge\":658,\"a\":54,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":658,\"a\":85,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":674,\"a\":56,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":674,\"a\":87,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":340,\"a\":66,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":356,\"a\":68,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":344,\"a\":72,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":664,\"a\":73,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":664,\"a\":92,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":360,\"a\":74,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":680,\"a\":75,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":680,\"a\":93,\"owners\":[75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":54,\"full_literals\":[-7,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":56,\"full_literals\":[-9,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-16,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":75,\"full_literals\":[-18,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":84,\"full_literals\":[-19,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":86,\"full_literals\":[-21,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-20,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-22,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":89,\"full_literals\":[-23,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":90,\"full_literals\":[-24,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":92,\"full_literals\":[-25,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":93,\"full_literals\":[-26,32]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-29,-30,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-32,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-38,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-35,-40,41],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[12,42,51,53,55,66,68,72,74,84,86,89,90]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[20,43,54,56,64,67,69,73,75,85,87,92,93]}]}"
  "p cnf 41 56\n-1 19 21 23 24 0\n-3 23 24 0\n-5 19 21 0\n-6 21 24 0\n-8 19 23 0\n-2 7 9 16 18 0\n-4 16 18 0\n-10 7 9 0\n-12 9 18 0\n-14 7 16 0\n-2 20 22 25 26 0\n-4 25 26 0\n-10 20 22 0\n-12 22 26 0\n-14 20 25 0\n-7 20 0\n-20 7 0\n-9 22 0\n-22 9 0\n-11 19 0\n-13 21 0\n-15 23 0\n-16 25 0\n-25 16 0\n-17 24 0\n-18 26 0\n-26 18 0\n-7 27 0\n-9 27 0\n-16 28 0\n-18 28 0\n-19 29 0\n-21 29 0\n-20 30 0\n-22 30 0\n-23 31 0\n-24 31 0\n-25 32 0\n-26 32 0\n-27 33 0\n-28 34 0\n-34 35 0\n-33 35 0\n-30 36 0\n-29 36 0\n-29 -30 37 0\n-32 38 0\n-31 38 0\n-31 -32 39 0\n-39 40 0\n-36 -38 40 0\n-37 40 0\n-35 -40 41 0\n-41 0\n1 3 5 6 8 11 13 15 17 19 21 23 24 0\n2 4 7 9 10 12 14 16 18 20 22 25 26 0\n"
  "57 35 0 42 43 41 40 30 31 28 29 7 24 10 27 9 6 17 19 8 56 0\n58 -40 0 57 54 53 0\n59 -39 0 58 50 0\n60 -37 0 58 52 0\n61 32 30 0 34 35 13 18 16 38 39 12 23 15 26 14 11 56 0\n62 36 0 59 44 45 32 33 3 20 21 61 49 36 37 2 22 5 25 1 4 55 0\n63 -38 0 62 58 51 0\n64 -32 0 63 47 0\n65 -31 0 63 48 0\n66 30 0 64 61 0\n67 -23 0 65 36 0\n68 -24 0 65 37 0\n69 -29 0 66 60 46 0\n70 -3 0 67 68 2 0\n71 -15 0 67 22 0\n72 -17 0 68 25 0\n73 -19 0 69 32 0\n74 -21 0 69 33 0\n75 -5 0 73 74 3 0\n76 -11 0 73 20 0\n77 -8 0 73 67 5 0\n78 -1 0 73 68 74 67 1 0\n79 -13 0 74 21 0\n80 -6 0 74 68 4 0\n81 0 78 80 70 68 77 75 67 71 72 73 76 79 74 55 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ab29c8f1725693aa9966a5a361d94e4b8ae2785e5c6a9a65598e539a9565a56551d68d5362d4b4ad8749d176a358e9354e334cc7362d4b2ad1b26c5ba1d4731e2749ca719e1725d0f13e340f12a0e8560d88e0b81e8c5290e68589615154352342d0754348c530cd0b22c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6d369b6934926db4934926924934d2492492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 56)]))
 (.leaf ([(facetIndex 63), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 73), (facetIndex 74)]))
 (.leaf ([(facetIndex 72), (facetIndex 75)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 80), (facetIndex 84)]))
 (.leaf ([(facetIndex 83), (facetIndex 85)])))
 (.branch 7
 (.leaf ([(facetIndex 87), (facetIndex 88)]))
 (.leaf ([(facetIndex 90), (facetIndex 91)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "fc6c2ca040006930010002z2f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record007" 41

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record007" "{\"ridges\":[[12,321],[12,322],[20,644],[42,321],[42,322],[43,644],[48,321],[48,322],[53,321],[53,322],[54,658],[55,321],[55,322],[56,674],[63,332],[64,644],[67,644],[68,356],[69,644],[72,344],[73,664],[74,680],[75,368],[80,332],[84,356],[87,344],[88,368]],\"owners\":[[12,321,[63,68,72,75],[42,48,53,55]],[42,321,[72,75],[12,48,53,55,63,68]],[48,321,[68,75],[12,42,53,55,63,72]],[53,321,[63,68],[12,42,48,55,72,75]],[55,321,[63,72],[12,42,48,53,68,75]],[12,322,[80,84,87,88],[42,48,53,55]],[42,322,[87,88],[12,48,53,55,80,84]],[48,322,[84,88],[12,42,53,55,80,87]],[53,322,[80,84],[12,42,48,55,87,88]],[55,322,[80,87],[12,42,48,53,84,88]],[20,644,[83,85,90,91],[43,64,67,69]],[43,644,[90,91],[20,64,67,69,83,85]],[64,644,[83,85],[20,43,67,69,90,91]],[67,644,[85,91],[20,43,64,69,83,90]],[69,644,[83,90],[20,43,64,67,85,91]],[54,658,[83],[]],[56,674,[85],[]],[63,332,[80],[]],[80,332,[63],[]],[68,356,[84],[]],[84,356,[68],[]],[72,344,[87],[]],[87,344,[72],[]],[73,664,[90],[]],[74,680,[91],[]],[75,368,[88],[]],[88,368,[75],[]]],\"edges\":[[40,[12,42,48,53,55,63,68,72,75,80,84,87,88]],[43,[20,43,54,56,64,67,69,73,74,83,85,90,91]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,10,13,15,18],[-3,15,18],[-5,13,18],[-6,10,13],[-8,10,15],[-1,19,21,23,24],[-3,23,24],[-5,21,24],[-6,19,21],[-8,19,23],[-2,20,22,25,26],[-4,25,26],[-11,20,22],[-12,22,26],[-14,20,25],[-7,20],[-9,22],[-10,19],[-19,10],[-13,21],[-21,13],[-15,23],[-23,15],[-16,25],[-17,26],[-18,24],[-24,18],[-10,27],[-13,27],[-15,28],[-18,28],[-19,29],[-21,29],[-20,30],[-22,30],[-23,31],[-24,31],[-25,32],[-26,32],[-27,33],[-28,34],[-34,35],[-33,35],[-30,36],[-29,36],[-29,-30,37],[-32,38],[-31,38],[-31,-32,39],[-39,40],[-36,-38,40],[-37,40],[-35,-40,41],[-41],[1,3,5,6,8,10,13,15,18,19,21,23,24],[2,4,7,9,11,12,14,16,17,20,22,25,26]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":321,\"a\":12,\"owners\":[63,68,72,75]},{\"tag\":\"mate\",\"ridge\":321,\"a\":42,\"owners\":[72,75]},{\"tag\":\"mate\",\"ridge\":321,\"a\":48,\"owners\":[68,75]},{\"tag\":\"mate\",\"ridge\":321,\"a\":53,\"owners\":[63,68]},{\"tag\":\"mate\",\"ridge\":321,\"a\":55,\"owners\":[63,72]},{\"tag\":\"mate\",\"ridge\":322,\"a\":12,\"owners\":[80,84,87,88]},{\"tag\":\"mate\",\"ridge\":322,\"a\":42,\"owners\":[87,88]},{\"tag\":\"mate\",\"ridge\":322,\"a\":48,\"owners\":[84,88]},{\"tag\":\"mate\",\"ridge\":322,\"a\":53,\"owners\":[80,84]},{\"tag\":\"mate\",\"ridge\":322,\"a\":55,\"owners\":[80,87]},{\"tag\":\"mate\",\"ridge\":644,\"a\":20,\"owners\":[83,85,90,91]},{\"tag\":\"mate\",\"ridge\":644,\"a\":43,\"owners\":[90,91]},{\"tag\":\"mate\",\"ridge\":644,\"a\":64,\"owners\":[83,85]},{\"tag\":\"mate\",\"ridge\":644,\"a\":67,\"owners\":[85,91]},{\"tag\":\"mate\",\"ridge\":644,\"a\":69,\"owners\":[83,90]},{\"tag\":\"mate\",\"ridge\":658,\"a\":54,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":674,\"a\":56,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":332,\"a\":63,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":332,\"a\":80,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":356,\"a\":68,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":356,\"a\":84,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":344,\"a\":72,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":344,\"a\":87,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":664,\"a\":73,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":680,\"a\":74,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":368,\"a\":75,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":368,\"a\":88,\"owners\":[75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":63,\"full_literals\":[-10,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":68,\"full_literals\":[-13,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-15,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":75,\"full_literals\":[-18,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-19,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":84,\"full_literals\":[-21,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-20,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-22,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-23,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-24,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":90,\"full_literals\":[-25,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":91,\"full_literals\":[-26,32]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-29,-30,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-32,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-38,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-35,-40,41],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[12,42,48,53,55,63,68,72,75,80,84,87,88]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[20,43,54,56,64,67,69,73,74,83,85,90,91]}]}"
  "p cnf 41 56\n-1 10 13 15 18 0\n-3 15 18 0\n-5 13 18 0\n-6 10 13 0\n-8 10 15 0\n-1 19 21 23 24 0\n-3 23 24 0\n-5 21 24 0\n-6 19 21 0\n-8 19 23 0\n-2 20 22 25 26 0\n-4 25 26 0\n-11 20 22 0\n-12 22 26 0\n-14 20 25 0\n-7 20 0\n-9 22 0\n-10 19 0\n-19 10 0\n-13 21 0\n-21 13 0\n-15 23 0\n-23 15 0\n-16 25 0\n-17 26 0\n-18 24 0\n-24 18 0\n-10 27 0\n-13 27 0\n-15 28 0\n-18 28 0\n-19 29 0\n-21 29 0\n-20 30 0\n-22 30 0\n-23 31 0\n-24 31 0\n-25 32 0\n-26 32 0\n-27 33 0\n-28 34 0\n-34 35 0\n-33 35 0\n-30 36 0\n-29 36 0\n-29 -30 37 0\n-32 38 0\n-31 38 0\n-31 -32 39 0\n-39 40 0\n-36 -38 40 0\n-37 40 0\n-35 -40 41 0\n-41 0\n1 3 5 6 8 10 13 15 18 19 21 23 24 0\n2 4 7 9 11 12 14 16 17 20 22 25 26 0\n"
  "57 35 0 42 43 41 40 30 31 28 29 2 23 27 1 19 5 3 21 4 55 0\n58 -40 0 57 54 53 0\n59 -39 0 58 50 0\n60 -37 0 58 52 0\n61 31 29 0 32 33 9 20 18 36 37 7 22 10 6 26 8 55 0\n62 36 0 59 44 45 34 35 16 17 13 61 49 38 39 12 24 15 11 25 14 56 0\n63 -38 0 62 58 51 0\n64 -32 0 63 47 0\n65 -31 0 63 48 0\n66 -25 0 64 38 0\n67 -26 0 64 39 0\n68 29 0 65 61 0\n69 -4 0 66 67 12 0\n70 -16 0 66 24 0\n71 -17 0 67 25 0\n72 -30 0 68 60 46 0\n73 -20 0 72 34 0\n74 -22 0 72 35 0\n75 -7 0 73 16 0\n76 -14 0 73 66 15 0\n77 -9 0 74 17 0\n78 -11 0 74 73 13 0\n79 -2 0 74 73 66 67 11 0\n80 -12 0 74 67 14 0\n81 0 76 77 69 73 78 80 79 75 71 70 74 66 67 56 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2b85d32ca715c8f13cacaaaa6a3a2e966a5a361da8e5392e8789e17971aa5594e4b9595554d475a354d8b51d2745da8d6334cb31ce8b52e2b4acab16e8751e2749c6725e0f43c8f13e2c4b03ca2a2a2683a898560da0e0b81e4a4990e545494550d50d0b41d24c530cc8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da6d26924da49a4936d249269249b4926924d2492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 42), (facetIndex 53)]))
 (.leaf ([(facetIndex 47), (facetIndex 52)])))
 (.branch 3
 (.leaf ([(facetIndex 59), (facetIndex 67)]))
 (.leaf ([(facetIndex 66), (facetIndex 68)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 73), (facetIndex 78)]))
 (.leaf ([(facetIndex 77), (facetIndex 83)])))
 (.branch 7
 (.leaf ([(facetIndex 86), (facetIndex 89)]))
 (.leaf ([(facetIndex 87), (facetIndex 90)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1f0f80a001280200034c00004000010002z23;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record008" 43

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record008" "{\"ridges\":[[16,321],[16,324],[29,648],[41,321],[41,324],[42,645],[47,330],[48,642],[52,354],[53,673],[58,321],[58,324],[62,321],[62,324],[63,321],[63,324],[66,344],[68,368],[73,330],[74,648],[77,660],[78,354],[81,648],[82,648],[83,688],[86,344],[87,660],[89,368],[90,688]],\"owners\":[[16,321,[47,52,66,68],[41,58,62,63]],[41,321,[66,68],[16,47,52,58,62,63]],[58,321,[52,68],[16,41,47,62,63,66]],[62,321,[47,52],[16,41,58,63,66,68]],[63,321,[47,66],[16,41,52,58,62,68]],[16,324,[73,78,86,89],[41,58,62,63]],[41,324,[86,89],[16,58,62,63,73,78]],[58,324,[78,89],[16,41,62,63,73,86]],[62,324,[73,78],[16,41,58,63,86,89]],[63,324,[73,86],[16,41,58,62,78,89]],[48,642,[77,83],[29,42,53,74,81,82]],[29,648,[59,67,87,90],[48,74,81,82]],[74,648,[67,90],[29,48,59,81,82,87]],[81,648,[59,67],[29,48,74,82,87,90]],[82,648,[59,87],[29,48,67,74,81,90]],[42,645,[59],[]],[47,330,[73],[]],[73,330,[47],[]],[52,354,[78],[]],[78,354,[52],[]],[53,673,[67],[]],[66,344,[86],[]],[86,344,[66],[]],[68,368,[89],[]],[89,368,[68],[]],[77,660,[87],[]],[87,660,[77],[]],[83,688,[90],[]],[90,688,[83],[]]],\"edges\":[[40,[16,41,47,52,58,62,63,66,68,73,78,86,89]],[43,[29,42,48,53,59,67,74,77,81,82,83,87,90]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,5,7,13,15],[-3,13,15],[-9,7,15],[-11,5,7],[-12,5,13],[-1,16,19,23,25],[-3,23,25],[-9,19,25],[-11,16,19],[-12,16,23],[-6,18,22],[-2,10,14,24,26],[-17,14,26],[-20,10,14],[-21,10,24],[-4,10],[-5,16],[-16,5],[-7,19],[-19,7],[-8,14],[-13,23],[-23,13],[-15,25],[-25,15],[-18,24],[-24,18],[-22,26],[-26,22],[-5,27],[-7,27],[-10,28],[-14,28],[-13,29],[-15,29],[-30,16,19],[-16,30],[-19,30],[-31,18,22],[-18,31],[-22,31],[-32,23,25],[-23,32],[-25,32],[-33,24,26],[-24,33],[-26,33],[-27,34],[-29,35],[-28,35],[-28,-29,36],[-35,37],[-36,38],[-34,37],[-34,-35,38],[-39,30,31],[-31,39],[-30,39],[-40,32,33],[-33,40],[-32,40],[-41,39,40],[-40,41],[-39,41],[-39,-40,42],[-37,-42,43],[-38,-41,43],[-43],[1,3,5,7,9,11,12,13,15,16,19,23,25],[2,4,6,8,10,14,17,18,20,21,22,24,26]],\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":321,\"a\":16,\"owners\":[47,52,66,68]},{\"tag\":\"mate\",\"ridge\":321,\"a\":41,\"owners\":[66,68]},{\"tag\":\"mate\",\"ridge\":321,\"a\":58,\"owners\":[52,68]},{\"tag\":\"mate\",\"ridge\":321,\"a\":62,\"owners\":[47,52]},{\"tag\":\"mate\",\"ridge\":321,\"a\":63,\"owners\":[47,66]},{\"tag\":\"mate\",\"ridge\":324,\"a\":16,\"owners\":[73,78,86,89]},{\"tag\":\"mate\",\"ridge\":324,\"a\":41,\"owners\":[86,89]},{\"tag\":\"mate\",\"ridge\":324,\"a\":58,\"owners\":[78,89]},{\"tag\":\"mate\",\"ridge\":324,\"a\":62,\"owners\":[73,78]},{\"tag\":\"mate\",\"ridge\":324,\"a\":63,\"owners\":[73,86]},{\"tag\":\"mate\",\"ridge\":642,\"a\":48,\"owners\":[77,83]},{\"tag\":\"mate\",\"ridge\":648,\"a\":29,\"owners\":[59,67,87,90]},{\"tag\":\"mate\",\"ridge\":648,\"a\":74,\"owners\":[67,90]},{\"tag\":\"mate\",\"ridge\":648,\"a\":81,\"owners\":[59,67]},{\"tag\":\"mate\",\"ridge\":648,\"a\":82,\"owners\":[59,87]},{\"tag\":\"mate\",\"ridge\":645,\"a\":42,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":330,\"a\":47,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":330,\"a\":73,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":354,\"a\":52,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":354,\"a\":78,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":673,\"a\":53,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":344,\"a\":66,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":344,\"a\":86,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":368,\"a\":68,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":368,\"a\":89,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":660,\"a\":77,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":660,\"a\":87,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":688,\"a\":83,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":688,\"a\":90,\"owners\":[83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":47,\"full_literals\":[-5,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":52,\"full_literals\":[-7,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":59,\"full_literals\":[-10,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-14,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":66,\"full_literals\":[-13,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":68,\"full_literals\":[-15,29]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[73,78],\"full_literals\":[-30,16,19]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":73,\"full_literals\":[-16,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":78,\"full_literals\":[-19,30]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[77,83],\"full_literals\":[-31,18,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":77,\"full_literals\":[-18,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-22,31]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[86,89],\"full_literals\":[-32,23,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-23,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":89,\"full_literals\":[-25,32]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[87,90],\"full_literals\":[-33,24,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":87,\"full_literals\":[-24,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":90,\"full_literals\":[-26,33]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-28,-29,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-36,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-34,-35,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-39,30,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-30,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-40,32,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-41,39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-40,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-37,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-38,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[16,41,47,52,58,62,63,66,68,73,78,86,89]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[29,42,48,53,59,67,74,77,81,82,83,87,90]}]}"
  "p cnf 43 70\n-1 5 7 13 15 0\n-3 13 15 0\n-9 7 15 0\n-11 5 7 0\n-12 5 13 0\n-1 16 19 23 25 0\n-3 23 25 0\n-9 19 25 0\n-11 16 19 0\n-12 16 23 0\n-6 18 22 0\n-2 10 14 24 26 0\n-17 14 26 0\n-20 10 14 0\n-21 10 24 0\n-4 10 0\n-5 16 0\n-16 5 0\n-7 19 0\n-19 7 0\n-8 14 0\n-13 23 0\n-23 13 0\n-15 25 0\n-25 15 0\n-18 24 0\n-24 18 0\n-22 26 0\n-26 22 0\n-5 27 0\n-7 27 0\n-10 28 0\n-14 28 0\n-13 29 0\n-15 29 0\n-30 16 19 0\n-16 30 0\n-19 30 0\n-31 18 22 0\n-18 31 0\n-22 31 0\n-32 23 25 0\n-23 32 0\n-25 32 0\n-33 24 26 0\n-24 33 0\n-26 33 0\n-27 34 0\n-29 35 0\n-28 35 0\n-28 -29 36 0\n-35 37 0\n-36 38 0\n-34 37 0\n-34 -35 38 0\n-39 30 31 0\n-31 39 0\n-30 39 0\n-40 32 33 0\n-33 40 0\n-32 40 0\n-41 39 40 0\n-40 41 0\n-39 41 0\n-39 -40 42 0\n-37 -42 43 0\n-38 -41 43 0\n-43 0\n1 3 5 7 9 11 12 13 15 16 19 23 25 0\n2 4 6 8 10 14 17 18 20 21 22 24 26 0\n"
  "71 37 0 52 54 49 48 34 35 30 31 23 5 25 2 3 18 20 1 4 69 0\n72 -42 0 71 68 66 0\n73 28 31 0 40 41 11 29 27 32 33 16 15 12 21 14 13 70 0\n74 -40 36 0 72 65 57 40 41 27 29 45 59 73 51 34 35 23 25 42 0\n75 -41 0 68 67 53 74 60 62 46 47 26 28 39 73 56 50 55 48 30 31 18 20 36 0\n76 -40 0 75 63 0\n77 -39 0 75 64 0\n78 -32 0 76 61 0\n79 -30 0 77 58 0\n80 -23 0 78 43 0\n81 -25 0 78 44 0\n82 -16 0 79 37 0\n83 -19 0 79 38 0\n84 -13 0 80 22 0\n85 -15 0 81 24 0\n86 -3 0 81 80 7 0\n87 -5 0 82 17 0\n88 -12 0 82 80 10 0\n89 -7 0 83 19 0\n90 -11 0 83 82 9 0\n91 -1 0 83 82 80 81 6 0\n92 -9 0 83 81 8 0\n93 0 92 88 86 91 89 87 90 84 85 82 83 80 81 69 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record014
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3e0f43b0dc2f07caa96a2e87aa59562d8766394e2b86e2785e0fab19c6a95a4b91e695554b51d4ad1b49d1743da8d63a4d532cc73a2d4b8ad2b2ac6b26c5b0ee8751ca719e1745c9715c3723c4f0bc1fac14ca8a928c8b22a8964388e8c47152469514554344d88e130cd0b0ad0705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db4d34d34934da4d34d34d34d34d269249b4d3692492489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 31), (facetIndex 33), (facetIndex 37), (facetIndex 61)]))
 (.leaf ([(facetIndex 42), (facetIndex 44), (facetIndex 46), (facetIndex 65)])))
 (.branch 3
 (.leaf ([(facetIndex 48), (facetIndex 49), (facetIndex 67), (facetIndex 68)]))
 (.leaf ([(facetIndex 29), (facetIndex 74), (facetIndex 75)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 32), (facetIndex 34), (facetIndex 51), (facetIndex 79)]))
 (.leaf ([(facetIndex 43), (facetIndex 45), (facetIndex 53), (facetIndex 83)])))
 (.branch 7
 (.leaf ([(facetIndex 27), (facetIndex 30), (facetIndex 57), (facetIndex 59), (facetIndex 73), (facetIndex 77)]))
 (.leaf ([(facetIndex 26), (facetIndex 39), (facetIndex 55), (facetIndex 63), (facetIndex 71), (facetIndex 81)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "a388306f0e02408e00c30e28812069a40e00104198dcz13;"⟩
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
def grouped2_0008 : List Nat := [4, 5]
def grouped2_0009 : List Nat := [4, 5, 6, 7]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record014" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record014" 52

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record014" "{\"ridges\":[[10,84],[14,112],[29,140],[31,84],[44,41],[48,112],[55,84],[56,153],[57,41],[59,84],[61,84],[63,112],[64,41],[67,112],[73,140],[74,328],[75,140],[86,216],[88,228]],\"owners\":[[10,84,[70,76,78,84,86,88],[31,55,59,61]],[31,84,[84,86,88],[10,55,59,61,70,76,78]],[55,84,[76,78,88],[10,31,59,61,70,84,86]],[59,84,[70,78,86],[10,31,55,61,76,84,88]],[61,84,[70,76,84,86,88],[10,31,55,59,78]],[74,328,[13,65],[24,46,82]],[14,112,[76,80,84,88,89],[48,59,63,67]],[48,112,[84,88,89],[14,59,63,67,76,80]],[63,112,[76,88],[14,48,59,67,80,84,89]],[67,112,[76,80,84,88,89],[14,48,59,63]],[29,140,[85,86,87],[16,56,58,71,73,75]],[73,140,[56,86],[16,29,58,71,75,85,87]],[75,140,[56,58,85,86,87],[16,29,71,73]],[56,153,[41,64],[]],[86,216,[89],[]],[88,228,[87],[]]],\"edges\":[[31,[10,14,31,40,48,50,55,59,61,63,67,70,76,78,80,84,86,88,89]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record014" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record014\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-11],[-18,-4],[-18,-9],[-18,-17],[-19,-2],[-19,-12],[-19,-14],[-20,-7],[-20,-19],[-21,-20],[-23,-18],[-25,-19],[-28,-18],[-30,-10],[-30,-16],[-30,-27],[-31,-5],[-32,-30],[-33,-20],[-34,-30],[-35,-30],[-36,-18],[-37,-4],[-37,-9],[-37,-17],[-37,-23],[-37,-28],[-37,-36],[-38,-4],[-38,-9],[-38,-17],[-38,-23],[-38,-28],[-38,-36],[-40,-5],[-40,-7],[-40,-19],[-40,-21],[-40,-33],[-42,-4],[-42,-9],[-42,-17],[-42,-23],[-42,-28],[-42,-36],[-13,-19,-24],[-1,27,32,34,37,39,41],[-8,37,39,41],[-17,32,34,41],[-21,27,34,39],[-22,27,32,37,39,41],[-30,2,25],[-3,32,35,37,41,42],[-15,37,41,42],[-23,32,41],[-26,32,35,37,41,42],[-6,38,39,40],[-29,18,39],[-31,18,20,38,39,40],[-18,11,24],[-39,42],[-41,40],[-43,12,13,14,25],[-44,6,30,31],[-45,5,7,19,21,29,33],[-46,4,9,17,23,28,36],[-47,43],[-48,44],[-49,47],[-49,48],[-50,45],[-50,46],[-51,50],[-52,49],[-52,51],[52],[1,3,8,10,15,16,17,21,22,23,26,27,32,34,35,37,39,41,42]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":56,\"b\":26},{\"tag\":\"incompatible\",\"a\":56,\"b\":39},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":13},{\"tag\":\"incompatible\",\"a\":57,\"b\":42},{\"tag\":\"incompatible\",\"a\":57,\"b\":46},{\"tag\":\"incompatible\",\"a\":58,\"b\":30},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":63,\"b\":56},{\"tag\":\"incompatible\",\"a\":65,\"b\":57},{\"tag\":\"incompatible\",\"a\":71,\"b\":56},{\"tag\":\"incompatible\",\"a\":74,\"b\":40},{\"tag\":\"incompatible\",\"a\":74,\"b\":50},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":75,\"b\":27},{\"tag\":\"incompatible\",\"a\":76,\"b\":74},{\"tag\":\"incompatible\",\"a\":77,\"b\":58},{\"tag\":\"incompatible\",\"a\":78,\"b\":74},{\"tag\":\"incompatible\",\"a\":80,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":56},{\"tag\":\"incompatible\",\"a\":84,\"b\":26},{\"tag\":\"incompatible\",\"a\":84,\"b\":39},{\"tag\":\"incompatible\",\"a\":84,\"b\":55},{\"tag\":\"incompatible\",\"a\":84,\"b\":63},{\"tag\":\"incompatible\",\"a\":84,\"b\":71},{\"tag\":\"incompatible\",\"a\":84,\"b\":81},{\"tag\":\"incompatible\",\"a\":85,\"b\":26},{\"tag\":\"incompatible\",\"a\":85,\"b\":39},{\"tag\":\"incompatible\",\"a\":85,\"b\":55},{\"tag\":\"incompatible\",\"a\":85,\"b\":63},{\"tag\":\"incompatible\",\"a\":85,\"b\":71},{\"tag\":\"incompatible\",\"a\":85,\"b\":81},{\"tag\":\"incompatible\",\"a\":87,\"b\":27},{\"tag\":\"incompatible\",\"a\":87,\"b\":30},{\"tag\":\"incompatible\",\"a\":87,\"b\":57},{\"tag\":\"incompatible\",\"a\":87,\"b\":59},{\"tag\":\"incompatible\",\"a\":87,\"b\":77},{\"tag\":\"incompatible\",\"a\":89,\"b\":26},{\"tag\":\"incompatible\",\"a\":89,\"b\":39},{\"tag\":\"incompatible\",\"a\":89,\"b\":55},{\"tag\":\"incompatible\",\"a\":89,\"b\":63},{\"tag\":\"incompatible\",\"a\":89,\"b\":71},{\"tag\":\"incompatible\",\"a\":89,\"b\":81},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[44,57,64]},{\"tag\":\"mate\",\"ridge\":84,\"a\":10,\"owners\":[70,76,78,84,86,88]},{\"tag\":\"mate\",\"ridge\":84,\"a\":31,\"owners\":[84,86,88]},{\"tag\":\"mate\",\"ridge\":84,\"a\":55,\"owners\":[76,78,88]},{\"tag\":\"mate\",\"ridge\":84,\"a\":59,\"owners\":[70,78,86]},{\"tag\":\"mate\",\"ridge\":84,\"a\":61,\"owners\":[70,76,84,86,88]},{\"tag\":\"mate\",\"ridge\":328,\"a\":74,\"owners\":[13,65]},{\"tag\":\"mate\",\"ridge\":112,\"a\":14,\"owners\":[76,80,84,88,89]},{\"tag\":\"mate\",\"ridge\":112,\"a\":48,\"owners\":[84,88,89]},{\"tag\":\"mate\",\"ridge\":112,\"a\":63,\"owners\":[76,88]},{\"tag\":\"mate\",\"ridge\":112,\"a\":67,\"owners\":[76,80,84,88,89]},{\"tag\":\"mate\",\"ridge\":140,\"a\":29,\"owners\":[85,86,87]},{\"tag\":\"mate\",\"ridge\":140,\"a\":73,\"owners\":[56,86]},{\"tag\":\"mate\",\"ridge\":140,\"a\":75,\"owners\":[56,58,85,86,87]},{\"tag\":\"mate\",\"ridge\":153,\"a\":56,\"owners\":[41,64]},{\"tag\":\"mate\",\"ridge\":216,\"a\":86,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":228,\"a\":88,\"owners\":[87]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[42,44,46,65],\"full_literals\":[-43,12,13,14,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[29,74,75],\"full_literals\":[-44,6,30,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[27,30,57,59,73,77],\"full_literals\":[-45,5,7,19,21,29,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[26,39,55,63,71,81],\"full_literals\":[-46,4,9,17,23,28,36]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-49,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-52,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-52,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"edge\",\"edge\":31,\"owners\":[10,14,31,40,48,50,55,59,61,63,67,70,76,78,80,84,86,88,89]}]}"
  "p cnf 52 77\n-13 -11 0\n-18 -4 0\n-18 -9 0\n-18 -17 0\n-19 -2 0\n-19 -12 0\n-19 -14 0\n-20 -7 0\n-20 -19 0\n-21 -20 0\n-23 -18 0\n-25 -19 0\n-28 -18 0\n-30 -10 0\n-30 -16 0\n-30 -27 0\n-31 -5 0\n-32 -30 0\n-33 -20 0\n-34 -30 0\n-35 -30 0\n-36 -18 0\n-37 -4 0\n-37 -9 0\n-37 -17 0\n-37 -23 0\n-37 -28 0\n-37 -36 0\n-38 -4 0\n-38 -9 0\n-38 -17 0\n-38 -23 0\n-38 -28 0\n-38 -36 0\n-40 -5 0\n-40 -7 0\n-40 -19 0\n-40 -21 0\n-40 -33 0\n-42 -4 0\n-42 -9 0\n-42 -17 0\n-42 -23 0\n-42 -28 0\n-42 -36 0\n-13 -19 -24 0\n-1 27 32 34 37 39 41 0\n-8 37 39 41 0\n-17 32 34 41 0\n-21 27 34 39 0\n-22 27 32 37 39 41 0\n-30 2 25 0\n-3 32 35 37 41 42 0\n-15 37 41 42 0\n-23 32 41 0\n-26 32 35 37 41 42 0\n-6 38 39 40 0\n-29 18 39 0\n-31 18 20 38 39 40 0\n-18 11 24 0\n-39 42 0\n-41 40 0\n-43 12 13 14 25 0\n-44 6 30 31 0\n-45 5 7 19 21 29 33 0\n-46 4 9 17 23 28 36 0\n-47 43 0\n-48 44 0\n-49 47 0\n-49 48 0\n-50 45 0\n-50 46 0\n-51 50 0\n-52 49 0\n-52 51 0\n52 0\n1 3 8 10 15 16 17 21 22 23 26 27 32 34 35 37 39 41 42 0\n"
  "78 49 0 76 74 0\n79 51 0 76 75 0\n80 47 0 78 69 0\n81 48 0 78 70 0\n82 50 0 79 73 0\n83 43 0 80 67 0\n84 44 0 81 68 0\n85 45 0 82 71 0\n86 46 0 82 72 0\n87 -37 0 86 23 24 25 26 27 28 66 0\n88 -38 0 86 29 30 31 32 33 34 66 0\n89 3 42 8 1 10 16 17 21 22 23 26 27 32 34 35 15 41 0 87 77 61 0\n90 -19 39 0 83 84 88 5 6 7 9 12 37 52 63 57 64 1 46 59 60 0\n91 -18 0 86 2 3 4 11 13 22 66 0\n92 -31 40 39 0 91 88 85 58 90 17 59 8 10 19 65 0\n93 40 42 0 88 84 87 61 62 57 54 48 92 64 14 15 16 18 20 21 49 55 51 47 50 53 56 89 0\n94 42 0 91 85 61 90 58 93 35 36 38 39 65 0\n95 -4 0 94 40 0\n96 -9 0 94 41 0\n97 -17 0 94 42 0\n98 -23 0 94 43 0\n99 -28 0 94 44 0\n100 -36 0 94 45 0\n101 0 100 99 86 95 97 96 98 66 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00090.record014_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00090.record014
