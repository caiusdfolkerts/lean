module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow30Part00024Frames
public import GraphInputsRow30Part00024Leaves
public import GraphInputsRow30Part00024Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00024.record012
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "760f8e90f4cb1ac3b19c370bc1f1d23cb2a5687ac99a639b16658d62d876c3a2e4b86e1783e3c4e9664d92e479e16a539715654d52d475c358d3362d2b46d4749d1743d98ce3c4d9334cb31cf0b8ad1b0ef0761cc729c6785d1725c570de0f43c4f6511c1a91a16b06899164382e078e13446916625294950b41d88c6314c4b0ac1b81c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6da6db6d24da4db49249269a6934936da4924926d34d249b492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 90), (facetIndex 94), (facetIndex 102), (facetIndex 105)]))
 (.leaf ([(facetIndex 46), (facetIndex 103)])))
 (.branch 3
 (.leaf ([(facetIndex 41), (facetIndex 51), (facetIndex 62), (facetIndex 63), (facetIndex 71)]))
 (.branch 4
 (.leaf ([(facetIndex 50), (facetIndex 68), (facetIndex 75)]))
 (.leaf ([(facetIndex 96), (facetIndex 107)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 40), (facetIndex 48), (facetIndex 64)]))
 (.branch 7
 (.leaf ([(facetIndex 61), (facetIndex 73), (facetIndex 84)]))
 (.leaf ([(facetIndex 85), (facetIndex 86), (facetIndex 97)]))))
 (.branch 9
 (.leaf ([(facetIndex 89), (facetIndex 95), (facetIndex 104)]))
 (.branch 10
 (.leaf ([(facetIndex 98), (facetIndex 99)]))
 (.leaf ([(facetIndex 101), (facetIndex 106)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "4a0810a0997480000080077600000000306020030005226000000000230501000025z28;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
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
def grouped3_0011 : List Nat := [5, 6, 7]
def grouped3_0012 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0013 : List Nat := [6]
def grouped3_0014 : List Nat := [6, 7]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [8, 9, 10]
def grouped3_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [9, 10]
def grouped3_0020 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00024.record012" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00024.record012" 72

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00024.record012" "{\"ridges\":[[13,164],[17,193],[18,224],[24,772],[29,388],[29,400],[41,387],[42,772],[49,208],[50,387],[51,785],[52,224],[59,164],[62,393],[63,777],[67,388],[69,224],[70,164],[71,897],[75,393],[76,224],[77,224],[83,772],[87,400],[88,772],[90,418],[91,770],[94,808],[96,450],[100,400],[102,424],[103,808],[105,928],[107,456]],\"owners\":[[13,164,[85,89,90,98,101,102,104,105],[39,59,65,69,70]],[59,164,[85,89,90,104,105],[13,39,65,69,70,98,101,102]],[70,164,[85,89,90,98,101,102,104],[13,39,59,65,69,105]],[17,193,[18,40,52,61,69,76],[49,66,74]],[49,208,[99,104,106,107],[17,66,74,77,86,95,96]],[18,224,[89,95,101,104,106],[52,69,76,77]],[52,224,[101,104,106],[18,69,76,77,89,95]],[69,224,[95,106],[18,52,76,77,89,101,104]],[76,224,[89,95,104],[18,52,69,77,101,106]],[77,224,[89,101],[18,52,69,76,95,104,106]],[91,770,[46,51],[24,42,83,88,94]],[24,772,[63,68,71,103,105],[42,83,88,91]],[42,772,[103,105],[24,63,68,71,83,88,91]],[83,772,[68,71,105],[24,42,63,88,91,103]],[88,772,[63,71,103,105],[24,42,68,83,91]],[29,388,[41,62,71,90,102,105],[67,87,100]],[67,388,[90,102,105],[29,41,62,71,87,100]],[29,400,[50,75,96,107],[67,87,100]],[87,400,[75,107],[29,50,67,96,100]],[100,400,[50,96],[29,67,75,87,107]],[41,387,[50],[]],[50,387,[41],[]],[63,777,[46],[]],[51,785,[68],[]],[62,393,[75],[]],[75,393,[62],[]],[71,897,[],[]],[90,418,[],[]],[94,808,[103],[]],[103,808,[94],[]],[96,450,[],[]],[102,424,[],[]],[105,928,[],[]],[107,456,[],[]]],\"edges\":[[36,[13,18,39,48,52,59,65,69,70,73,76,77,85,89,90,95,98,101,102,104,105,106]],[39,[17,18,40,49,52,61,66,69,74,76,77,86,89,95,96,99,101,104,106,107]],[42,[29,41,50,62,67,71,75,87,90,96,100,102,105,107]],[44,[24,42,46,51,63,68,71,83,88,91,94,103,105]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00024.record012" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00024.record012\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-6],[-13,-10],[-13,-11],[-15,-13],[-20,-8],[-23,-8],[-23,-13],[-23,-18],[-29,-10],[-29,-17],[-29,-21],[-29,-23],[-29,-28],[-30,-29],[-33,-13],[-35,-23],[-37,-13],[-41,-13],[-44,-29],[-45,-23],[-46,-29],[-51,-29],[-1,33,37,38,43,46,47,49,50],[-16,33,37,38,49,50],[-25,33,37,38,43,46,47,49],[-2,3,7,15,17,24,30],[-12,44,49,51,52],[-3,37,41,46,49,51],[-15,46,49,51],[-24,41,51],[-30,37,41,49],[-31,37,46],[-39,10,14],[-4,19,23,26,48,50],[-9,48,50],[-32,23,26,50],[-36,19,26,48,50],[-5,8,18,26,38,47,50],[-22,38,47,50],[-5,13,29,42,52],[-35,29,52],[-45,13,42],[-8,13],[-13,8],[-19,10],[-14,23],[-18,29],[-29,18],[-26],[-38],[-40,48],[-48,40],[-42],[-47],[-50],[-52],[-40,53],[-48,54],[-8,55],[-18,55],[-56,13,23,29],[-13,56],[-29,56],[-7,57],[-27,58],[-34,59],[-37,60],[-41,60],[-49,60],[-43,61],[-46,62],[-51,62],[-53,-54,63],[-56,64],[-55,-64,65],[-63,-65,66],[-59,67],[-58,67],[-67,68],[-57,68],[-62,69],[-61,69],[-69,70],[-60,70],[-70,71],[-68,71],[-66,-71,72],[-72],[1,3,6,11,15,16,20,24,25,27,30,31,33,37,38,41,43,46,47,49,50,51],[2,3,7,12,15,17,21,24,28,30,31,34,37,41,42,44,46,49,51,52],[5,8,13,18,22,26,29,35,38,42,45,47,50,52],[4,9,10,14,19,23,26,32,36,39,40,48,50]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":50,\"b\":39},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":65,\"b\":41},{\"tag\":\"incompatible\",\"a\":68,\"b\":41},{\"tag\":\"incompatible\",\"a\":68,\"b\":50},{\"tag\":\"incompatible\",\"a\":68,\"b\":62},{\"tag\":\"incompatible\",\"a\":75,\"b\":46},{\"tag\":\"incompatible\",\"a\":75,\"b\":61},{\"tag\":\"incompatible\",\"a\":75,\"b\":66},{\"tag\":\"incompatible\",\"a\":75,\"b\":68},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":85,\"b\":50},{\"tag\":\"incompatible\",\"a\":87,\"b\":68},{\"tag\":\"incompatible\",\"a\":89,\"b\":50},{\"tag\":\"incompatible\",\"a\":95,\"b\":50},{\"tag\":\"incompatible\",\"a\":99,\"b\":75},{\"tag\":\"incompatible\",\"a\":100,\"b\":68},{\"tag\":\"incompatible\",\"a\":101,\"b\":75},{\"tag\":\"incompatible\",\"a\":106,\"b\":75},{\"tag\":\"mate\",\"ridge\":164,\"a\":13,\"owners\":[85,89,90,98,101,102,104,105]},{\"tag\":\"mate\",\"ridge\":164,\"a\":59,\"owners\":[85,89,90,104,105]},{\"tag\":\"mate\",\"ridge\":164,\"a\":70,\"owners\":[85,89,90,98,101,102,104]},{\"tag\":\"mate\",\"ridge\":193,\"a\":17,\"owners\":[18,40,52,61,69,76]},{\"tag\":\"mate\",\"ridge\":208,\"a\":49,\"owners\":[99,104,106,107]},{\"tag\":\"mate\",\"ridge\":224,\"a\":18,\"owners\":[89,95,101,104,106]},{\"tag\":\"mate\",\"ridge\":224,\"a\":52,\"owners\":[101,104,106]},{\"tag\":\"mate\",\"ridge\":224,\"a\":69,\"owners\":[95,106]},{\"tag\":\"mate\",\"ridge\":224,\"a\":76,\"owners\":[89,95,104]},{\"tag\":\"mate\",\"ridge\":224,\"a\":77,\"owners\":[89,101]},{\"tag\":\"mate\",\"ridge\":770,\"a\":91,\"owners\":[46,51]},{\"tag\":\"mate\",\"ridge\":772,\"a\":24,\"owners\":[63,68,71,103,105]},{\"tag\":\"mate\",\"ridge\":772,\"a\":42,\"owners\":[103,105]},{\"tag\":\"mate\",\"ridge\":772,\"a\":83,\"owners\":[68,71,105]},{\"tag\":\"mate\",\"ridge\":772,\"a\":88,\"owners\":[63,71,103,105]},{\"tag\":\"mate\",\"ridge\":388,\"a\":29,\"owners\":[41,62,71,90,102,105]},{\"tag\":\"mate\",\"ridge\":388,\"a\":67,\"owners\":[90,102,105]},{\"tag\":\"mate\",\"ridge\":400,\"a\":29,\"owners\":[50,75,96,107]},{\"tag\":\"mate\",\"ridge\":400,\"a\":87,\"owners\":[75,107]},{\"tag\":\"mate\",\"ridge\":400,\"a\":100,\"owners\":[50,96]},{\"tag\":\"mate\",\"ridge\":387,\"a\":41,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":387,\"a\":50,\"owners\":[41]},{\"tag\":\"mate\",\"ridge\":777,\"a\":63,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":785,\"a\":51,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":393,\"a\":62,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":393,\"a\":75,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":897,\"a\":71,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":418,\"a\":90,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":808,\"a\":94,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":808,\"a\":103,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":450,\"a\":96,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":424,\"a\":102,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":928,\"a\":105,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":456,\"a\":107,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":94,\"full_literals\":[-40,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":103,\"full_literals\":[-48,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":41,\"full_literals\":[-8,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":62,\"full_literals\":[-18,55]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[50,68,75],\"full_literals\":[-56,13,23,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":50,\"full_literals\":[-13,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":75,\"full_literals\":[-29,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":40,\"full_literals\":[-7,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":73,\"full_literals\":[-27,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-34,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":89,\"full_literals\":[-37,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":95,\"full_literals\":[-41,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":104,\"full_literals\":[-49,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":98,\"full_literals\":[-43,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":101,\"full_literals\":[-46,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":106,\"full_literals\":[-51,62]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-54,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-63,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":4,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":36,\"owners\":[13,18,39,48,52,59,65,69,70,73,76,77,85,89,90,95,98,101,102,104,105,106]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[17,18,40,49,52,61,66,69,74,76,77,86,89,95,96,99,101,104,106,107]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[29,41,50,62,67,71,75,87,90,96,100,102,105,107]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[24,42,46,51,63,68,71,83,88,91,94,103,105]}]}"
  "93 -22 0 55 50 54 39 0\n94 1 3 6 11 15 16 20 24 25 27 30 31 33 37 41 43 46 49 51 0 50 54 55 89 0\n95 2 3 7 12 15 17 21 24 28 30 31 34 37 41 44 46 49 51 0 53 56 90 0\n96 5 8 13 18 29 35 45 0 93 49 50 53 54 55 56 91 0\n97 4 9 10 14 19 23 32 36 39 40 48 0 49 55 92 0\n98 -23 0 55 54 50 49 6 7 8 12 16 20 38 96 0\n99 -32 0 98 49 55 36 0\n100 -14 0 98 46 0\n101 -10 -56 0 98 2 9 61 0\n102 48 10 0 55 49 99 98 100 33 45 35 51 37 34 97 0\n103 -13 -56 0 88 55 54 50 101 102 58 52 57 73 74 1 3 4 15 17 18 44 5 59 75 76 87 85 86 83 84 79 81 82 69 78 71 72 70 24 31 65 28 32 30 23 25 94 0\n104 -56 0 98 88 56 74 101 102 52 58 57 73 103 61 10 11 13 14 19 21 22 48 60 75 76 87 85 86 84 79 80 67 68 69 77 64 28 32 30 27 29 66 26 95 0\n105 -13 0 104 62 0\n106 -29 0 104 63 0\n107 -45 0 105 53 42 0\n108 -8 0 105 43 0\n109 -5 0 105 106 53 56 40 0\n110 -35 0 106 56 41 0\n111 -18 0 106 47 0\n112 0 109 111 105 108 106 110 107 96 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012 Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00024.record012
