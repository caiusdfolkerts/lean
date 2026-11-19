module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00015Frames
public import GraphInputsRow26Part00015Leaves
public import GraphInputsRow26Part00015Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00015.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ce1b4c725c4f1b23aa5a699964d8b6338ae1783ef07316c7293a719966394e745715a5c5595955352d70d934cd4b4ad8751d1743d68ce364e534ccb392ccb2ac6b86c5b61d2729d1725c570dc8f0bc3a3184e079a1c4531926190e585315151341d30ca30cc4b0ac1b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6db4d26936924d249a6d26d24926d2492493492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 62), (facetIndex 71)]))
 (.leaf ([(facetIndex 42), (facetIndex 57)])))
 (.branch 3
 (.leaf ([(facetIndex 50), (facetIndex 67)]))
 (.branch 4
 (.leaf ([(facetIndex 80), (facetIndex 84)]))
 (.leaf ([(facetIndex 74), (facetIndex 81)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 51), (facetIndex 54), (facetIndex 68)]))
 (.leaf ([(facetIndex 83), (facetIndex 85), (facetIndex 87)])))
 (.branch 8
 (.leaf ([(facetIndex 32), (facetIndex 43), (facetIndex 55)]))
 (.branch 9
 (.leaf ([(facetIndex 76), (facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 79), (facetIndex 82), (facetIndex 86)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "69636943988804000005200000000010750052000000710000000007z20;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00015.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00015.record011" 54

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00015.record011" "{\"ridges\":[[14,385],[14,388],[17,577],[19,784],[20,416],[33,388],[39,577],[42,594],[43,402],[45,416],[53,577],[57,596],[58,388],[59,784],[60,416],[61,385],[62,836],[65,584],[66,784],[69,416],[70,784],[71,960],[78,402],[79,294],[80,594],[82,402],[84,596],[86,180]],\"owners\":[[14,385,[20,43,45,69,71],[33,58,61]],[61,385,[20,43,45,69],[14,33,58,71]],[14,388,[78,79,86],[33,58,60,61]],[33,388,[86],[14,58,60,61,78,79]],[58,388,[79],[14,33,60,61,78,86]],[17,577,[42,57,62,71],[39,53,65]],[39,577,[57,62,71],[17,42,53,65]],[53,577,[42,71],[17,39,57,62,65]],[65,584,[],[17,39,53,80,84]],[19,784,[85,87],[59,66,70]],[59,784,[87],[19,66,70,85]],[66,784,[],[19,59,70,85,87]],[70,784,[85],[19,59,66,87]],[20,416,[79,82,86],[45,60,69]],[45,416,[86],[20,60,69,79,82]],[60,416,[82],[20,45,69,79,86]],[69,416,[79],[20,45,60,82,86]],[79,294,[32,77],[]],[42,594,[80],[]],[80,594,[42],[]],[43,402,[78,82],[]],[78,402,[43,82],[]],[82,402,[43,78],[]],[86,180,[55,76],[]],[57,596,[84],[]],[84,596,[57],[]],[62,836,[],[]],[71,960,[],[]]],\"edges\":[[41,[17,39,42,53,57,62,65,71,80,84]],[42,[14,20,33,43,45,58,60,61,69,71,78,79,82,86]],[44,[19,54,59,62,66,68,70,71,85,87]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00015.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00015.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,4,9,10,23,25],[-18,4,9,10,23],[-1,28,29,34],[-6,34],[-15,29],[-2,8,14,19,25],[-7,14,19,25],[-11,8,25],[-20],[-3,33,35],[-16,35],[-21],[-24,33],[-4,29,31,34],[-10,34],[-17,31],[-23,29],[-29,5,27],[-8,30],[-30,8],[-9,28,31],[-28,9,31],[-31,9,28],[-34,13,26],[-14,32],[-32,14],[-19],[-25],[-36,19,25],[-37,8,14],[-8,37],[-14,37],[-30,38],[-32,38],[-12,39],[-22,39],[-33,40],[-35,40],[-5,41],[-9,41],[-13,41],[-26,42],[-27,42],[-28,42],[-43,29,31,34],[-29,43],[-31,43],[-34,43],[-44,36,37],[-37,44],[-38,45],[-45,46],[-47,44,46],[-46,47],[-44,47],[-44,-46,48],[-40,49],[-39,49],[-43,50],[-42,50],[-42,-43,51],[-51,52],[-41,-50,52],[-49,-52,53],[-48,-53,54],[-54],[2,7,8,11,14,19,20,25,30,32],[1,4,6,9,10,15,17,18,23,25,28,29,31,34],[3,12,16,19,21,22,24,25,33,35]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":385,\"a\":14,\"owners\":[20,43,45,69,71]},{\"tag\":\"mate\",\"ridge\":385,\"a\":61,\"owners\":[20,43,45,69]},{\"tag\":\"mate\",\"ridge\":388,\"a\":14,\"owners\":[78,79,86]},{\"tag\":\"mate\",\"ridge\":388,\"a\":33,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":388,\"a\":58,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":577,\"a\":17,\"owners\":[42,57,62,71]},{\"tag\":\"mate\",\"ridge\":577,\"a\":39,\"owners\":[57,62,71]},{\"tag\":\"mate\",\"ridge\":577,\"a\":53,\"owners\":[42,71]},{\"tag\":\"mate\",\"ridge\":584,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":784,\"a\":19,\"owners\":[85,87]},{\"tag\":\"mate\",\"ridge\":784,\"a\":59,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":784,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":784,\"a\":70,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":416,\"a\":20,\"owners\":[79,82,86]},{\"tag\":\"mate\",\"ridge\":416,\"a\":45,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":416,\"a\":60,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":416,\"a\":69,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":294,\"a\":79,\"owners\":[32,77]},{\"tag\":\"mate\",\"ridge\":594,\"a\":42,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":594,\"a\":80,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":402,\"a\":43,\"owners\":[78,82]},{\"tag\":\"mate\",\"ridge\":402,\"a\":78,\"owners\":[43,82]},{\"tag\":\"mate\",\"ridge\":402,\"a\":82,\"owners\":[43,78]},{\"tag\":\"mate\",\"ridge\":180,\"a\":86,\"owners\":[55,76]},{\"tag\":\"mate\",\"ridge\":596,\"a\":57,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":596,\"a\":84,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":836,\"a\":62,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":960,\"a\":71,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[62,71],\"full_literals\":[-36,19,25]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[42,57],\"full_literals\":[-37,8,14]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":42,\"full_literals\":[-8,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":57,\"full_literals\":[-14,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":80,\"full_literals\":[-30,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":84,\"full_literals\":[-32,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":54,\"full_literals\":[-12,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":68,\"full_literals\":[-22,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":85,\"full_literals\":[-33,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-35,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":32,\"full_literals\":[-5,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":43,\"full_literals\":[-9,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":55,\"full_literals\":[-13,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":76,\"full_literals\":[-26,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":77,\"full_literals\":[-27,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":78,\"full_literals\":[-28,42]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[79,82,86],\"full_literals\":[-43,29,31,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":79,\"full_literals\":[-29,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":82,\"full_literals\":[-31,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":86,\"full_literals\":[-34,43]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-46,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-43,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-50,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-49,-52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-48,-53,54],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[17,39,42,53,57,62,65,71,80,84]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[14,20,33,43,45,58,60,61,69,71,78,79,82,86]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[19,54,59,62,66,68,70,71,85,87]}]}"
  "70 -36 0 27 28 29 0\n71 -44 37 0 70 49 0\n72 2 7 8 11 14 30 32 0 27 9 28 67 0\n73 1 4 6 9 10 15 17 18 23 28 29 31 34 0 28 68 0\n74 3 12 16 22 24 33 35 0 27 12 28 69 0\n75 47 0 28 27 54 55 52 50 51 31 32 33 34 8 7 6 72 0\n76 49 0 57 58 37 38 35 36 10 13 11 74 0\n77 46 0 75 52 53 51 71 33 34 19 25 30 0\n78 37 0 28 27 31 32 8 20 7 26 6 72 0\n79 44 0 78 50 0\n80 48 0 79 77 56 0\n81 -53 0 80 66 65 0\n82 -52 0 81 76 64 0\n83 -51 0 82 62 0\n84 -43 41 0 83 41 40 39 61 42 43 44 24 18 23 45 0\n85 4 34 1 6 9 10 17 15 23 28 29 31 0 73 2 0\n86 41 0 28 40 84 46 47 48 5 14 17 16 22 4 15 1 85 0\n87 -50 0 86 82 63 0\n88 -43 0 87 59 0\n89 -42 0 87 60 0\n90 -29 0 88 46 0\n91 -31 0 88 47 0\n92 -34 0 88 48 0\n93 -28 0 89 44 0\n94 -15 0 90 5 0\n95 -4 0 90 91 92 14 0\n96 -23 0 90 17 0\n97 -17 0 91 16 0\n98 -6 0 92 4 0\n99 -10 0 92 15 0\n100 -1 0 93 90 92 3 0\n101 -9 0 93 91 21 0\n102 0 95 100 92 98 101 99 97 94 96 93 90 91 85 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00015.record011
