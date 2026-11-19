module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00184Frames
public import GraphInputsRow29Part00184Leaves
public import GraphInputsRow29Part00184Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9e2749b25c8f07c74a726aa6a96a3a1e9c669966358762b86e1783ed85d19c5a99a699966391e5c56966559655356351d64d8b4ad1b61d1743d70da398d9394d5334e331cd8b92e2b4acab1ae1b16c3b61d4731d2729c3713c9c5889a198961588e0b81e985619462986499194951548d0b41d60d4348c6324c5322c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6db6924924d34926da4934d249249249349a492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 73), (facetIndex 80)]))
 (.leaf ([(facetIndex 74), (facetIndex 82)])))
 (.branch 3
 (.leaf ([(facetIndex 91), (facetIndex 97)]))
 (.branch 4
 (.leaf ([(facetIndex 92), (facetIndex 99)]))
 (.leaf ([(facetIndex 49), (facetIndex 52), (facetIndex 75)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 66), (facetIndex 68), (facetIndex 93)]))
 (.leaf ([(facetIndex 94), (facetIndex 95), (facetIndex 100)])))
 (.branch 8
 (.leaf ([(facetIndex 96), (facetIndex 98), (facetIndex 105)]))
 (.branch 9
 (.leaf ([(facetIndex 101), (facetIndex 102)]))
 (.leaf ([(facetIndex 103), (facetIndex 104)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "799886372766532000000001000000410000050500000000000004004z31;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record007" 53

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record007" "{\"ridges\":[[13,385],[13,386],[21,536],[23,592],[41,385],[41,386],[44,536],[50,385],[50,386],[52,562],[55,592],[56,385],[56,386],[58,385],[58,386],[59,385],[59,386],[62,536],[70,592],[73,420],[74,452],[76,552],[77,592],[78,536],[80,424],[81,608],[82,464],[91,420],[92,452],[97,424],[99,464]],\"owners\":[[13,385,[73,74,80,82],[41,50,56,58,59]],[41,385,[80,82],[13,50,56,58,59,73,74]],[50,385,[73,74,82],[13,41,56,58,59,80]],[56,385,[73,74,80],[13,41,50,58,59,82]],[58,385,[74,82],[13,41,50,56,59,73,80]],[59,385,[73,80],[13,41,50,56,58,74,82]],[13,386,[91,92,97,99],[41,50,56,58,59]],[41,386,[97,99],[13,50,56,58,59,91,92]],[50,386,[91,92,99],[13,41,56,58,59,97]],[56,386,[91,92,97],[13,41,50,58,59,99]],[58,386,[92,99],[13,41,50,56,59,91,97]],[59,386,[91,97],[13,41,50,56,58,92,99]],[21,536,[94,95,101,102,105],[44,62,76,77,78]],[44,536,[101,102,105],[21,62,76,77,78,94,95]],[62,536,[94,95,105],[21,44,76,77,78,101,102]],[78,536,[94,95,101,102,105],[21,44,62,76,77]],[76,552,[96,103],[22,48,65,79,94,101,105]],[23,592,[95,98,102,104,105],[55,70,77,81]],[55,592,[102,104,105],[23,70,77,81,95,98]],[70,592,[95,98,105],[23,55,77,81,102,104]],[77,592,[98,104],[23,55,70,81,95,102,105]],[81,608,[96,103],[25,57,72,79,83,98,104,105]],[52,562,[94,98],[]],[73,420,[91],[]],[91,420,[73],[]],[74,452,[92],[]],[92,452,[74],[]],[80,424,[97],[]],[97,424,[80],[]],[82,464,[99],[]],[99,464,[82],[]]],\"edges\":[[34,[21,23,44,52,55,62,68,70,76,77,78,81,94,95,98,101,102,104,105]],[42,[13,41,50,56,58,59,73,74,80,82,91,92,97,99]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,15,16,20,22],[-4,20,22],[-6,15,16,22],[-9,15,16,20],[-10,16,22],[-11,15,20],[-1,23,24,28,30],[-4,28,30],[-6,23,24,30],[-9,23,24,28],[-10,24,30],[-11,23,28],[-2,25,26,31,32,35],[-5,31,32,35],[-12,25,26,35],[-19,25,26,31,32,35],[-17,27,33],[-3,26,29,32,34,35],[-8,32,34,35],[-14,26,29,35],[-18,29,34],[-21,27,33],[-7,25,29],[-15,23],[-23,15],[-16,24],[-24,16],[-20,28],[-28,20],[-22,30],[-30,22],[-15,36],[-20,36],[-16,37],[-22,37],[-23,38],[-28,38],[-24,39],[-30,39],[-13,40],[-25,41],[-26,41],[-27,42],[-29,42],[-35,42],[-31,43],[-32,43],[-33,44],[-34,44],[-37,45],[-36,45],[-39,46],[-46,47],[-38,47],[-45,-47,48],[-41,49],[-40,49],[-44,50],[-43,50],[-50,51],[-42,51],[-51,52],[-49,52],[-48,-52,53],[-53],[2,3,5,7,8,12,13,14,17,18,19,21,25,26,29,31,32,34,35],[1,4,6,9,10,11,15,16,20,22,23,24,28,30]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":385,\"a\":13,\"owners\":[73,74,80,82]},{\"tag\":\"mate\",\"ridge\":385,\"a\":41,\"owners\":[80,82]},{\"tag\":\"mate\",\"ridge\":385,\"a\":50,\"owners\":[73,74,82]},{\"tag\":\"mate\",\"ridge\":385,\"a\":56,\"owners\":[73,74,80]},{\"tag\":\"mate\",\"ridge\":385,\"a\":58,\"owners\":[74,82]},{\"tag\":\"mate\",\"ridge\":385,\"a\":59,\"owners\":[73,80]},{\"tag\":\"mate\",\"ridge\":386,\"a\":13,\"owners\":[91,92,97,99]},{\"tag\":\"mate\",\"ridge\":386,\"a\":41,\"owners\":[97,99]},{\"tag\":\"mate\",\"ridge\":386,\"a\":50,\"owners\":[91,92,99]},{\"tag\":\"mate\",\"ridge\":386,\"a\":56,\"owners\":[91,92,97]},{\"tag\":\"mate\",\"ridge\":386,\"a\":58,\"owners\":[92,99]},{\"tag\":\"mate\",\"ridge\":386,\"a\":59,\"owners\":[91,97]},{\"tag\":\"mate\",\"ridge\":536,\"a\":21,\"owners\":[94,95,101,102,105]},{\"tag\":\"mate\",\"ridge\":536,\"a\":44,\"owners\":[101,102,105]},{\"tag\":\"mate\",\"ridge\":536,\"a\":62,\"owners\":[94,95,105]},{\"tag\":\"mate\",\"ridge\":536,\"a\":78,\"owners\":[94,95,101,102,105]},{\"tag\":\"mate\",\"ridge\":552,\"a\":76,\"owners\":[96,103]},{\"tag\":\"mate\",\"ridge\":592,\"a\":23,\"owners\":[95,98,102,104,105]},{\"tag\":\"mate\",\"ridge\":592,\"a\":55,\"owners\":[102,104,105]},{\"tag\":\"mate\",\"ridge\":592,\"a\":70,\"owners\":[95,98,105]},{\"tag\":\"mate\",\"ridge\":592,\"a\":77,\"owners\":[98,104]},{\"tag\":\"mate\",\"ridge\":608,\"a\":81,\"owners\":[96,103]},{\"tag\":\"mate\",\"ridge\":562,\"a\":52,\"owners\":[94,98]},{\"tag\":\"mate\",\"ridge\":420,\"a\":73,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":420,\"a\":91,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":452,\"a\":74,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":452,\"a\":92,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":424,\"a\":80,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":424,\"a\":97,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":464,\"a\":82,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":464,\"a\":99,\"owners\":[82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":73,\"full_literals\":[-15,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":80,\"full_literals\":[-20,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":74,\"full_literals\":[-16,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-22,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":91,\"full_literals\":[-23,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":97,\"full_literals\":[-28,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":92,\"full_literals\":[-24,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":99,\"full_literals\":[-30,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":68,\"full_literals\":[-13,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":94,\"full_literals\":[-25,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":95,\"full_literals\":[-26,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":96,\"full_literals\":[-27,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":98,\"full_literals\":[-29,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":105,\"full_literals\":[-35,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":101,\"full_literals\":[-31,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":102,\"full_literals\":[-32,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":103,\"full_literals\":[-33,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":104,\"full_literals\":[-34,44]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-48,-52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[21,23,44,52,55,62,68,70,76,77,78,81,94,95,98,101,102,104,105]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[13,41,50,56,58,59,73,74,80,82,91,92,97,99]}]}"
  "p cnf 53 67\n-1 15 16 20 22 0\n-4 20 22 0\n-6 15 16 22 0\n-9 15 16 20 0\n-10 16 22 0\n-11 15 20 0\n-1 23 24 28 30 0\n-4 28 30 0\n-6 23 24 30 0\n-9 23 24 28 0\n-10 24 30 0\n-11 23 28 0\n-2 25 26 31 32 35 0\n-5 31 32 35 0\n-12 25 26 35 0\n-19 25 26 31 32 35 0\n-17 27 33 0\n-3 26 29 32 34 35 0\n-8 32 34 35 0\n-14 26 29 35 0\n-18 29 34 0\n-21 27 33 0\n-7 25 29 0\n-15 23 0\n-23 15 0\n-16 24 0\n-24 16 0\n-20 28 0\n-28 20 0\n-22 30 0\n-30 22 0\n-15 36 0\n-20 36 0\n-16 37 0\n-22 37 0\n-23 38 0\n-28 38 0\n-24 39 0\n-30 39 0\n-13 40 0\n-25 41 0\n-26 41 0\n-27 42 0\n-29 42 0\n-35 42 0\n-31 43 0\n-32 43 0\n-33 44 0\n-34 44 0\n-37 45 0\n-36 45 0\n-39 46 0\n-46 47 0\n-38 47 0\n-45 -47 48 0\n-41 49 0\n-40 49 0\n-44 50 0\n-43 50 0\n-50 51 0\n-42 51 0\n-51 52 0\n-49 52 0\n-48 -52 53 0\n-53 0\n2 3 5 7 8 12 13 14 17 18 19 21 25 26 29 31 32 34 35 0\n1 4 6 9 10 11 15 16 20 22 23 24 28 30 0\n"
  "68 47 0 53 54 52 36 37 38 39 10 24 8 28 7 12 11 26 9 30 67 0\n69 45 0 50 51 34 35 32 33 5 27 31 3 4 25 2 29 1 6 67 0\n70 48 0 69 68 55 0\n71 -52 0 70 65 64 0\n72 -51 0 71 62 0\n73 -49 0 71 63 0\n74 -50 0 72 60 0\n75 -42 0 72 61 0\n76 -41 0 73 56 0\n77 -40 0 73 57 0\n78 -44 0 74 58 0\n79 -43 0 74 59 0\n80 -27 0 75 43 0\n81 -29 0 75 44 0\n82 -35 0 75 45 0\n83 -25 0 76 41 0\n84 -26 0 76 42 0\n85 -13 0 77 40 0\n86 -33 0 78 48 0\n87 -34 0 78 49 0\n88 -31 0 79 46 0\n89 -32 0 79 47 0\n90 -7 0 81 83 23 0\n91 -14 0 81 84 82 20 0\n92 -12 0 82 84 83 15 0\n93 -17 0 86 80 17 0\n94 -21 0 86 80 22 0\n95 -18 0 87 81 21 0\n96 -5 0 88 89 82 14 0\n97 -8 0 89 87 82 19 0\n98 -2 0 89 84 88 83 82 13 0\n99 -19 0 89 84 88 83 82 16 0\n100 -3 0 89 84 81 87 82 18 0\n101 0 93 99 98 100 97 92 85 96 90 95 91 94 83 84 81 88 89 87 82 66 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2789d26ca725c8f07c74a726aa6a96a3a1e9c669a6659a5635a361da4e8b8ae1ba1e1783e746716a669966391e5c56966559655356351d64d8b4ad1b61d1743d70da364d5334c7362d2b2ac6b16c3b61d4731d2729c3713e649522c8709c5889a198961588e0b81e58499194951548d0b41d60d4348c6324c5322c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "34924db6db6da4934d24926db6db6924d3492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 67), (facetIndex 73)]))
 (.leaf ([(facetIndex 68), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 89), (facetIndex 95)]))
 (.branch 4
 (.leaf ([(facetIndex 90), (facetIndex 97)]))
 (.leaf ([(facetIndex 60), (facetIndex 62), (facetIndex 69)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 91)]))
 (.leaf ([(facetIndex 72), (facetIndex 74), (facetIndex 98)])))
 (.branch 8
 (.leaf ([(facetIndex 82), (facetIndex 84), (facetIndex 104)]))
 (.branch 9
 (.leaf ([(facetIndex 92), (facetIndex 93)]))
 (.leaf ([(facetIndex 94), (facetIndex 96)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "700000639298853200007070000001606554100000404z3c;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record005" 50

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record005" "{\"ridges\":[[13,385],[13,386],[32,552],[34,608],[41,385],[41,386],[47,385],[47,386],[51,385],[51,386],[52,385],[52,386],[53,385],[53,386],[59,552],[62,561],[66,608],[67,420],[68,452],[73,424],[75,464],[81,552],[88,608],[89,420],[90,452],[95,424],[97,464],[99,552],[102,608],[103,608]],\"owners\":[[13,385,[67,68,73,75],[41,47,51,52,53]],[41,385,[73,75],[13,47,51,52,53,67,68]],[47,385,[67,68,75],[13,41,51,52,53,73]],[51,385,[67,68,73],[13,41,47,52,53,75]],[52,385,[68,75],[13,41,47,51,53,67,73]],[53,385,[67,73],[13,41,47,51,52,68,75]],[13,386,[89,90,95,97],[41,47,51,52,53]],[41,386,[95,97],[13,47,51,52,53,89,90]],[47,386,[89,90,97],[13,41,51,52,53,95]],[51,386,[89,90,95],[13,41,47,52,53,97]],[52,386,[90,97],[13,41,47,51,53,89,95]],[53,386,[89,95],[13,41,47,51,52,90,97]],[32,552,[70,72,92,94,104],[59,81,99,102]],[59,552,[92,94,104],[32,70,72,81,99,102]],[81,552,[70,72,104],[32,59,92,94,99,102]],[99,552,[72,94],[32,59,70,81,92,102,104]],[34,608,[72,74,94,96,104],[66,88,102,103]],[66,608,[94,96,104],[34,72,74,88,102,103]],[88,608,[72,74,104],[34,66,94,96,102,103]],[102,608,[74,96],[34,66,72,88,94,103,104]],[103,608,[72,94],[34,66,74,88,96,102,104]],[62,561,[70,74],[]],[67,420,[89],[]],[89,420,[67],[]],[68,452,[90],[]],[90,452,[68],[]],[73,424,[95],[]],[95,424,[73],[]],[75,464,[97],[]],[97,464,[75],[]]],\"edges\":[[38,[32,34,59,62,66,70,72,74,81,84,88,92,94,96,99,102,103,104]],[42,[13,41,47,51,52,53,67,68,73,75,89,90,95,97]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,12,13,16,18],[-4,16,18],[-5,12,13,18],[-6,12,13,16],[-7,13,18],[-8,12,16],[-1,22,23,26,28],[-4,26,28],[-5,22,23,28],[-6,22,23,26],[-7,23,28],[-8,22,26],[-2,14,15,24,25,32],[-9,24,25,32],[-19,14,15,32],[-29,15,25],[-3,15,17,25,27,32],[-11,25,27,32],[-21,15,17,32],[-30,17,27],[-31,15,25],[-10,14,17],[-12,22],[-22,12],[-13,23],[-23,13],[-16,26],[-26,16],[-18,28],[-28,18],[-12,33],[-16,33],[-13,34],[-18,34],[-22,35],[-26,35],[-23,36],[-28,36],[-14,37],[-15,38],[-17,38],[-20,39],[-32,39],[-24,40],[-25,41],[-27,41],[-34,42],[-33,42],[-36,43],[-43,44],[-35,44],[-42,-44,45],[-38,46],[-37,46],[-41,47],[-40,47],[-47,48],[-39,48],[-48,49],[-46,49],[-45,-49,50],[-50],[2,3,9,10,11,14,15,17,19,20,21,24,25,27,29,30,31,32],[1,4,5,6,7,8,12,13,16,18,22,23,26,28]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":385,\"a\":13,\"owners\":[67,68,73,75]},{\"tag\":\"mate\",\"ridge\":385,\"a\":41,\"owners\":[73,75]},{\"tag\":\"mate\",\"ridge\":385,\"a\":47,\"owners\":[67,68,75]},{\"tag\":\"mate\",\"ridge\":385,\"a\":51,\"owners\":[67,68,73]},{\"tag\":\"mate\",\"ridge\":385,\"a\":52,\"owners\":[68,75]},{\"tag\":\"mate\",\"ridge\":385,\"a\":53,\"owners\":[67,73]},{\"tag\":\"mate\",\"ridge\":386,\"a\":13,\"owners\":[89,90,95,97]},{\"tag\":\"mate\",\"ridge\":386,\"a\":41,\"owners\":[95,97]},{\"tag\":\"mate\",\"ridge\":386,\"a\":47,\"owners\":[89,90,97]},{\"tag\":\"mate\",\"ridge\":386,\"a\":51,\"owners\":[89,90,95]},{\"tag\":\"mate\",\"ridge\":386,\"a\":52,\"owners\":[90,97]},{\"tag\":\"mate\",\"ridge\":386,\"a\":53,\"owners\":[89,95]},{\"tag\":\"mate\",\"ridge\":552,\"a\":32,\"owners\":[70,72,92,94,104]},{\"tag\":\"mate\",\"ridge\":552,\"a\":59,\"owners\":[92,94,104]},{\"tag\":\"mate\",\"ridge\":552,\"a\":81,\"owners\":[70,72,104]},{\"tag\":\"mate\",\"ridge\":552,\"a\":99,\"owners\":[72,94]},{\"tag\":\"mate\",\"ridge\":608,\"a\":34,\"owners\":[72,74,94,96,104]},{\"tag\":\"mate\",\"ridge\":608,\"a\":66,\"owners\":[94,96,104]},{\"tag\":\"mate\",\"ridge\":608,\"a\":88,\"owners\":[72,74,104]},{\"tag\":\"mate\",\"ridge\":608,\"a\":102,\"owners\":[74,96]},{\"tag\":\"mate\",\"ridge\":608,\"a\":103,\"owners\":[72,94]},{\"tag\":\"mate\",\"ridge\":561,\"a\":62,\"owners\":[70,74]},{\"tag\":\"mate\",\"ridge\":420,\"a\":67,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":420,\"a\":89,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":452,\"a\":68,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":452,\"a\":90,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":424,\"a\":73,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":424,\"a\":95,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":464,\"a\":75,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":464,\"a\":97,\"owners\":[75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":67,\"full_literals\":[-12,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":73,\"full_literals\":[-16,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":68,\"full_literals\":[-13,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":75,\"full_literals\":[-18,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":89,\"full_literals\":[-22,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":95,\"full_literals\":[-26,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":90,\"full_literals\":[-23,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":97,\"full_literals\":[-28,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":70,\"full_literals\":[-14,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":72,\"full_literals\":[-15,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":74,\"full_literals\":[-17,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-20,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":104,\"full_literals\":[-32,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":92,\"full_literals\":[-24,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":94,\"full_literals\":[-25,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":96,\"full_literals\":[-27,41]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[32,34,59,62,66,70,72,74,81,84,88,92,94,96,99,102,103,104]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[13,41,47,51,52,53,67,68,73,75,89,90,95,97]}]}"
  "p cnf 50 64\n-1 12 13 16 18 0\n-4 16 18 0\n-5 12 13 18 0\n-6 12 13 16 0\n-7 13 18 0\n-8 12 16 0\n-1 22 23 26 28 0\n-4 26 28 0\n-5 22 23 28 0\n-6 22 23 26 0\n-7 23 28 0\n-8 22 26 0\n-2 14 15 24 25 32 0\n-9 24 25 32 0\n-19 14 15 32 0\n-29 15 25 0\n-3 15 17 25 27 32 0\n-11 25 27 32 0\n-21 15 17 32 0\n-30 17 27 0\n-31 15 25 0\n-10 14 17 0\n-12 22 0\n-22 12 0\n-13 23 0\n-23 13 0\n-16 26 0\n-26 16 0\n-18 28 0\n-28 18 0\n-12 33 0\n-16 33 0\n-13 34 0\n-18 34 0\n-22 35 0\n-26 35 0\n-23 36 0\n-28 36 0\n-14 37 0\n-15 38 0\n-17 38 0\n-20 39 0\n-32 39 0\n-24 40 0\n-25 41 0\n-27 41 0\n-34 42 0\n-33 42 0\n-36 43 0\n-43 44 0\n-35 44 0\n-42 -44 45 0\n-38 46 0\n-37 46 0\n-41 47 0\n-40 47 0\n-47 48 0\n-39 48 0\n-48 49 0\n-46 49 0\n-45 -49 50 0\n-50 0\n2 3 9 10 11 14 15 17 19 20 21 24 25 27 29 30 31 32 0\n1 4 5 6 7 8 12 13 16 18 22 23 26 28 0\n"
  "65 22 28 23 26 0 7 9 10 23 8 27 12 11 25 29 64 0\n66 44 0 50 51 49 35 36 37 38 65 0\n67 42 0 47 48 33 34 31 32 5 26 30 1 3 4 24 2 28 6 64 0\n68 45 0 67 66 52 0\n69 -49 0 68 62 61 0\n70 -48 0 69 59 0\n71 -46 0 69 60 0\n72 -47 0 70 57 0\n73 -39 0 70 58 0\n74 -38 0 71 53 0\n75 -37 0 71 54 0\n76 -41 0 72 55 0\n77 -40 0 72 56 0\n78 -20 0 73 42 0\n79 -32 0 73 43 0\n80 -15 0 74 40 0\n81 -17 0 74 41 0\n82 -14 0 75 39 0\n83 -25 0 76 45 0\n84 -27 0 76 46 0\n85 -24 0 77 44 0\n86 -21 0 79 81 80 19 0\n87 -19 0 79 80 82 15 0\n88 -10 0 82 81 22 0\n89 -11 0 83 84 79 18 0\n90 -29 0 83 80 16 0\n91 -3 0 83 81 80 84 79 17 0\n92 -31 0 83 80 21 0\n93 -30 0 84 81 20 0\n94 -9 0 85 83 79 14 0\n95 -2 0 85 82 80 83 79 13 0\n96 0 95 91 94 88 89 82 80 81 87 78 86 85 83 84 90 93 92 79 63 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "278752746b26c9723c1f1d29c9aa9aa5a8e87a719a659996558d61d98e4b8ae1b89e1783ed85d19c5a99a699966391e5c56966565655554d58d4756364d8b52d2b46d8745d0f5c368e6364e5354cd38cc7362e4b8ad2b2ac6b86c5b0ed8751cc749ca719d1725c570dd0f23c4f0bc1f5909c5889a9856194629864996154549465254552342d0758350d2318c9314c8b0ac1b"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db6db6db4db6db69b4d349269249269349249249249a4d24924934d349b4d2249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 38), (facetIndex 84)]))
 (.branch 2
 (.leaf ([(facetIndex 36), (facetIndex 40), (facetIndex 86)]))
 (.leaf ([(facetIndex 92), (facetIndex 93), (facetIndex 106)]))))
 (.branch 4
 (.leaf ([(facetIndex 96), (facetIndex 97), (facetIndex 108)]))
 (.branch 5
 (.leaf ([(facetIndex 94), (facetIndex 100), (facetIndex 113)]))
 (.leaf ([(facetIndex 98), (facetIndex 101), (facetIndex 115)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 30), (facetIndex 50), (facetIndex 68), (facetIndex 79)]))
 (.branch 8
 (.leaf ([(facetIndex 33), (facetIndex 53), (facetIndex 71), (facetIndex 102)]))
 (.leaf ([(facetIndex 89), (facetIndex 104), (facetIndex 109), (facetIndex 111)]))))
 (.branch 10
 (.leaf ([(facetIndex 91), (facetIndex 105), (facetIndex 112), (facetIndex 116)]))
 (.branch 11
 (.leaf ([(facetIndex 88), (facetIndex 103), (facetIndex 110)]))
 (.leaf ([(facetIndex 95), (facetIndex 107), (facetIndex 114)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "95b498a83b298a7540533b422908a0100000060000000700600000000000000700600000000010001007006z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [1, 2]
def grouped3_0006 : List Nat := [2]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4, 5]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [4, 5]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [7, 8]
def grouped3_0017 : List Nat := [8]
def grouped3_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [9, 10, 11]
def grouped3_0020 : List Nat := [10]
def grouped3_0021 : List Nat := [10, 11]
def grouped3_0022 : List Nat := [11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record006" 72

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record006" "{\"ridges\":[[8,385],[8,386],[17,388],[20,552],[23,608],[32,270],[38,166],[42,388],[49,552],[51,386],[57,385],[57,386],[58,608],[59,386],[60,385],[60,386],[67,552],[69,388],[75,388],[76,608],[77,388],[78,388],[80,552],[83,608],[84,424],[85,608],[86,464],[87,608],[94,270],[96,198],[97,278],[98,278],[100,166],[101,198],[106,424],[108,464],[113,424],[115,464]],\"owners\":[[8,385,[17,69,75,77,78,84,86],[51,57,59,60]],[57,385,[17,69,77,78,84],[8,51,59,60,75,86]],[60,385,[17,69,75,77,84],[8,51,57,59,78,86]],[8,386,[94,98,100,101,106,108],[42,51,57,59,60]],[51,386,[98,100,101,108],[8,42,57,59,60,94,106]],[57,386,[94,100,101,106],[8,42,51,59,60,98,108]],[59,386,[94,98,101,108],[8,42,51,57,60,100,106]],[60,386,[94,98,100,106],[8,42,51,57,59,101,108]],[17,388,[94,98,100,101,113,115],[42,69,75,77,78]],[42,388,[113,115],[17,69,75,77,78,94,98,100,101]],[69,388,[98,100,101,115],[17,42,75,77,78,94,113]],[75,388,[94,100,101,113],[17,42,69,77,78,98,115]],[77,388,[94,98,101,115],[17,42,69,75,78,100,113]],[78,388,[94,98,100,113],[17,42,69,75,77,101,115]],[20,552,[103,105,110,112,116],[49,67,80,83]],[49,552,[110,112,116],[20,67,80,83,103,105]],[67,552,[103,105,116],[20,49,80,83,110,112]],[80,552,[105,112],[20,49,67,83,103,110,116]],[23,608,[105,107,112,114,116],[58,76,83,85,87]],[58,608,[112,114,116],[23,76,83,85,87,105,107]],[76,608,[105,107,116],[23,58,83,85,87,112,114]],[83,608,[107,114],[23,58,76,85,87,105,112,116]],[85,608,[105,112],[23,58,76,83,87,107,114,116]],[87,608,[105,107,112,114,116],[23,58,76,83,85]],[32,270,[93,94],[]],[94,270,[32,93],[]],[97,278,[36,98],[]],[98,278,[36,97],[]],[38,166,[92,100],[]],[100,166,[38,92],[]],[96,198,[40,101],[]],[101,198,[40,96],[]],[84,424,[106,113],[]],[106,424,[84,113],[]],[113,424,[84,106],[]],[86,464,[108,115],[]],[108,464,[86,115],[]],[115,464,[86,108],[]]],\"edges\":[[38,[20,23,49,53,58,67,71,76,80,83,85,87,103,105,107,110,112,114,116]],[42,[8,17,42,51,57,59,60,69,75,77,78,84,86,94,98,100,101,106,108,113,115]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,2,18,20,22,23,26,28],[-13,2,18,22,23,26],[-16,2,18,20,22,26],[-1,32,35,36,37,40,42],[-11,35,36,37,42],[-13,32,36,37,40],[-15,32,35,37,42],[-16,32,35,36,40],[-2,32,35,36,37,45,47],[-9,45,47],[-18,35,36,37,47],[-20,32,36,37,45],[-22,32,35,37,47],[-23,32,35,36,45],[-3,38,39,43,44,48],[-10,43,44,48],[-17,38,39,48],[-24,39,44],[-4,39,41,44,46,48],[-14,44,46,48],[-21,39,41,48],[-25,41,46],[-27,39,44],[-29,39,41,44,46,48],[-5,31,32],[-32,5,31],[-34,6,35],[-35,6,34],[-7,30,36],[-36,7,30],[-33,8,37],[-37,8,33],[-26,40,45],[-40,26,45],[-45,26,40],[-28,42,47],[-42,28,47],[-47,28,42],[-49,5,7,26],[-5,49],[-7,49],[-26,49],[-6,50],[-8,50],[-28,50],[-30,51],[-31,51],[-40,51],[-52,33,34,42],[-33,52],[-34,52],[-42,52],[-53,32,36,45],[-32,53],[-36,53],[-45,53],[-54,35,37,47],[-35,54],[-37,54],[-47,54],[-12,55],[-19,55],[-39,56],[-44,56],[-48,56],[-38,57],[-43,57],[-41,58],[-46,58],[-51,59],[-50,59],[-60,49,59],[-59,60],[-49,60],[-49,-59,61],[-62,53,54],[-54,62],[-53,62],[-63,52,62],[-62,63],[-52,63],[-52,-62,64],[-65,60,63],[-63,65],[-64,66],[-60,65],[-60,-63,66],[-61,66],[-55,67],[-67,68],[-58,69],[-57,69],[-69,70],[-56,70],[-70,71],[-68,71],[-66,-71,72],[-72],[3,4,10,12,14,17,19,21,24,25,27,29,38,39,41,43,44,46,48],[1,2,9,11,13,15,16,18,20,22,23,26,28,32,35,36,37,40,42,45,47]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":385,\"a\":8,\"owners\":[17,69,75,77,78,84,86]},{\"tag\":\"mate\",\"ridge\":385,\"a\":57,\"owners\":[17,69,77,78,84]},{\"tag\":\"mate\",\"ridge\":385,\"a\":60,\"owners\":[17,69,75,77,84]},{\"tag\":\"mate\",\"ridge\":386,\"a\":8,\"owners\":[94,98,100,101,106,108]},{\"tag\":\"mate\",\"ridge\":386,\"a\":51,\"owners\":[98,100,101,108]},{\"tag\":\"mate\",\"ridge\":386,\"a\":57,\"owners\":[94,100,101,106]},{\"tag\":\"mate\",\"ridge\":386,\"a\":59,\"owners\":[94,98,101,108]},{\"tag\":\"mate\",\"ridge\":386,\"a\":60,\"owners\":[94,98,100,106]},{\"tag\":\"mate\",\"ridge\":388,\"a\":17,\"owners\":[94,98,100,101,113,115]},{\"tag\":\"mate\",\"ridge\":388,\"a\":42,\"owners\":[113,115]},{\"tag\":\"mate\",\"ridge\":388,\"a\":69,\"owners\":[98,100,101,115]},{\"tag\":\"mate\",\"ridge\":388,\"a\":75,\"owners\":[94,100,101,113]},{\"tag\":\"mate\",\"ridge\":388,\"a\":77,\"owners\":[94,98,101,115]},{\"tag\":\"mate\",\"ridge\":388,\"a\":78,\"owners\":[94,98,100,113]},{\"tag\":\"mate\",\"ridge\":552,\"a\":20,\"owners\":[103,105,110,112,116]},{\"tag\":\"mate\",\"ridge\":552,\"a\":49,\"owners\":[110,112,116]},{\"tag\":\"mate\",\"ridge\":552,\"a\":67,\"owners\":[103,105,116]},{\"tag\":\"mate\",\"ridge\":552,\"a\":80,\"owners\":[105,112]},{\"tag\":\"mate\",\"ridge\":608,\"a\":23,\"owners\":[105,107,112,114,116]},{\"tag\":\"mate\",\"ridge\":608,\"a\":58,\"owners\":[112,114,116]},{\"tag\":\"mate\",\"ridge\":608,\"a\":76,\"owners\":[105,107,116]},{\"tag\":\"mate\",\"ridge\":608,\"a\":83,\"owners\":[107,114]},{\"tag\":\"mate\",\"ridge\":608,\"a\":85,\"owners\":[105,112]},{\"tag\":\"mate\",\"ridge\":608,\"a\":87,\"owners\":[105,107,112,114,116]},{\"tag\":\"mate\",\"ridge\":270,\"a\":32,\"owners\":[93,94]},{\"tag\":\"mate\",\"ridge\":270,\"a\":94,\"owners\":[32,93]},{\"tag\":\"mate\",\"ridge\":278,\"a\":97,\"owners\":[36,98]},{\"tag\":\"mate\",\"ridge\":278,\"a\":98,\"owners\":[36,97]},{\"tag\":\"mate\",\"ridge\":166,\"a\":38,\"owners\":[92,100]},{\"tag\":\"mate\",\"ridge\":166,\"a\":100,\"owners\":[38,92]},{\"tag\":\"mate\",\"ridge\":198,\"a\":96,\"owners\":[40,101]},{\"tag\":\"mate\",\"ridge\":198,\"a\":101,\"owners\":[40,96]},{\"tag\":\"mate\",\"ridge\":424,\"a\":84,\"owners\":[106,113]},{\"tag\":\"mate\",\"ridge\":424,\"a\":106,\"owners\":[84,113]},{\"tag\":\"mate\",\"ridge\":424,\"a\":113,\"owners\":[84,106]},{\"tag\":\"mate\",\"ridge\":464,\"a\":86,\"owners\":[108,115]},{\"tag\":\"mate\",\"ridge\":464,\"a\":108,\"owners\":[86,115]},{\"tag\":\"mate\",\"ridge\":464,\"a\":115,\"owners\":[86,108]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[32,38,84],\"full_literals\":[-49,5,7,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":32,\"full_literals\":[-5,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":38,\"full_literals\":[-7,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":84,\"full_literals\":[-26,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":36,\"full_literals\":[-6,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":40,\"full_literals\":[-8,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":86,\"full_literals\":[-28,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":92,\"full_literals\":[-30,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":93,\"full_literals\":[-31,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":106,\"full_literals\":[-40,51]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[96,97,108],\"full_literals\":[-52,33,34,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":96,\"full_literals\":[-33,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":97,\"full_literals\":[-34,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":108,\"full_literals\":[-42,52]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[94,100,113],\"full_literals\":[-53,32,36,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":94,\"full_literals\":[-32,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":100,\"full_literals\":[-36,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":113,\"full_literals\":[-45,53]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[98,101,115],\"full_literals\":[-54,35,37,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":98,\"full_literals\":[-35,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":101,\"full_literals\":[-37,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":115,\"full_literals\":[-47,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":53,\"full_literals\":[-12,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":71,\"full_literals\":[-19,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":105,\"full_literals\":[-39,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":112,\"full_literals\":[-44,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":116,\"full_literals\":[-48,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":103,\"full_literals\":[-38,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":110,\"full_literals\":[-43,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":107,\"full_literals\":[-41,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":114,\"full_literals\":[-46,58]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,49,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,53,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,52,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,60,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-63,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[20,23,49,53,58,67,71,76,80,83,85,87,103,105,107,110,112,114,116]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[8,17,42,51,57,59,60,69,75,77,78,84,86,94,98,100,101,106,108,113,115]}]}"
  "p cnf 72 100\n-1 2 18 20 22 23 26 28 0\n-13 2 18 22 23 26 0\n-16 2 18 20 22 26 0\n-1 32 35 36 37 40 42 0\n-11 35 36 37 42 0\n-13 32 36 37 40 0\n-15 32 35 37 42 0\n-16 32 35 36 40 0\n-2 32 35 36 37 45 47 0\n-9 45 47 0\n-18 35 36 37 47 0\n-20 32 36 37 45 0\n-22 32 35 37 47 0\n-23 32 35 36 45 0\n-3 38 39 43 44 48 0\n-10 43 44 48 0\n-17 38 39 48 0\n-24 39 44 0\n-4 39 41 44 46 48 0\n-14 44 46 48 0\n-21 39 41 48 0\n-25 41 46 0\n-27 39 44 0\n-29 39 41 44 46 48 0\n-5 31 32 0\n-32 5 31 0\n-34 6 35 0\n-35 6 34 0\n-7 30 36 0\n-36 7 30 0\n-33 8 37 0\n-37 8 33 0\n-26 40 45 0\n-40 26 45 0\n-45 26 40 0\n-28 42 47 0\n-42 28 47 0\n-47 28 42 0\n-49 5 7 26 0\n-5 49 0\n-7 49 0\n-26 49 0\n-6 50 0\n-8 50 0\n-28 50 0\n-30 51 0\n-31 51 0\n-40 51 0\n-52 33 34 42 0\n-33 52 0\n-34 52 0\n-42 52 0\n-53 32 36 45 0\n-32 53 0\n-36 53 0\n-45 53 0\n-54 35 37 47 0\n-35 54 0\n-37 54 0\n-47 54 0\n-12 55 0\n-19 55 0\n-39 56 0\n-44 56 0\n-48 56 0\n-38 57 0\n-43 57 0\n-41 58 0\n-46 58 0\n-51 59 0\n-50 59 0\n-60 49 59 0\n-59 60 0\n-49 60 0\n-49 -59 61 0\n-62 53 54 0\n-54 62 0\n-53 62 0\n-63 52 62 0\n-62 63 0\n-52 63 0\n-52 -62 64 0\n-65 60 63 0\n-63 65 0\n-64 66 0\n-60 65 0\n-60 -63 66 0\n-61 66 0\n-55 67 0\n-67 68 0\n-58 69 0\n-57 69 0\n-69 70 0\n-56 70 0\n-70 71 0\n-68 71 0\n-66 -71 72 0\n-72 0\n3 4 10 12 14 17 19 21 24 25 27 29 38 39 41 43 44 46 48 0\n1 2 9 11 13 15 16 18 20 22 23 26 28 32 35 36 37 40 42 45 47 0\n"
  "101 65 0 84 86 80 81 73 74 77 78 52 70 42 58 59 60 54 55 56 36 48 5 11 4 6 7 8 9 12 13 14 10 100 0\n102 59 63 0 101 80 78 56 55 54 83 70 72 46 47 48 29 25 33 39 0\n103 63 61 0 80 81 77 78 52 58 59 60 54 55 56 36 5 11 7 9 12 13 14 10 102 75 42 34 2 3 1 100 0\n104 62 66 0 88 103 87 73 71 45 44 43 77 79 58 59 60 27 31 37 49 0\n105 66 0 85 88 103 87 73 74 70 71 40 41 42 46 47 48 43 44 45 30 26 35 53 104 76 82 50 51 52 32 28 38 57 0\n106 -71 0 105 98 97 0\n107 -70 0 106 95 0\n108 -68 0 106 96 0\n109 -69 0 107 93 0\n110 -56 0 107 94 0\n111 -67 0 108 90 0\n112 -58 0 109 91 0\n113 -57 0 109 92 0\n114 -39 0 110 63 0\n115 -44 0 110 64 0\n116 -48 0 110 65 0\n117 -55 0 111 89 0\n118 -41 0 112 68 0\n119 -46 0 112 69 0\n120 -38 0 113 66 0\n121 -43 0 113 67 0\n122 -24 0 114 115 18 0\n123 -27 0 114 115 23 0\n124 -12 0 117 61 0\n125 -19 0 117 62 0\n126 -25 0 118 119 22 0\n127 -4 0 118 114 115 119 116 19 0\n128 -21 0 118 114 116 21 0\n129 -29 0 118 114 115 119 116 24 0\n130 -14 0 119 115 116 20 0\n131 -3 0 120 114 121 115 116 15 0\n132 -17 0 120 114 116 17 0\n133 -10 0 121 115 116 16 0\n134 0 127 131 133 124 130 132 125 128 122 126 123 129 120 114 118 121 115 119 116 99 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record006
