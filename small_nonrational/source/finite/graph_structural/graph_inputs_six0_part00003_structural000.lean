module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsSix0Part00003Frames
public import GraphInputsSix0Part00003Leaves
public import GraphInputsSix0Part00003Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00003.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2769ce5b8fa1f7a5cb6e5ab63d735aced3acdb2f49ff43c8e52d4cd38cb31ac4f332b293a1eac695a36a3a4e3385e0fbc1e4751b45d1725a9565391e785b15a5c56956565535535634cd4b4ad4745d0f6c3c4e534cc7332d2b1ad1b16c3ba1e4731e1715c8f13c1f94a160d82e4c589325290d48d0b4530cc4b0ac2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "49249249249246db6db6db6d26db4db6d269b6db6da4926d369249349b692489249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 35), (facetIndex 74)]))
 (.branch 2
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 53), (facetIndex 55), (facetIndex 72)]))
 (.leaf ([(facetIndex 64), (facetIndex 71), (facetIndex 75)]))))
 (.branch 4
 (.leaf ([(facetIndex 47), (facetIndex 49), (facetIndex 50), (facetIndex 78), (facetIndex 79)]))
 (.branch 5
 (.leaf ([(facetIndex 52), (facetIndex 76), (facetIndex 81)]))
 (.leaf ([(facetIndex 66), (facetIndex 67), (facetIndex 82)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 23), (facetIndex 25), (facetIndex 73)]))
 (.branch 8
 (.leaf ([(facetIndex 48), (facetIndex 58), (facetIndex 60)]))
 (.leaf ([(facetIndex 59), (facetIndex 62), (facetIndex 83)]))))
 (.branch 10
 (.leaf ([(facetIndex 24), (facetIndex 45), (facetIndex 65), (facetIndex 77)]))
 (.branch 11
 (.leaf ([(facetIndex 46), (facetIndex 70), (facetIndex 80)]))
 (.leaf ([(facetIndex 36), (facetIndex 51), (facetIndex 61)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "854a339420612a00559208b787001014b3373a900000110b0000000000696z17;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3, 4]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00003.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00003.record003" 66

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00003.record003" "{\"ridges\":[[12,392],[13,304],[33,304],[35,771],[36,643],[43,392],[44,304],[48,644],[49,784],[51,704],[52,644],[52,896],[54,304],[56,392],[57,385],[58,464],[59,704],[60,273],[60,784],[60,833],[61,784],[62,704],[62,833],[62,896],[67,650],[74,802],[78,780],[79,804],[81,644],[81,784],[82,840],[83,464],[83,704],[83,784],[83,896],[91,392],[92,392],[93,296],[94,385],[95,392]],\"owners\":[[93,296,[],[10,30,41,54,56,72,75,76,89,92,95]],[57,385,[47,50,52,61],[12,43,56,58,62,91,92,93,94,95]],[94,385,[47,50,52,61],[12,43,56,57,58,62,91,92,93,95]],[12,392,[76,78,82],[43,56,57,91,92,93,94,95]],[43,392,[82],[12,56,57,76,78,91,92,93,94,95]],[56,392,[78,82],[12,43,57,76,91,92,93,94,95]],[91,392,[82],[12,43,56,57,76,78,92,93,94,95]],[92,392,[78,82],[12,43,56,57,76,91,93,94,95]],[95,392,[78],[12,43,56,57,76,82,91,92,93,94]],[60,273,[13,28,33,39,44,47,54,93],[35,49,55,58,61,90]],[13,304,[72,74,75,79],[33,44,54,90,93]],[33,304,[75,79],[13,44,54,72,74,90,93]],[44,304,[72,74],[13,33,54,75,79,90,93]],[54,304,[74,79],[13,33,44,72,75,90,93]],[36,643,[25],[]],[48,644,[67,70,77,78],[25,51,52,80,81]],[52,644,[67,70,77,80],[25,48,51,78,81]],[81,644,[25,51,67,70,77],[48,52,78,80]],[35,771,[],[]],[49,784,[74,83],[35,60,61,79,81]],[60,784,[74,79,81],[35,49,61,83]],[61,784,[74,79],[35,49,60,81,83]],[81,784,[35,60,74],[49,61,79,83]],[83,784,[35,49,74,79],[60,61,81]],[51,704,[73,82,83],[36,59,62,70,77,80]],[59,704,[70,73,77,82],[36,51,62,80,83]],[62,704,[70,73,77,80],[36,51,59,82,83]],[83,704,[36,51,70,73,77],[59,62,80,82]],[52,896,[82,83],[61,62,78,81]],[62,896,[78,81],[52,61,82,83]],[83,896,[52,78],[61,62,81,82]],[58,464,[83],[]],[83,464,[58],[]],[60,833,[62],[]],[62,833,[60],[]],[67,650,[73],[]],[74,802,[],[]],[78,780,[],[]],[79,804,[],[]],[82,840,[],[]]],\"edges\":[[42,[12,43,47,50,52,56,57,58,61,62,76,78,81,82,83,91,92,93,94,95]],[43,[25,36,48,51,52,59,61,62,67,70,73,77,78,80,81,82,83]],[44,[35,49,52,60,61,62,74,78,79,81,82,83]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00003.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00003.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-15,-13],[-41],[-19,11,14,16,23],[-42,11,14,16,23],[-1,31,33,37],[-9,37],[-18,33,37],[-39,37],[-40,33,37],[-43,33],[-22,2,4,5,8,10,11,17,41],[-2,27,29,30,34],[-5,30,34],[-10,27,29],[-17,29,34],[-7,3],[-12,25,26,32,33],[-16,25,26,32,35],[-36,3,15,25,26,32],[-6],[-13,29,38],[-22,29,34,36],[-23,29,34],[-36,6,22,29],[-38,6,13,29,34],[-15,28,37,38],[-21,26,28,32,37],[-24,26,28,32,35],[-38,7,15,26,28,32],[-16,37,38],[-24,33,36],[-38,16,33],[-20,38],[-38,20],[-22,24],[-24,22],[-25,28],[-29],[-33],[-34],[-37],[-4,44],[-8,45],[-27,45],[-30,46],[-11,47],[-13,47],[-14,47],[-16,48],[-31,48],[-36,48],[-3,49],[-28,49],[-20,50],[-22,50],[-24,51],[-38,51],[-32,52],[-26,53],[-35,53],[-46,54],[-45,54],[-54,55],[-44,55],[-48,56],[-56,57],[-47,57],[-47,-56,58],[-58,59],[-55,-57,59],[-50,-51,60],[-60,61],[-49,-60,62],[-53,63],[-63,64],[-52,64],[-61,-64,65],[-62,65],[-59,-65,66],[-66],[1,9,11,14,16,18,19,20,23,24,31,33,36,37,38,39,40,41,42,43],[3,7,12,15,16,21,23,24,25,26,28,32,33,35,36,37,38],[6,13,16,22,23,24,29,33,34,36,37,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":51,\"b\":49},{\"tag\":\"mate\",\"ridge\":296,\"a\":93,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":385,\"a\":57,\"owners\":[47,50,52,61]},{\"tag\":\"mate\",\"ridge\":385,\"a\":94,\"owners\":[47,50,52,61]},{\"tag\":\"mate\",\"ridge\":392,\"a\":12,\"owners\":[76,78,82]},{\"tag\":\"mate\",\"ridge\":392,\"a\":43,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":392,\"a\":56,\"owners\":[78,82]},{\"tag\":\"mate\",\"ridge\":392,\"a\":91,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":392,\"a\":92,\"owners\":[78,82]},{\"tag\":\"mate\",\"ridge\":392,\"a\":95,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":273,\"a\":60,\"owners\":[13,28,33,39,44,47,54,93]},{\"tag\":\"mate\",\"ridge\":304,\"a\":13,\"owners\":[72,74,75,79]},{\"tag\":\"mate\",\"ridge\":304,\"a\":33,\"owners\":[75,79]},{\"tag\":\"mate\",\"ridge\":304,\"a\":44,\"owners\":[72,74]},{\"tag\":\"mate\",\"ridge\":304,\"a\":54,\"owners\":[74,79]},{\"tag\":\"mate\",\"ridge\":643,\"a\":36,\"owners\":[25]},{\"tag\":\"mate\",\"ridge\":644,\"a\":48,\"owners\":[67,70,77,78]},{\"tag\":\"mate\",\"ridge\":644,\"a\":52,\"owners\":[67,70,77,80]},{\"tag\":\"mate\",\"ridge\":644,\"a\":81,\"owners\":[25,51,67,70,77]},{\"tag\":\"mate\",\"ridge\":771,\"a\":35,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":784,\"a\":49,\"owners\":[74,83]},{\"tag\":\"mate\",\"ridge\":784,\"a\":60,\"owners\":[74,79,81]},{\"tag\":\"mate\",\"ridge\":784,\"a\":61,\"owners\":[74,79]},{\"tag\":\"mate\",\"ridge\":784,\"a\":81,\"owners\":[35,60,74]},{\"tag\":\"mate\",\"ridge\":784,\"a\":83,\"owners\":[35,49,74,79]},{\"tag\":\"mate\",\"ridge\":704,\"a\":51,\"owners\":[73,82,83]},{\"tag\":\"mate\",\"ridge\":704,\"a\":59,\"owners\":[70,73,77,82]},{\"tag\":\"mate\",\"ridge\":704,\"a\":62,\"owners\":[70,73,77,80]},{\"tag\":\"mate\",\"ridge\":704,\"a\":83,\"owners\":[36,51,70,73,77]},{\"tag\":\"mate\",\"ridge\":896,\"a\":52,\"owners\":[82,83]},{\"tag\":\"mate\",\"ridge\":896,\"a\":62,\"owners\":[78,81]},{\"tag\":\"mate\",\"ridge\":896,\"a\":83,\"owners\":[52,78]},{\"tag\":\"mate\",\"ridge\":464,\"a\":58,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":464,\"a\":83,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":833,\"a\":60,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":833,\"a\":62,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":650,\"a\":67,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":802,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":780,\"a\":78,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":804,\"a\":79,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":840,\"a\":82,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":28,\"full_literals\":[-4,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":39,\"full_literals\":[-8,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":72,\"full_literals\":[-27,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-30,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":47,\"full_literals\":[-11,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":49,\"full_literals\":[-13,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":50,\"full_literals\":[-14,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":52,\"full_literals\":[-16,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-31,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":81,\"full_literals\":[-36,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":25,\"full_literals\":[-3,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":73,\"full_literals\":[-28,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":58,\"full_literals\":[-20,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":60,\"full_literals\":[-22,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":62,\"full_literals\":[-24,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":83,\"full_literals\":[-38,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":77,\"full_literals\":[-32,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":70,\"full_literals\":[-26,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":80,\"full_literals\":[-35,53]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-56,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-58,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-51,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-49,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-59,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[12,43,47,50,52,56,57,58,61,62,76,78,81,82,83,91,92,93,94,95]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[25,36,48,51,52,59,61,62,67,70,73,77,78,80,81,82,83]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[35,49,52,60,61,62,74,78,79,81,82,83]}]}"
  "p cnf 66 83\n-15 -13 0\n-41 0\n-19 11 14 16 23 0\n-42 11 14 16 23 0\n-1 31 33 37 0\n-9 37 0\n-18 33 37 0\n-39 37 0\n-40 33 37 0\n-43 33 0\n-22 2 4 5 8 10 11 17 41 0\n-2 27 29 30 34 0\n-5 30 34 0\n-10 27 29 0\n-17 29 34 0\n-7 3 0\n-12 25 26 32 33 0\n-16 25 26 32 35 0\n-36 3 15 25 26 32 0\n-6 0\n-13 29 38 0\n-22 29 34 36 0\n-23 29 34 0\n-36 6 22 29 0\n-38 6 13 29 34 0\n-15 28 37 38 0\n-21 26 28 32 37 0\n-24 26 28 32 35 0\n-38 7 15 26 28 32 0\n-16 37 38 0\n-24 33 36 0\n-38 16 33 0\n-20 38 0\n-38 20 0\n-22 24 0\n-24 22 0\n-25 28 0\n-29 0\n-33 0\n-34 0\n-37 0\n-4 44 0\n-8 45 0\n-27 45 0\n-30 46 0\n-11 47 0\n-13 47 0\n-14 47 0\n-16 48 0\n-31 48 0\n-36 48 0\n-3 49 0\n-28 49 0\n-20 50 0\n-22 50 0\n-24 51 0\n-38 51 0\n-32 52 0\n-26 53 0\n-35 53 0\n-46 54 0\n-45 54 0\n-54 55 0\n-44 55 0\n-48 56 0\n-56 57 0\n-47 57 0\n-47 -56 58 0\n-58 59 0\n-55 -57 59 0\n-50 -51 60 0\n-60 61 0\n-49 -60 62 0\n-53 63 0\n-63 64 0\n-52 64 0\n-61 -64 65 0\n-62 65 0\n-59 -65 66 0\n-66 0\n1 9 11 14 16 18 19 20 23 24 31 33 36 37 38 39 40 41 42 43 0\n3 7 12 15 16 21 23 24 25 26 28 32 33 35 36 37 38 0\n6 13 16 22 23 24 29 33 34 36 37 38 0\n"
  "84 -22 2 4 5 8 10 11 17 0 2 11 0\n85 -36 22 29 0 20 24 0\n86 -38 13 29 34 0 20 25 0\n87 -43 0 39 10 0\n88 -17 0 40 38 15 0\n89 -23 0 40 38 23 0\n90 -9 0 41 6 0\n91 -39 0 41 8 0\n92 -18 0 41 39 7 0\n93 -40 0 41 39 9 0\n94 1 11 14 16 19 20 24 31 36 38 42 0 90 92 89 39 41 91 93 2 87 81 0\n95 3 7 12 15 16 21 24 25 26 28 32 35 36 38 0 89 39 41 82 0\n96 13 16 22 24 36 38 0 20 89 38 39 40 41 83 0\n97 57 0 89 40 38 41 39 66 67 65 46 47 48 49 50 51 3 4 86 5 31 33 94 0\n98 -15 28 0 41 40 38 1 26 86 0\n99 -38 60 0 34 57 54 71 0\n100 22 38 0 41 38 30 21 85 36 96 0\n101 60 0 99 100 35 55 56 71 0\n102 61 0 101 72 0\n103 -22 59 0 97 88 40 38 70 63 62 44 14 61 45 12 13 43 64 42 69 84 22 46 51 68 65 0\n104 59 0 40 38 39 69 103 100 86 32 47 49 68 65 0\n105 -65 0 104 80 79 0\n106 -62 0 105 78 0\n107 -64 0 105 102 77 0\n108 -49 0 106 101 73 0\n109 -63 0 107 75 0\n110 -52 0 107 76 0\n111 -3 0 108 52 0\n112 -28 0 108 53 0\n113 -53 0 109 74 0\n114 -32 0 110 58 0\n115 -7 0 111 16 0\n116 -25 0 112 37 0\n117 -15 0 112 98 0\n118 -26 0 113 59 0\n119 -35 0 113 60 0\n120 -21 0 118 112 114 41 27 0\n121 -24 0 118 112 114 119 28 0\n122 -12 0 118 116 114 39 17 0\n123 -16 0 118 116 114 119 18 0\n124 -36 0 118 111 116 117 114 19 0\n125 -38 0 118 115 117 112 114 29 0\n126 0 118 120 111 115 117 123 121 122 116 112 114 119 124 125 95 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003 Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00003.record003
