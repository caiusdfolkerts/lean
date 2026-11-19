module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00068Frames
public import GraphInputsRow29Part00068Leaves
public import GraphInputsRow29Part00068Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1d46d32c4f3a26c8ea368bac99a639996359362da2e1b83ee85d16c7293a719365392e5c5c95a539595554d54d4b5c362d4b46d4743de0f23a8da338f1364d332ce4b32cab1ae1b26c3bc1d8731e2749ca719d1725c3783c5c34a2a168561382e07b21685913462916525454551342d074c388ca324c5382c4b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db4db6d36924926d36d26924da4926924d34924926d2492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 75), (facetIndex 79)]))
 (.leaf ([(facetIndex 94), (facetIndex 96)])))
 (.branch 3
 (.leaf ([(facetIndex 65), (facetIndex 76), (facetIndex 78)]))
 (.leaf ([(facetIndex 99), (facetIndex 100)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 42), (facetIndex 66), (facetIndex 71), (facetIndex 74)]))
 (.leaf ([(facetIndex 87), (facetIndex 90), (facetIndex 91), (facetIndex 102)])))
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 52), (facetIndex 54), (facetIndex 59), (facetIndex 92)]))
 (.branch 8
 (.leaf ([(facetIndex 88), (facetIndex 93), (facetIndex 98)]))
 (.leaf ([(facetIndex 97), (facetIndex 101)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5833781017655075000000002020400400004200000600006060000000064z2a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
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
def grouped3_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8]
def grouped3_0016 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record002" 72

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record002" "{\"ridges\":[[10,162],[17,273],[17,276],[22,400],[23,416],[24,769],[24,800],[36,276],[42,390],[48,162],[51,162],[52,306],[53,400],[54,786],[55,162],[56,162],[56,416],[57,162],[58,800],[59,898],[61,273],[67,276],[69,273],[69,276],[70,400],[72,416],[73,769],[73,800],[74,452],[78,792],[80,769],[80,800],[81,400],[82,400],[83,416],[83,769],[83,800],[90,390],[92,390],[97,306],[98,898],[101,180],[102,452]],\"owners\":[[10,162,[87,91,92,94,96,97,98],[38,48,51,55,56,57]],[48,162,[87,91,92,97,98],[10,38,51,55,56,57,94,96]],[51,162,[91,92,96,98],[10,38,48,55,56,57,87,94,97]],[55,162,[87,92,94,97,98],[10,38,48,51,56,57,91,96]],[56,162,[87,91,94,96],[10,38,48,51,55,57,92,97,98]],[57,162,[87,91,92,94,96,97],[10,38,48,51,55,56,98]],[17,273,[22,52,53,54,76,78,81,82],[36,61,67,69]],[61,273,[22,52,53,54,81,82],[17,36,67,69,76,78]],[69,273,[22,52,53,54,76,78,81],[17,36,61,67,82]],[17,276,[88,90,99,101,102],[36,61,67,69,70]],[36,276,[99,101,102],[17,61,67,69,70,88,90]],[67,276,[90,102],[17,36,61,69,70,88,99,101]],[69,276,[88,90,99,101],[17,36,61,67,70,102]],[22,400,[90,97,101,102],[53,70,81,82]],[53,400,[101,102],[22,70,81,82,90,97]],[70,400,[97],[22,53,81,82,90,101,102]],[81,400,[90,102],[22,53,70,82,97,101]],[82,400,[90,97,101],[22,53,70,81,102]],[23,416,[92,97,98,101],[56,72,81,83]],[56,416,[101],[23,72,81,83,92,97,98]],[72,416,[97,98],[23,56,81,83,92,101]],[83,416,[92,97,101],[23,56,72,81,98]],[24,769,[43,54,59,65,78],[58,73,80,83]],[73,769,[54,59,78],[24,43,58,65,80,83]],[80,769,[43,54,59],[24,58,65,73,78,83]],[83,769,[43,54,65,78],[24,58,59,73,80]],[24,800,[93,98,100],[58,73,80,83]],[58,800,[100],[24,73,80,83,93,98]],[73,800,[98],[24,58,80,83,93,100]],[80,800,[93,98],[24,58,73,83,100]],[83,800,[93,100],[24,58,73,80,98]],[42,390,[90,92],[]],[90,390,[42,92],[]],[92,390,[42,90],[]],[52,306,[88,97],[]],[97,306,[52,88],[]],[54,786,[],[]],[59,898,[98],[]],[98,898,[59],[]],[101,180,[66,87],[]],[74,452,[102],[]],[102,452,[74],[]],[78,792,[],[]]],\"edges\":[[33,[17,22,36,52,53,54,61,67,69,70,76,78,81,82,88,90,97,99,101,102]],[36,[10,23,38,48,51,55,56,57,66,71,72,75,79,81,83,87,91,92,94,96,97,98,101]],[42,[22,23,42,53,56,59,70,72,74,81,82,83,90,92,97,98,101,102]],[44,[24,43,54,58,59,65,73,78,80,83,93,98,100]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-35,-29],[-39,-8],[-40,-9],[-40,-19],[-43,-40],[-46,-9],[-46,-19],[-46,-43],[-47,-12],[-47,-39],[-47,-40],[-47,-46],[-51,-7],[-51,-22],[-51,-26],[-51,-27],[-51,-38],[-51,-41],[-51,-42],[-1,38,41,42,44,45,46,47],[-10,38,41,42,46,47],[-11,41,42,45,47],[-15,38,42,44,46,47],[-16,38,41,44,45],[-17,38,41,42,44,45,46],[-2,3,12,13,14,31,32,35,36],[-20,3,12,13,14,35,36],[-24,3,12,13,14,31,32,35],[-2,39,40,48,50,51],[-6,48,50,51],[-23,40,51],[-24,39,40,48,50],[-3,40,46,50,51],[-13,50,51],[-25,46],[-35,40,51],[-36,40,46,50],[-4,42,46,47,50],[-16,50],[-27,46,47],[-37,42,46,50],[-5,9,14,19,21,32],[-28,14,19,32],[-34,9,14,19],[-37,9,14,21,32],[-5,43,47,49],[-18,49],[-28,47],[-34,43,47],[-37,43,49],[-8,40,42],[-40,8,42],[-42,8,40],[-12,39,46],[-46,12,39],[-14],[-19,47],[-47,19],[-50,22,38],[-29,51],[-51,29],[-32],[-30,52],[-33,52],[-44,53],[-45,53],[-21,54],[-31,54],[-48,55],[-49,55],[-8,56],[-22,56],[-29,56],[-38,57],[-40,57],[-41,57],[-51,57],[-9,58],[-12,58],[-19,58],[-42,58],[-39,59],[-43,59],[-47,59],[-46,60],[-50,60],[-53,61],[-52,61],[-55,62],[-54,62],[-62,63],[-61,63],[-57,64],[-56,64],[-56,-57,65],[-60,66],[-59,66],[-59,-60,67],[-66,68],[-67,69],[-58,68],[-58,-66,69],[-69,70],[-64,-68,70],[-64,-69,71],[-65,70],[-65,-68,71],[-71,72],[-63,-70,72],[-72],[2,3,6,12,13,14,20,23,24,25,31,32,35,36,39,40,46,48,50,51],[1,4,7,10,11,15,16,17,22,26,27,30,33,35,37,38,41,42,44,45,46,47,50],[3,4,8,13,16,19,25,27,29,35,36,37,40,42,46,47,50,51],[5,9,14,18,19,21,28,32,34,37,43,47,49]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":81,\"b\":74},{\"tag\":\"incompatible\",\"a\":88,\"b\":42},{\"tag\":\"incompatible\",\"a\":90,\"b\":43},{\"tag\":\"incompatible\",\"a\":90,\"b\":59},{\"tag\":\"incompatible\",\"a\":93,\"b\":90},{\"tag\":\"incompatible\",\"a\":97,\"b\":43},{\"tag\":\"incompatible\",\"a\":97,\"b\":59},{\"tag\":\"incompatible\",\"a\":97,\"b\":93},{\"tag\":\"incompatible\",\"a\":98,\"b\":52},{\"tag\":\"incompatible\",\"a\":98,\"b\":88},{\"tag\":\"incompatible\",\"a\":98,\"b\":90},{\"tag\":\"incompatible\",\"a\":98,\"b\":97},{\"tag\":\"incompatible\",\"a\":102,\"b\":38},{\"tag\":\"incompatible\",\"a\":102,\"b\":66},{\"tag\":\"incompatible\",\"a\":102,\"b\":71},{\"tag\":\"incompatible\",\"a\":102,\"b\":72},{\"tag\":\"incompatible\",\"a\":102,\"b\":87},{\"tag\":\"incompatible\",\"a\":102,\"b\":91},{\"tag\":\"incompatible\",\"a\":102,\"b\":92},{\"tag\":\"mate\",\"ridge\":162,\"a\":10,\"owners\":[87,91,92,94,96,97,98]},{\"tag\":\"mate\",\"ridge\":162,\"a\":48,\"owners\":[87,91,92,97,98]},{\"tag\":\"mate\",\"ridge\":162,\"a\":51,\"owners\":[91,92,96,98]},{\"tag\":\"mate\",\"ridge\":162,\"a\":55,\"owners\":[87,92,94,97,98]},{\"tag\":\"mate\",\"ridge\":162,\"a\":56,\"owners\":[87,91,94,96]},{\"tag\":\"mate\",\"ridge\":162,\"a\":57,\"owners\":[87,91,92,94,96,97]},{\"tag\":\"mate\",\"ridge\":273,\"a\":17,\"owners\":[22,52,53,54,76,78,81,82]},{\"tag\":\"mate\",\"ridge\":273,\"a\":61,\"owners\":[22,52,53,54,81,82]},{\"tag\":\"mate\",\"ridge\":273,\"a\":69,\"owners\":[22,52,53,54,76,78,81]},{\"tag\":\"mate\",\"ridge\":276,\"a\":17,\"owners\":[88,90,99,101,102]},{\"tag\":\"mate\",\"ridge\":276,\"a\":36,\"owners\":[99,101,102]},{\"tag\":\"mate\",\"ridge\":276,\"a\":67,\"owners\":[90,102]},{\"tag\":\"mate\",\"ridge\":276,\"a\":69,\"owners\":[88,90,99,101]},{\"tag\":\"mate\",\"ridge\":400,\"a\":22,\"owners\":[90,97,101,102]},{\"tag\":\"mate\",\"ridge\":400,\"a\":53,\"owners\":[101,102]},{\"tag\":\"mate\",\"ridge\":400,\"a\":70,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":400,\"a\":81,\"owners\":[90,102]},{\"tag\":\"mate\",\"ridge\":400,\"a\":82,\"owners\":[90,97,101]},{\"tag\":\"mate\",\"ridge\":416,\"a\":23,\"owners\":[92,97,98,101]},{\"tag\":\"mate\",\"ridge\":416,\"a\":56,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":416,\"a\":72,\"owners\":[97,98]},{\"tag\":\"mate\",\"ridge\":416,\"a\":83,\"owners\":[92,97,101]},{\"tag\":\"mate\",\"ridge\":769,\"a\":24,\"owners\":[43,54,59,65,78]},{\"tag\":\"mate\",\"ridge\":769,\"a\":73,\"owners\":[54,59,78]},{\"tag\":\"mate\",\"ridge\":769,\"a\":80,\"owners\":[43,54,59]},{\"tag\":\"mate\",\"ridge\":769,\"a\":83,\"owners\":[43,54,65,78]},{\"tag\":\"mate\",\"ridge\":800,\"a\":24,\"owners\":[93,98,100]},{\"tag\":\"mate\",\"ridge\":800,\"a\":58,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":800,\"a\":73,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":800,\"a\":80,\"owners\":[93,98]},{\"tag\":\"mate\",\"ridge\":800,\"a\":83,\"owners\":[93,100]},{\"tag\":\"mate\",\"ridge\":390,\"a\":42,\"owners\":[90,92]},{\"tag\":\"mate\",\"ridge\":390,\"a\":90,\"owners\":[42,92]},{\"tag\":\"mate\",\"ridge\":390,\"a\":92,\"owners\":[42,90]},{\"tag\":\"mate\",\"ridge\":306,\"a\":52,\"owners\":[88,97]},{\"tag\":\"mate\",\"ridge\":306,\"a\":97,\"owners\":[52,88]},{\"tag\":\"mate\",\"ridge\":786,\"a\":54,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":898,\"a\":59,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":898,\"a\":98,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":180,\"a\":101,\"owners\":[66,87]},{\"tag\":\"mate\",\"ridge\":452,\"a\":74,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":452,\"a\":102,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":792,\"a\":78,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":75,\"full_literals\":[-30,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":79,\"full_literals\":[-33,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":94,\"full_literals\":[-44,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":96,\"full_literals\":[-45,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-21,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":76,\"full_literals\":[-31,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":99,\"full_literals\":[-48,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":100,\"full_literals\":[-49,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":42,\"full_literals\":[-8,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":66,\"full_literals\":[-22,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-29,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-38,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":90,\"full_literals\":[-40,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":91,\"full_literals\":[-41,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":102,\"full_literals\":[-51,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":43,\"full_literals\":[-9,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":52,\"full_literals\":[-12,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":59,\"full_literals\":[-19,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":92,\"full_literals\":[-42,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":88,\"full_literals\":[-39,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":93,\"full_literals\":[-43,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":98,\"full_literals\":[-47,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":97,\"full_literals\":[-46,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":101,\"full_literals\":[-50,60]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-57,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-60,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-66,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-68,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-64,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-68,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-63,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[17,22,36,52,53,54,61,67,69,70,76,78,81,82,88,90,97,99,101,102]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[10,23,38,48,51,55,56,57,66,71,72,75,79,81,83,87,91,92,94,96,97,98,101]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[22,23,42,53,56,59,70,72,74,81,82,83,90,92,97,98,101,102]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[24,43,54,58,59,65,73,78,80,83,93,98,100]}]}"
  "p cnf 72 114\n-35 -29 0\n-39 -8 0\n-40 -9 0\n-40 -19 0\n-43 -40 0\n-46 -9 0\n-46 -19 0\n-46 -43 0\n-47 -12 0\n-47 -39 0\n-47 -40 0\n-47 -46 0\n-51 -7 0\n-51 -22 0\n-51 -26 0\n-51 -27 0\n-51 -38 0\n-51 -41 0\n-51 -42 0\n-1 38 41 42 44 45 46 47 0\n-10 38 41 42 46 47 0\n-11 41 42 45 47 0\n-15 38 42 44 46 47 0\n-16 38 41 44 45 0\n-17 38 41 42 44 45 46 0\n-2 3 12 13 14 31 32 35 36 0\n-20 3 12 13 14 35 36 0\n-24 3 12 13 14 31 32 35 0\n-2 39 40 48 50 51 0\n-6 48 50 51 0\n-23 40 51 0\n-24 39 40 48 50 0\n-3 40 46 50 51 0\n-13 50 51 0\n-25 46 0\n-35 40 51 0\n-36 40 46 50 0\n-4 42 46 47 50 0\n-16 50 0\n-27 46 47 0\n-37 42 46 50 0\n-5 9 14 19 21 32 0\n-28 14 19 32 0\n-34 9 14 19 0\n-37 9 14 21 32 0\n-5 43 47 49 0\n-18 49 0\n-28 47 0\n-34 43 47 0\n-37 43 49 0\n-8 40 42 0\n-40 8 42 0\n-42 8 40 0\n-12 39 46 0\n-46 12 39 0\n-14 0\n-19 47 0\n-47 19 0\n-50 22 38 0\n-29 51 0\n-51 29 0\n-32 0\n-30 52 0\n-33 52 0\n-44 53 0\n-45 53 0\n-21 54 0\n-31 54 0\n-48 55 0\n-49 55 0\n-8 56 0\n-22 56 0\n-29 56 0\n-38 57 0\n-40 57 0\n-41 57 0\n-51 57 0\n-9 58 0\n-12 58 0\n-19 58 0\n-42 58 0\n-39 59 0\n-43 59 0\n-47 59 0\n-46 60 0\n-50 60 0\n-53 61 0\n-52 61 0\n-55 62 0\n-54 62 0\n-62 63 0\n-61 63 0\n-57 64 0\n-56 64 0\n-56 -57 65 0\n-60 66 0\n-59 66 0\n-59 -60 67 0\n-66 68 0\n-67 69 0\n-58 68 0\n-58 -66 69 0\n-69 70 0\n-64 -68 70 0\n-64 -69 71 0\n-65 70 0\n-65 -68 71 0\n-71 72 0\n-63 -70 72 0\n-72 0\n2 3 6 12 13 14 20 23 24 25 31 32 35 36 39 40 46 48 50 51 0\n1 4 7 10 11 15 16 17 22 26 27 30 33 35 37 38 41 42 44 45 46 47 50 0\n3 4 8 13 16 19 25 27 29 35 36 37 40 42 46 47 50 51 0\n5 9 14 18 19 21 28 32 34 37 43 47 49 0\n"
  "115 -71 0 110 108 0\n116 2 3 6 12 13 20 23 24 25 31 35 36 39 40 46 48 50 51 0 56 62 111 0\n117 5 9 18 19 21 28 34 37 43 47 49 0 56 62 114 0\n118 -46 62 0 62 56 89 70 47 90 67 6 7 8 12 45 43 44 42 117 0\n119 47 50 16 29 8 51 40 46 0 53 41 37 33 34 36 35 57 40 38 113 0\n120 12 51 2 6 13 3 23 24 25 31 35 36 39 40 46 48 50 0 56 116 27 0\n121 64 63 0 62 56 91 118 35 92 87 66 65 90 68 89 69 93 94 74 75 76 77 71 72 73 24 59 31 36 34 30 33 37 119 9 10 26 28 120 0\n122 39 40 51 50 62 0 118 37 33 36 31 89 69 30 34 35 90 68 29 32 54 120 0\n123 40 51 50 62 0 60 39 118 122 2 10 119 0\n124 -40 62 0 62 56 89 70 47 90 67 3 4 5 11 45 44 42 43 117 0\n125 50 63 0 115 91 124 118 92 88 64 63 87 66 65 39 123 13 14 15 16 17 18 19 61 77 41 25 1 73 95 107 99 97 84 22 38 20 21 23 112 0\n126 63 0 115 91 89 90 70 67 47 121 105 100 125 86 96 98 102 83 84 78 80 50 49 46 48 117 0\n127 -70 0 126 110 109 0\n128 -69 0 127 103 0\n129 -65 0 127 106 0\n130 -67 0 128 100 0\n131 -50 0 127 86 96 99 104 93 94 74 72 59 0\n132 -16 0 131 39 0\n133 -8 40 0 127 51 71 81 94 101 104 0\n134 -46 0 130 128 85 96 98 102 82 79 55 0\n135 -47 0 128 58 84 80 97 102 0\n136 40 51 0 135 132 131 134 60 133 119 0\n137 -40 0 129 127 75 93 95 104 71 101 52 81 0\n138 51 0 137 136 0\n139 29 0 138 61 0\n140 57 0 138 77 0\n141 56 0 139 73 0\n142 0 141 140 129 95 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "6e0f8e91d4cd1b46b19c3713c2f3326a8ea4e87a71b2669b1655a364d98e33a2e4b8ae4783ee87316c4f13a4d92e479e1725a95a5c5595356354d4b58b4ad2743dc8da338f138cd331cccb8acab1af0761e4731e2749ca785d170de0f23c2f3305cc89321683ac19161584e078c92a4590e4c51548d1341d88c530cc4b0ac1b81c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6d369b49a6934d36d26db4926db6d36da4936d249249a49b492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 36), (facetIndex 41), (facetIndex 51), (facetIndex 82), (facetIndex 89)]))
 (.leaf ([(facetIndex 72), (facetIndex 92)])))
 (.branch 3
 (.leaf ([(facetIndex 58), (facetIndex 62), (facetIndex 98), (facetIndex 102), (facetIndex 104)]))
 (.leaf ([(facetIndex 37), (facetIndex 50), (facetIndex 52), (facetIndex 67), (facetIndex 73)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 59), (facetIndex 63), (facetIndex 75)]))
 (.leaf ([(facetIndex 60), (facetIndex 64), (facetIndex 74)])))
 (.branch 7
 (.leaf ([(facetIndex 57), (facetIndex 65), (facetIndex 66), (facetIndex 78), (facetIndex 79), (facetIndex 84), (facetIndex 95)]))
 (.branch 8
 (.leaf ([(facetIndex 80), (facetIndex 87), (facetIndex 96), (facetIndex 100), (facetIndex 101), (facetIndex 103)]))
 (.leaf ([(facetIndex 93), (facetIndex 99), (facetIndex 105)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "827277820760810000700600076600453100003665420542600003030000000000003z25;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
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
def grouped3_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8]
def grouped3_0016 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record005" 51

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record005" "{\"ridges\":[[3,517],[9,545],[32,517],[35,517],[38,545],[40,517],[41,387],[42,517],[45,545],[49,545],[50,785],[52,416],[53,545],[62,388],[64,388],[64,416],[67,897],[73,416],[75,416],[75,897],[82,394],[87,388],[89,450],[93,394],[98,408],[99,388],[100,388],[102,464],[103,388],[105,408]],\"owners\":[[3,517,[57,60,63,65,66,67],[32,35,38,40,42]],[32,517,[60,63,65,66,67],[3,35,38,40,42,57]],[35,517,[57,65,66,67],[3,32,38,40,42,60,63]],[40,517,[57,60,63,65,66,67],[3,32,35,38,42]],[42,517,[57,60,65],[3,32,35,38,40,63,66,67]],[9,545,[57,60,65,66,74,75],[38,45,49,53]],[38,545,[74,75],[9,45,49,53,57,60,65,66]],[45,545,[60,65,66,74,75],[9,38,49,53,57]],[49,545,[57,65,66,75],[9,38,45,53,60,74]],[53,545,[57,60,65],[9,38,45,49,66,74,75]],[41,387,[52],[]],[62,388,[82,87,89,99,103],[41,64,67,98,100,102]],[64,388,[82,89,98,102],[41,62,67,87,99,100,103]],[87,388,[62,67,98,102],[41,64,82,89,99,100,103]],[99,388,[41,62,67,89,102],[64,82,87,98,100,103]],[100,388,[41,67,82,89],[62,64,87,98,99,102,103]],[103,388,[41,62,82,89,98,102],[64,67,87,99,100]],[50,785,[63,74],[]],[52,416,[99,100,103,105],[64,73,75,87,93]],[64,416,[93,105],[52,73,75,87,99,100,103]],[73,416,[87,93,99,103],[52,64,75,100,105]],[75,416,[87,93,99,100,105],[52,64,73,103]],[67,897,[75],[]],[75,897,[67],[]],[82,394,[93],[]],[93,394,[82],[]],[89,450,[],[]],[98,408,[105],[]],[105,408,[98],[]],[102,464,[],[]]],\"edges\":[[8,[3,9,32,35,38,40,42,45,49,50,53,57,60,63,65,66,67,74,75]],[42,[41,52,62,64,67,73,75,82,87,89,93,98,99,100,102,103,105]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,14,15,17,19,20,21],[-3,15,17,19,20,21],[-4,14,19,20,21],[-6,14,15,17,19,20,21],[-8,14,15,19],[-2,14,15,19,20,23,24],[-5,23,24],[-9,15,19,20,23,24],[-10,14,19,20,24],[-13,14,15,19],[-7,12],[-16,25,26,27,30,33],[-18,25,27,29,32],[-26,16,21,29,32],[-30,7,16,21,27,32],[-31,7,21,25,27],[-33,7,16,25,27,29,32],[-11,17,23],[-12,30,31,33,34],[-18,28,34],[-22,26,28,30,33],[-24,26,28,30,31,34],[-21,24],[-24,21],[-25,28],[-28,25],[-27],[-29,34],[-34,29],[-32],[-7,35],[-25,35],[-16,36],[-29,36],[-12,37],[-21,37],[-22,37],[-17,38],[-24,38],[-15,39],[-18,39],[-23,39],[-14,40],[-19,40],[-20,40],[-26,41],[-31,41],[-33,41],[-28,42],[-30,42],[-34,42],[-35,43],[-37,44],[-36,44],[-44,45],[-43,45],[-39,46],[-38,46],[-42,47],[-41,47],[-47,48],[-40,-47,49],[-49,50],[-46,-48,50],[-45,-50,51],[-51],[1,2,3,4,5,6,8,9,10,11,13,14,15,17,19,20,21,23,24],[7,12,16,18,21,22,24,25,26,27,28,29,30,31,32,33,34]],\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":517,\"a\":3,\"owners\":[57,60,63,65,66,67]},{\"tag\":\"mate\",\"ridge\":517,\"a\":32,\"owners\":[60,63,65,66,67]},{\"tag\":\"mate\",\"ridge\":517,\"a\":35,\"owners\":[57,65,66,67]},{\"tag\":\"mate\",\"ridge\":517,\"a\":40,\"owners\":[57,60,63,65,66,67]},{\"tag\":\"mate\",\"ridge\":517,\"a\":42,\"owners\":[57,60,65]},{\"tag\":\"mate\",\"ridge\":545,\"a\":9,\"owners\":[57,60,65,66,74,75]},{\"tag\":\"mate\",\"ridge\":545,\"a\":38,\"owners\":[74,75]},{\"tag\":\"mate\",\"ridge\":545,\"a\":45,\"owners\":[60,65,66,74,75]},{\"tag\":\"mate\",\"ridge\":545,\"a\":49,\"owners\":[57,65,66,75]},{\"tag\":\"mate\",\"ridge\":545,\"a\":53,\"owners\":[57,60,65]},{\"tag\":\"mate\",\"ridge\":387,\"a\":41,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":388,\"a\":62,\"owners\":[82,87,89,99,103]},{\"tag\":\"mate\",\"ridge\":388,\"a\":64,\"owners\":[82,89,98,102]},{\"tag\":\"mate\",\"ridge\":388,\"a\":87,\"owners\":[62,67,98,102]},{\"tag\":\"mate\",\"ridge\":388,\"a\":99,\"owners\":[41,62,67,89,102]},{\"tag\":\"mate\",\"ridge\":388,\"a\":100,\"owners\":[41,67,82,89]},{\"tag\":\"mate\",\"ridge\":388,\"a\":103,\"owners\":[41,62,82,89,98,102]},{\"tag\":\"mate\",\"ridge\":785,\"a\":50,\"owners\":[63,74]},{\"tag\":\"mate\",\"ridge\":416,\"a\":52,\"owners\":[99,100,103,105]},{\"tag\":\"mate\",\"ridge\":416,\"a\":64,\"owners\":[93,105]},{\"tag\":\"mate\",\"ridge\":416,\"a\":73,\"owners\":[87,93,99,103]},{\"tag\":\"mate\",\"ridge\":416,\"a\":75,\"owners\":[87,93,99,100,105]},{\"tag\":\"mate\",\"ridge\":897,\"a\":67,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":897,\"a\":75,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":394,\"a\":82,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":394,\"a\":93,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":450,\"a\":89,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":408,\"a\":98,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":408,\"a\":105,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":464,\"a\":102,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":41,\"full_literals\":[-7,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":82,\"full_literals\":[-25,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":62,\"full_literals\":[-16,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":98,\"full_literals\":[-29,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":52,\"full_literals\":[-12,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-21,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-22,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":63,\"full_literals\":[-17,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":75,\"full_literals\":[-24,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":60,\"full_literals\":[-15,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":64,\"full_literals\":[-18,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-23,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":57,\"full_literals\":[-14,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":65,\"full_literals\":[-19,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":66,\"full_literals\":[-20,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":87,\"full_literals\":[-26,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":100,\"full_literals\":[-31,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":103,\"full_literals\":[-33,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":93,\"full_literals\":[-28,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":99,\"full_literals\":[-30,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":105,\"full_literals\":[-34,42]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-47,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-45,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":8,\"owners\":[3,9,32,35,38,40,42,45,49,50,53,57,60,63,65,66,67,74,75]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[41,52,62,64,67,73,75,82,87,89,93,98,99,100,102,103,105]}]}"
  "p cnf 51 68\n-1 14 15 17 19 20 21 0\n-3 15 17 19 20 21 0\n-4 14 19 20 21 0\n-6 14 15 17 19 20 21 0\n-8 14 15 19 0\n-2 14 15 19 20 23 24 0\n-5 23 24 0\n-9 15 19 20 23 24 0\n-10 14 19 20 24 0\n-13 14 15 19 0\n-7 12 0\n-16 25 26 27 30 33 0\n-18 25 27 29 32 0\n-26 16 21 29 32 0\n-30 7 16 21 27 32 0\n-31 7 21 25 27 0\n-33 7 16 25 27 29 32 0\n-11 17 23 0\n-12 30 31 33 34 0\n-18 28 34 0\n-22 26 28 30 33 0\n-24 26 28 30 31 34 0\n-21 24 0\n-24 21 0\n-25 28 0\n-28 25 0\n-27 0\n-29 34 0\n-34 29 0\n-32 0\n-7 35 0\n-25 35 0\n-16 36 0\n-29 36 0\n-12 37 0\n-21 37 0\n-22 37 0\n-17 38 0\n-24 38 0\n-15 39 0\n-18 39 0\n-23 39 0\n-14 40 0\n-19 40 0\n-20 40 0\n-26 41 0\n-31 41 0\n-33 41 0\n-28 42 0\n-30 42 0\n-34 42 0\n-35 43 0\n-37 44 0\n-36 44 0\n-44 45 0\n-43 45 0\n-39 46 0\n-38 46 0\n-42 47 0\n-41 47 0\n-47 48 0\n-40 -47 49 0\n-49 50 0\n-46 -48 50 0\n-45 -50 51 0\n-51 0\n1 2 3 4 5 6 8 9 10 11 13 14 15 17 19 20 21 23 24 0\n7 12 16 18 21 22 24 25 26 27 28 29 30 31 32 33 34 0\n"
  "69 7 12 16 18 21 22 24 25 26 28 29 30 31 33 34 0 27 30 68 0\n70 45 0 30 27 55 56 53 54 52 35 36 37 33 34 31 32 24 16 14 15 29 13 26 17 69 0\n71 -50 0 70 66 65 0\n72 -49 0 71 63 0\n73 40 46 0 58 39 23 57 42 38 18 7 40 43 44 45 1 6 9 4 5 10 3 2 8 67 0\n74 46 0 72 27 57 58 41 39 23 73 62 59 60 49 50 51 46 47 48 25 19 28 21 12 11 69 0\n75 -48 0 74 71 64 0\n76 -47 0 75 61 0\n77 -42 0 76 59 0\n78 -41 0 76 60 0\n79 -28 0 77 49 0\n80 -30 0 77 50 0\n81 -34 0 77 51 0\n82 -26 0 78 46 0\n83 -31 0 78 47 0\n84 -33 0 78 48 0\n85 -18 0 79 81 20 0\n86 -25 0 79 25 0\n87 -12 0 80 83 84 81 19 0\n88 -24 0 80 79 82 83 81 22 0\n89 -29 0 81 28 0\n90 -22 0 82 79 80 84 21 0\n91 -16 0 86 82 27 80 84 12 0\n92 -7 0 87 11 0\n93 -21 0 88 23 0\n94 0 90 91 92 87 85 93 88 86 82 80 89 79 83 84 81 69 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record010
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "278cb0dc8f07c78b2a36a3a1e9a639996358763392e1b89e1783e787919c7299a659366391e725694e5c5595356351d70d3362d4b46d8749d1743d70f2368d6338f1364e331cf0b32e2b4ae1b26c3b31ca719d1715c3743c8f13cd21a85a619262582e07b21346291a61916585494950b41d60cc348c6324c5312c2b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6d349a4da4926da4924936936da4924924934d3492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 52), (facetIndex 71), (facetIndex 82)]))
 (.leaf ([(facetIndex 72), (facetIndex 83)])))
 (.branch 3
 (.leaf ([(facetIndex 93), (facetIndex 99)]))
 (.branch 4
 (.leaf ([(facetIndex 48), (facetIndex 66)]))
 (.leaf ([(facetIndex 65), (facetIndex 67)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 89), (facetIndex 90)]))
 (.leaf ([(facetIndex 98), (facetIndex 103)])))
 (.branch 8
 (.leaf ([(facetIndex 100), (facetIndex 102)]))
 (.branch 9
 (.leaf ([(facetIndex 50), (facetIndex 68), (facetIndex 81)]))
 (.leaf ([(facetIndex 96), (facetIndex 101), (facetIndex 104)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "967972609002005500000108000000001000843400000000000000803z30;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0, 1]
def grouped3_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0003 : List Nat := [2]
def grouped3_0004 : List Nat := [2, 3, 4]
def grouped3_0005 : List Nat := [3]
def grouped3_0006 : List Nat := [3, 4]
def grouped3_0007 : List Nat := [4]
def grouped3_0008 : List Nat := [5]
def grouped3_0009 : List Nat := [5, 6]
def grouped3_0010 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0011 : List Nat := [6]
def grouped3_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [7, 8, 9]
def grouped3_0014 : List Nat := [8]
def grouped3_0015 : List Nat := [8, 9]
def grouped3_0016 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record010" "{\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record010" 34

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record010" "{\"ridges\":[[20,536],[24,769],[44,536],[48,778],[52,786],[56,769],[61,536],[66,780],[71,788],[74,769],[76,536],[78,536],[80,800],[82,912],[98,778],[103,780]],\"owners\":[[20,536,[96,101,104],[44,61,76,78]],[44,536,[101,104],[20,61,76,78,96]],[61,536,[96,104],[20,44,76,78,101]],[76,536,[],[20,44,61,78,96,101,104]],[78,536,[96,101],[20,44,61,76,104]],[24,769,[48,52,66,71,82],[56,74,80]],[56,769,[66,71,82],[24,48,52,74,80]],[74,769,[48,52,82],[24,56,66,71,80]],[80,800,[],[24,56,74,98,103]],[48,778,[98],[]],[98,778,[48],[]],[52,786,[],[]],[66,780,[103],[]],[103,780,[66],[]],[71,788,[],[]],[82,912,[],[]]],\"edges\":[[34,[20,44,50,52,61,68,71,76,78,81,82,96,101,104]],[44,[24,48,52,56,66,71,74,80,82,98,103]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record010" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record010\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,18,20,22],[-3,20,22],[-8,18,22],[-13],[-14,18,20],[-2,4,6,9,11,17],[-7,9,11,17],[-12,4,6,17],[-15],[-4,19],[-19,4],[-6],[-9,21],[-21,9],[-11],[-17],[-23,4,9],[-4,23],[-9,23],[-19,24],[-21,24],[-5,25],[-10,25],[-16,25],[-18,26],[-20,26],[-22,26],[-23,27],[-27,28],[-28,29],[-24,30],[-26,31],[-25,31],[-31,32],[-30,-32,33],[-29,-33,34],[-34],[1,3,5,6,8,10,11,13,14,16,17,18,20,22],[2,4,6,7,9,11,12,15,17,19,21]],\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":536,\"a\":20,\"owners\":[96,101,104]},{\"tag\":\"mate\",\"ridge\":536,\"a\":44,\"owners\":[101,104]},{\"tag\":\"mate\",\"ridge\":536,\"a\":61,\"owners\":[96,104]},{\"tag\":\"mate\",\"ridge\":536,\"a\":76,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":536,\"a\":78,\"owners\":[96,101]},{\"tag\":\"mate\",\"ridge\":769,\"a\":24,\"owners\":[48,52,66,71,82]},{\"tag\":\"mate\",\"ridge\":769,\"a\":56,\"owners\":[66,71,82]},{\"tag\":\"mate\",\"ridge\":769,\"a\":74,\"owners\":[48,52,82]},{\"tag\":\"mate\",\"ridge\":800,\"a\":80,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":778,\"a\":48,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":778,\"a\":98,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":786,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":780,\"a\":66,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":780,\"a\":103,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":788,\"a\":71,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":912,\"a\":82,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[48,66],\"full_literals\":[-23,4,9]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":48,\"full_literals\":[-4,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":66,\"full_literals\":[-9,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":98,\"full_literals\":[-19,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":103,\"full_literals\":[-21,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":50,\"full_literals\":[-5,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":68,\"full_literals\":[-10,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":81,\"full_literals\":[-16,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":96,\"full_literals\":[-18,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":101,\"full_literals\":[-20,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":104,\"full_literals\":[-22,26]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-23,false,27],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-30,-32,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-29,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[20,44,50,52,61,68,71,76,78,81,82,96,101,104]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[24,48,52,56,66,71,74,80,82,98,103]}]}"
  "p cnf 34 39\n-1 18 20 22 0\n-3 20 22 0\n-8 18 22 0\n-13 0\n-14 18 20 0\n-2 4 6 9 11 17 0\n-7 9 11 17 0\n-12 4 6 17 0\n-15 0\n-4 19 0\n-19 4 0\n-6 0\n-9 21 0\n-21 9 0\n-11 0\n-17 0\n-23 4 9 0\n-4 23 0\n-9 23 0\n-19 24 0\n-21 24 0\n-5 25 0\n-10 25 0\n-16 25 0\n-18 26 0\n-20 26 0\n-22 26 0\n-23 27 0\n-27 28 0\n-28 29 0\n-24 30 0\n-26 31 0\n-25 31 0\n-31 32 0\n-30 -32 33 0\n-29 -33 34 0\n-34 0\n1 3 5 6 8 10 11 13 14 16 17 18 20 22 0\n2 4 6 7 9 11 12 15 17 19 21 0\n"
  "40 1 3 5 8 10 14 16 18 20 22 0 12 15 4 16 38 0\n41 2 4 7 9 12 19 21 0 12 15 9 16 39 0\n42 23 0 16 15 12 18 19 8 11 7 14 6 41 0\n43 27 0 42 28 0\n44 28 0 43 29 0\n45 29 0 44 30 0\n46 -33 0 45 37 36 0\n47 24 0 42 20 21 10 13 17 0\n48 30 0 47 31 0\n49 -32 0 48 46 35 0\n50 -31 0 49 34 0\n51 -26 0 50 32 0\n52 -25 0 50 33 0\n53 -18 0 51 25 0\n54 -20 0 51 26 0\n55 -22 0 51 27 0\n56 -5 0 52 22 0\n57 -10 0 52 23 0\n58 -16 0 52 24 0\n59 -3 0 54 55 2 0\n60 -1 0 54 53 55 1 0\n61 -14 0 54 53 5 0\n62 -8 0 55 53 3 0\n63 0 57 60 56 62 59 61 58 53 54 55 40 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record014
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ce0f43707ce4b3272b2a5ab1a668da8e93a1e8d68d876638ce4b86e2785e0f9e1e47316c4f1727295a719664d98e5391e5a5394d58d4b51d58d3352d2745de0dc3c8e6358f13a4d9334e334cc73c2d8b52ccb8ad2b1ae1b46c9b16c3b61e2749c6785c570dd0f23c2f1b03c318961381ec86314a4690e4c5194950d44d0b41dc0d8330e1324d0b12c1b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b69b6db6db69b69a49369b6936d24d249349249369249b4926924924da492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 74), (facetIndex 84), (facetIndex 85), (facetIndex 88)]))
 (.leaf ([(facetIndex 53), (facetIndex 79), (facetIndex 80), (facetIndex 87)])))
 (.branch 3
 (.leaf ([(facetIndex 100), (facetIndex 103), (facetIndex 104), (facetIndex 109)]))
 (.leaf ([(facetIndex 68), (facetIndex 78), (facetIndex 83)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 95), (facetIndex 102), (facetIndex 107)]))
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 47), (facetIndex 52), (facetIndex 59), (facetIndex 60), (facetIndex 108)])))
 (.branch 7
 (.leaf ([(facetIndex 93), (facetIndex 96), (facetIndex 97), (facetIndex 101), (facetIndex 105)]))
 (.branch 8
 (.leaf ([(facetIndex 99), (facetIndex 111), (facetIndex 112)]))
 (.leaf ([(facetIndex 106), (facetIndex 113)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "87702548622462706640600000100030011300000000030000000550000015000050000000055z25;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
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
def grouped3_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8]
def grouped3_0016 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record014" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record014" 51

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record014" "{\"ridges\":[[10,385],[10,386],[22,560],[23,800],[39,385],[39,386],[50,385],[50,386],[54,560],[56,385],[56,386],[60,610],[61,800],[62,385],[62,386],[63,385],[63,386],[68,396],[71,560],[74,420],[77,560],[79,408],[82,800],[83,456],[85,432],[86,560],[87,912],[88,480],[95,396],[97,550],[103,408],[107,456],[109,912]],\"owners\":[[10,385,[68,74,79,83,85,87,88],[39,50,56,62,63]],[39,385,[79,83,85,87,88],[10,50,56,62,63,68,74]],[50,385,[74,85,87,88],[10,39,56,62,63,68,79,83]],[56,385,[68,74,83,88],[10,39,50,62,63,79,85,87]],[62,385,[68,74,79,85,87],[10,39,50,56,63,83,88]],[63,385,[68,74,79,83,85,88],[10,39,50,56,62,87]],[10,386,[95,103,107,109],[39,50,56,62,63]],[39,386,[103,107,109],[10,50,56,62,63,95]],[50,386,[109],[10,39,56,62,63,95,103,107]],[56,386,[95,107],[10,39,50,62,63,103,109]],[62,386,[95,103,109],[10,39,50,56,63,107]],[63,386,[95,103,107],[10,39,50,56,62,109]],[22,560,[97,101,108,113],[54,71,77,86]],[54,560,[113],[22,71,77,86,97,101,108]],[71,560,[101,108,113],[22,54,77,86,97]],[77,560,[97,108],[22,54,71,86,101,113]],[86,560,[97,101],[22,54,71,77,108,113]],[23,800,[106,108,113],[61,82,86]],[61,800,[113],[23,82,86,106,108]],[82,800,[108],[23,61,86,106,113]],[97,550,[38],[]],[60,610,[],[]],[68,396,[95],[]],[95,396,[68],[]],[74,420,[],[]],[79,408,[103],[]],[103,408,[79],[]],[83,456,[107],[]],[107,456,[83],[]],[85,432,[],[]],[87,912,[109],[]],[109,912,[87],[]],[88,480,[],[]]],\"edges\":[[38,[22,23,38,47,54,60,61,71,77,82,86,97,101,106,108,113]],[42,[10,39,50,56,62,63,68,74,79,83,85,87,88,95,103,107,109]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record014" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record014\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,14,16,18,20,21,23,24],[-5,18,20,21,23,24],[-7,16,21,23,24],[-9,14,16,20,24],[-12,14,16,18,21,23],[-13,14,16,18,20,21,24],[-1,25,28,30,32],[-5,28,30,32],[-7,32],[-9,25,30],[-12,25,28,32],[-13,25,28,30],[-2,26,27,31,33],[-8,33],[-15,27,31,33],[-17,26,31],[-22,26,27],[-3,29,31,33],[-11,33],[-19,31],[-26,4],[-10],[-14,25],[-25,14],[-16],[-18,28],[-28,18],[-20,30],[-30,20],[-21],[-23,32],[-32,23],[-24],[-18,34],[-23,34],[-28,35],[-32,35],[-14,36],[-20,36],[-25,37],[-30,37],[-4,38],[-6,38],[-31,38],[-26,39],[-27,39],[-29,40],[-33,40],[-34,41],[-36,42],[-35,42],[-42,43],[-41,43],[-41,-42,44],[-38,45],[-37,45],[-37,-38,46],[-40,47],[-47,48],[-39,48],[-48,49],[-45,49],[-45,-48,50],[-46,50],[-43,-50,51],[-44,-49,51],[-51],[2,3,4,6,8,10,11,15,17,19,22,26,27,29,31,33],[1,5,7,9,12,13,14,16,18,20,21,23,24,25,28,30,32]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":385,\"a\":10,\"owners\":[68,74,79,83,85,87,88]},{\"tag\":\"mate\",\"ridge\":385,\"a\":39,\"owners\":[79,83,85,87,88]},{\"tag\":\"mate\",\"ridge\":385,\"a\":50,\"owners\":[74,85,87,88]},{\"tag\":\"mate\",\"ridge\":385,\"a\":56,\"owners\":[68,74,83,88]},{\"tag\":\"mate\",\"ridge\":385,\"a\":62,\"owners\":[68,74,79,85,87]},{\"tag\":\"mate\",\"ridge\":385,\"a\":63,\"owners\":[68,74,79,83,85,88]},{\"tag\":\"mate\",\"ridge\":386,\"a\":10,\"owners\":[95,103,107,109]},{\"tag\":\"mate\",\"ridge\":386,\"a\":39,\"owners\":[103,107,109]},{\"tag\":\"mate\",\"ridge\":386,\"a\":50,\"owners\":[109]},{\"tag\":\"mate\",\"ridge\":386,\"a\":56,\"owners\":[95,107]},{\"tag\":\"mate\",\"ridge\":386,\"a\":62,\"owners\":[95,103,109]},{\"tag\":\"mate\",\"ridge\":386,\"a\":63,\"owners\":[95,103,107]},{\"tag\":\"mate\",\"ridge\":560,\"a\":22,\"owners\":[97,101,108,113]},{\"tag\":\"mate\",\"ridge\":560,\"a\":54,\"owners\":[113]},{\"tag\":\"mate\",\"ridge\":560,\"a\":71,\"owners\":[101,108,113]},{\"tag\":\"mate\",\"ridge\":560,\"a\":77,\"owners\":[97,108]},{\"tag\":\"mate\",\"ridge\":560,\"a\":86,\"owners\":[97,101]},{\"tag\":\"mate\",\"ridge\":800,\"a\":23,\"owners\":[106,108,113]},{\"tag\":\"mate\",\"ridge\":800,\"a\":61,\"owners\":[113]},{\"tag\":\"mate\",\"ridge\":800,\"a\":82,\"owners\":[108]},{\"tag\":\"mate\",\"ridge\":550,\"a\":97,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":610,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":396,\"a\":68,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":396,\"a\":95,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":420,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":408,\"a\":79,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":408,\"a\":103,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":456,\"a\":83,\"owners\":[107]},{\"tag\":\"mate\",\"ridge\":456,\"a\":107,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":432,\"a\":85,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":912,\"a\":87,\"owners\":[109]},{\"tag\":\"mate\",\"ridge\":912,\"a\":109,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":480,\"a\":88,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":79,\"full_literals\":[-18,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-23,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":103,\"full_literals\":[-28,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":109,\"full_literals\":[-32,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":68,\"full_literals\":[-14,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-20,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":95,\"full_literals\":[-25,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":107,\"full_literals\":[-30,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":38,\"full_literals\":[-4,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":47,\"full_literals\":[-6,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":108,\"full_literals\":[-31,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":97,\"full_literals\":[-26,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":101,\"full_literals\":[-27,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":106,\"full_literals\":[-29,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":113,\"full_literals\":[-33,40]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-42,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-37,-38,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-43,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[22,23,38,47,54,60,61,71,77,82,86,97,101,106,108,113]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[10,39,50,56,62,63,68,74,79,83,85,87,88,95,103,107,109]}]}"
  "p cnf 51 69\n-1 14 16 18 20 21 23 24 0\n-5 18 20 21 23 24 0\n-7 16 21 23 24 0\n-9 14 16 20 24 0\n-12 14 16 18 21 23 0\n-13 14 16 18 20 21 24 0\n-1 25 28 30 32 0\n-5 28 30 32 0\n-7 32 0\n-9 25 30 0\n-12 25 28 32 0\n-13 25 28 30 0\n-2 26 27 31 33 0\n-8 33 0\n-15 27 31 33 0\n-17 26 31 0\n-22 26 27 0\n-3 29 31 33 0\n-11 33 0\n-19 31 0\n-26 4 0\n-10 0\n-14 25 0\n-25 14 0\n-16 0\n-18 28 0\n-28 18 0\n-20 30 0\n-30 20 0\n-21 0\n-23 32 0\n-32 23 0\n-24 0\n-18 34 0\n-23 34 0\n-28 35 0\n-32 35 0\n-14 36 0\n-20 36 0\n-25 37 0\n-30 37 0\n-4 38 0\n-6 38 0\n-31 38 0\n-26 39 0\n-27 39 0\n-29 40 0\n-33 40 0\n-34 41 0\n-36 42 0\n-35 42 0\n-42 43 0\n-41 43 0\n-41 -42 44 0\n-38 45 0\n-37 45 0\n-37 -38 46 0\n-40 47 0\n-47 48 0\n-39 48 0\n-48 49 0\n-45 49 0\n-45 -48 50 0\n-46 50 0\n-43 -50 51 0\n-44 -49 51 0\n-51 0\n2 3 4 6 8 10 11 15 17 19 22 26 27 29 31 33 0\n1 5 7 9 12 13 14 16 18 20 21 23 24 25 28 30 32 0\n"
  "70 2 3 4 6 8 11 15 17 19 22 26 27 29 31 33 0 22 68 0\n71 1 5 7 9 12 13 14 18 20 23 25 28 30 32 0 25 30 33 69 0\n72 43 0 30 33 25 52 53 50 51 49 38 39 36 37 34 35 1 24 29 4 8 11 12 9 71 0\n73 -50 0 72 67 65 0\n74 -46 0 73 64 0\n75 34 37 0 33 30 25 40 41 10 28 23 34 35 2 27 5 6 1 3 32 71 0\n76 37 44 0 40 41 23 28 10 75 49 54 51 36 37 8 26 11 12 7 9 31 71 0\n77 -37 0 74 73 56 57 63 42 43 44 59 60 21 20 16 58 46 47 48 17 14 19 15 13 18 70 0\n78 44 0 77 76 0\n79 -49 0 78 67 66 0\n80 -48 0 79 61 0\n81 -45 0 79 62 0\n82 -47 0 80 59 0\n83 -39 0 80 60 0\n84 -38 0 81 55 0\n85 -40 0 82 58 0\n86 -26 0 83 45 0\n87 -27 0 83 46 0\n88 -4 0 84 42 0\n89 -6 0 84 43 0\n90 -31 0 84 44 0\n91 -29 0 85 47 0\n92 -33 0 85 48 0\n93 -22 0 87 86 17 0\n94 -19 0 90 20 0\n95 -17 0 90 86 16 0\n96 -8 0 92 14 0\n97 -11 0 92 19 0\n98 -15 0 92 90 87 15 0\n99 -2 0 92 86 90 87 13 0\n100 -3 0 92 90 91 18 0\n101 0 100 98 99 89 88 96 97 95 94 93 86 87 91 90 92 70 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00068.record014
