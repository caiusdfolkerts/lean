module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow25Part00014Frames
public import GraphInputsRow25Part00014Leaves
public import GraphInputsRow25Part00014Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00014.record037
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "751744f07cb8a9a6693a1e996359361da2e4b86e4785e0fba1b85e174571e2729a65994e4797156565555355351d62d1b45d0f6c3a8da398ce3a4d934cc73a2d8b4ac6b86d1b26c5b0ed8731e2749d1725c3783d0f13d2c470d28a8661582e07991346294a51949465454554342d0768330e2318c9314e0b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b4db6db4d24924db4da6936924924924d249a4d24924d2492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 49), (facetIndex 61), (facetIndex 64), (facetIndex 73), (facetIndex 76)]))
 (.leaf ([(facetIndex 37), (facetIndex 41), (facetIndex 67), (facetIndex 69), (facetIndex 91)])))
 (.branch 3
 (.leaf ([(facetIndex 47), (facetIndex 51), (facetIndex 55), (facetIndex 59)]))
 (.branch 4
 (.leaf ([(facetIndex 45), (facetIndex 54), (facetIndex 74), (facetIndex 79)]))
 (.leaf ([(facetIndex 35), (facetIndex 40), (facetIndex 48), (facetIndex 88)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 34), (facetIndex 38), (facetIndex 39), (facetIndex 46), (facetIndex 85), (facetIndex 87)]))
 (.leaf ([(facetIndex 36), (facetIndex 65), (facetIndex 66), (facetIndex 68), (facetIndex 70)])))
 (.branch 8
 (.leaf ([(facetIndex 52), (facetIndex 56), (facetIndex 57), (facetIndex 60)]))
 (.branch 9
 (.leaf ([(facetIndex 83), (facetIndex 89), (facetIndex 99)]))
 (.leaf ([(facetIndex 33), (facetIndex 44), (facetIndex 62), (facetIndex 63), (facetIndex 84), (facetIndex 86)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "8000000010845959800030000300061616609907207723072004253900145516459z21;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 50), (facetIndex 75), (facetIndex 77)]))
 (.leaf ([(facetIndex 58), (facetIndex 80), (facetIndex 81), (facetIndex 82)])))
 (.branch 3
 (.leaf ([(facetIndex 95), (facetIndex 96)]))
 (.leaf ([(facetIndex 97)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 42), (facetIndex 71)]))
 (.leaf ([(facetIndex 53), (facetIndex 72), (facetIndex 78)])))
 (.branch 7
 (.leaf ([(facetIndex 90), (facetIndex 93), (facetIndex 100)]))
 (.branch 8
 (.leaf ([(facetIndex 94), (facetIndex 98)]))
 (.leaf ([(facetIndex 92), (facetIndex 101)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "860732276806000000011105000005400000000000010000500000000004z2a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3, 4]
def grouped2_0006 : List Nat := [5]
def grouped2_0007 : List Nat := [5, 6]
def grouped2_0008 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0009 : List Nat := [6]
def grouped2_0010 : List Nat := [7, 8, 9]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0022 : List Nat := [5]
def grouped3_0023 : List Nat := [6]
def grouped3_0024 : List Nat := [6, 7, 8]
def grouped3_0025 : List Nat := [7]
def grouped3_0026 : List Nat := [7, 8]
def grouped3_0027 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00014.record037" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":9,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00014.record037" 64

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00014.record037" "{\"ridges\":[[12,642],[24,400],[42,390],[50,394],[51,642],[54,400],[55,642],[58,418],[59,641],[59,642],[60,642],[69,400],[71,452],[74,400],[77,904],[79,400],[80,480],[82,928],[90,306],[92,390],[93,120],[94,306],[95,394],[98,120],[100,368],[101,452]],\"owners\":[[59,641,[75,77],[12,51,55,60,81,82]],[12,642,[96,97],[51,55,59,60]],[51,642,[97],[12,55,59,60,96]],[55,642,[97],[12,51,59,60,96]],[59,642,[96],[12,51,55,60,97]],[60,642,[96],[12,51,55,59,97]],[24,400,[92,95,101],[54,69,74,79]],[54,400,[101],[24,69,74,79,92,95]],[69,400,[95],[24,54,74,79,92,101]],[74,400,[92,101],[24,54,69,79,95]],[79,400,[92,95],[24,54,69,74,101]],[42,390,[92],[]],[92,390,[42],[]],[50,394,[95],[]],[95,394,[50],[]],[90,306,[53,94],[]],[94,306,[53,90],[]],[58,418,[],[]],[71,452,[101],[]],[101,452,[71],[]],[93,120,[72,98],[]],[98,120,[72,93],[]],[77,904,[],[]],[100,368,[78],[]],[80,480,[],[]],[82,928,[],[]]],\"edges\":[[42,[24,42,50,54,58,69,71,74,77,79,80,82,92,95,101]],[43,[12,51,55,59,60,75,77,81,82,96,97]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00014.record037" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00014.record037\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-8],[-13,-9],[-34,-3],[-34,-4],[-34,-5],[-34,-7],[-34,-10],[-34,-21],[-34,-28],[-34,-29],[-15,21,22],[-1,35,36],[-10,36],[-13,36],[-15,35],[-16,35],[-2,31,34,39],[-12,39],[-17,34],[-20,31,39],[-24,31,34],[-6,31],[-31,6],[-9,34],[-34,9],[-30,11,33],[-33,11,30],[-14],[-18,39],[-39,18],[-32,19,37],[-37,19,32],[-22],[-38,23],[-25],[-27],[-40,8,10,13,15],[-41,3,4,5,7,28,29],[-42,40],[-43,42],[-44,41],[-45,44],[-46,43,45],[46],[-21,47],[-26,48],[-35,49],[-36,50],[-6,51],[-18,51],[-11,52],[-19,52],[-23,52],[-53,30,32,38],[-30,53],[-32,53],[-54,33,37],[-33,54],[-37,54],[-55,31,39],[-31,55],[-39,55],[-48,56],[-47,56],[-50,57],[-49,57],[-57,58],[-56,58],[-52,59],[-51,59],[-60,54,55],[-55,60],[-54,60],[-61,53,60],[-60,61],[-53,-60,62],[-62,63],[-59,-61,63],[-58,-63,64],[-64],[2,6,9,12,14,17,18,20,22,24,25,27,31,34,39],[1,10,13,15,16,21,22,26,27,35,36]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":50,\"b\":47},{\"tag\":\"incompatible\",\"a\":55,\"b\":50},{\"tag\":\"incompatible\",\"a\":95,\"b\":34},{\"tag\":\"incompatible\",\"a\":95,\"b\":38},{\"tag\":\"incompatible\",\"a\":95,\"b\":39},{\"tag\":\"incompatible\",\"a\":95,\"b\":46},{\"tag\":\"incompatible\",\"a\":95,\"b\":51},{\"tag\":\"incompatible\",\"a\":95,\"b\":75},{\"tag\":\"incompatible\",\"a\":95,\"b\":85},{\"tag\":\"incompatible\",\"a\":95,\"b\":87},{\"tag\":\"mate\",\"ridge\":641,\"a\":59,\"owners\":[75,77]},{\"tag\":\"mate\",\"ridge\":642,\"a\":12,\"owners\":[96,97]},{\"tag\":\"mate\",\"ridge\":642,\"a\":51,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":642,\"a\":55,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":642,\"a\":59,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":642,\"a\":60,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":400,\"a\":24,\"owners\":[92,95,101]},{\"tag\":\"mate\",\"ridge\":400,\"a\":54,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":400,\"a\":69,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":400,\"a\":74,\"owners\":[92,101]},{\"tag\":\"mate\",\"ridge\":400,\"a\":79,\"owners\":[92,95]},{\"tag\":\"mate\",\"ridge\":390,\"a\":42,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":390,\"a\":92,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":394,\"a\":50,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":394,\"a\":95,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":306,\"a\":90,\"owners\":[53,94]},{\"tag\":\"mate\",\"ridge\":306,\"a\":94,\"owners\":[53,90]},{\"tag\":\"mate\",\"ridge\":418,\"a\":58,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":452,\"a\":71,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":452,\"a\":101,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":120,\"a\":93,\"owners\":[72,98]},{\"tag\":\"mate\",\"ridge\":120,\"a\":98,\"owners\":[72,93]},{\"tag\":\"mate\",\"ridge\":904,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":368,\"a\":100,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":480,\"a\":80,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":928,\"a\":82,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[47,51,55,59],\"full_literals\":[-40,8,10,13,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[34,38,39,46,85,87],\"full_literals\":[-41,3,4,5,7,28,29]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-42,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-43,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-45,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-46,43,45],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":9,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":75,\"full_literals\":[-21,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":81,\"full_literals\":[-26,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":96,\"full_literals\":[-35,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":97,\"full_literals\":[-36,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":42,\"full_literals\":[-6,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":71,\"full_literals\":[-18,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":53,\"full_literals\":[-11,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":72,\"full_literals\":[-19,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-23,52]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[90,93,100],\"full_literals\":[-53,30,32,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":90,\"full_literals\":[-30,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":93,\"full_literals\":[-32,53]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[94,98],\"full_literals\":[-54,33,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":94,\"full_literals\":[-33,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":98,\"full_literals\":[-37,54]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[92,101],\"full_literals\":[-55,31,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":92,\"full_literals\":[-31,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":101,\"full_literals\":[-39,55]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,53,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-62,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-58,-63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[24,42,50,54,58,69,71,74,77,79,80,82,92,95,101]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[12,51,55,59,60,75,77,81,82,96,97]}]}"
  "p cnf 64 82\n-9 -8 0\n-13 -9 0\n-34 -3 0\n-34 -4 0\n-34 -5 0\n-34 -7 0\n-34 -10 0\n-34 -21 0\n-34 -28 0\n-34 -29 0\n-15 21 22 0\n-1 35 36 0\n-10 36 0\n-13 36 0\n-15 35 0\n-16 35 0\n-2 31 34 39 0\n-12 39 0\n-17 34 0\n-20 31 39 0\n-24 31 34 0\n-6 31 0\n-31 6 0\n-9 34 0\n-34 9 0\n-30 11 33 0\n-33 11 30 0\n-14 0\n-18 39 0\n-39 18 0\n-32 19 37 0\n-37 19 32 0\n-22 0\n-38 23 0\n-25 0\n-27 0\n-40 8 10 13 15 0\n-41 3 4 5 7 28 29 0\n-42 40 0\n-43 42 0\n-44 41 0\n-45 44 0\n-46 43 45 0\n46 0\n-21 47 0\n-26 48 0\n-35 49 0\n-36 50 0\n-6 51 0\n-18 51 0\n-11 52 0\n-19 52 0\n-23 52 0\n-53 30 32 38 0\n-30 53 0\n-32 53 0\n-54 33 37 0\n-33 54 0\n-37 54 0\n-55 31 39 0\n-31 55 0\n-39 55 0\n-48 56 0\n-47 56 0\n-50 57 0\n-49 57 0\n-57 58 0\n-56 58 0\n-52 59 0\n-51 59 0\n-60 54 55 0\n-55 60 0\n-54 60 0\n-61 53 60 0\n-60 61 0\n-53 -60 62 0\n-62 63 0\n-59 -61 63 0\n-58 -63 64 0\n-64 0\n2 6 9 12 14 17 18 20 22 24 25 27 31 34 39 0\n1 10 13 15 16 21 22 26 27 35 36 0\n"
  "83 2 6 9 12 17 18 20 24 31 34 39 0 28 33 35 36 81 0\n84 1 10 13 15 16 21 26 35 36 0 33 36 82 0\n85 58 0 67 68 65 66 63 64 48 47 46 45 13 14 12 15 16 84 0\n86 -63 0 85 80 79 0\n87 -62 0 86 77 0\n88 -60 59 0 87 70 49 23 50 30 60 69 52 51 71 76 55 56 27 32 57 0\n89 -61 0 86 78 69 51 52 53 34 88 73 74 58 59 26 31 54 0\n90 -60 0 89 75 0\n91 -55 0 90 72 0\n92 -31 0 91 61 0\n93 -39 0 91 62 0\n94 -6 0 92 22 0\n95 -12 0 93 18 0\n96 -18 0 93 29 0\n97 -20 0 93 92 20 0\n98 34 0 93 97 92 96 95 94 19 24 21 17 83 0\n99 -3 0 98 3 0\n100 -4 0 98 4 0\n101 -5 0 98 5 0\n102 -7 0 98 6 0\n103 -10 0 98 7 0\n104 -21 0 98 8 0\n105 -28 0 98 9 0\n106 -29 0 98 10 0\n107 9 0 98 25 0\n108 -15 0 104 33 11 0\n109 -41 0 105 99 101 100 102 106 38 0\n110 -8 0 107 1 0\n111 -13 0 107 2 0\n112 -40 0 108 110 111 103 37 0\n113 -44 0 109 41 0\n114 -42 0 112 39 0\n115 -45 0 113 42 0\n116 -43 0 114 40 0\n117 0 116 115 44 43 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037 Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00014.record037
