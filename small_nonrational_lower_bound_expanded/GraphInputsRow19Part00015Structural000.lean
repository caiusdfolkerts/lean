module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00015Frames
public import GraphInputsRow19Part00015Leaves
public import GraphInputsRow19Part00015Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00015.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2e8b319cb2a6a8eac671876a398e938ce1b91e0fae1b26a99a4e9665c565475634cd1b51d2743db0dc398d331ce8b62e4b32e2b1ad1b61d4731c6715c3743c8f13c2f98a2a0e91607839614c54548d0746344c330ac1b41c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36da4db6db6936db69349a49b4936da492492492249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 24), (facetIndex 25), (facetIndex 30), (facetIndex 37), (facetIndex 38)]))
 (.branch 2
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 39), (facetIndex 68)]))
 (.leaf ([(facetIndex 20), (facetIndex 57), (facetIndex 67)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 23), (facetIndex 44), (facetIndex 47), (facetIndex 58)]))
 (.leaf ([(facetIndex 22), (facetIndex 42), (facetIndex 43)])))
 (.branch 6
 (.leaf ([(facetIndex 29), (facetIndex 46), (facetIndex 49), (facetIndex 50)]))
 (.leaf ([(facetIndex 21), (facetIndex 26), (facetIndex 27), (facetIndex 28)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "14000000d000016874390020000122ed80732000000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 48)]))
 (.leaf ([(facetIndex 35), (facetIndex 51)])))
 (.branch 3
 (.leaf ([(facetIndex 59), (facetIndex 64)]))
 (.branch 4
 (.leaf ([(facetIndex 62), (facetIndex 70)]))
 (.leaf ([(facetIndex 34), (facetIndex 52), (facetIndex 54)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 53), (facetIndex 56), (facetIndex 72)]))
 (.leaf ([(facetIndex 33), (facetIndex 36), (facetIndex 40), (facetIndex 63)])))
 (.branch 8
 (.leaf ([(facetIndex 41), (facetIndex 60), (facetIndex 65), (facetIndex 66)]))
 (.branch 9
 (.leaf ([(facetIndex 55), (facetIndex 61), (facetIndex 69)]))
 (.leaf ([(facetIndex 71)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5938007726387200584541000000000760006146z21;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [1, 2]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [3, 4, 5, 6]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6]
def grouped2_0010 : List Nat := [6]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3, 4]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [3, 4]
def grouped3_0020 : List Nat := [4]
def grouped3_0021 : List Nat := [5]
def grouped3_0022 : List Nat := [5, 6]
def grouped3_0023 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0024 : List Nat := [6]
def grouped3_0025 : List Nat := [7]
def grouped3_0026 : List Nat := [7, 8, 9]
def grouped3_0027 : List Nat := [8, 9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00015.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00015.record011" 67

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00015.record011" "{\"ridges\":[[14,49],[17,50],[27,196],[29,385],[31,97],[32,552],[35,394],[36,648],[39,97],[39,608],[42,49],[45,108],[48,116],[49,385],[50,385],[51,408],[54,648],[56,673],[56,704],[57,50],[64,116],[68,522],[68,552],[68,608],[72,232],[72,648],[72,704]],\"owners\":[[14,49,[6,24,37,38,48],[42]],[42,49,[6,37,38],[14,24,48]],[17,50,[6,24,37,38,64],[57,67]],[57,50,[6,37,38],[17,24,64,67]],[31,97,[48,56],[8,26,37,39,45,52,53]],[39,97,[45,48,52],[8,26,31,37,53,56]],[27,196,[71],[12,46,50,60,65,66]],[29,385,[51],[13,35,40,47,49,50]],[49,385,[35,40],[13,29,47,50,51]],[50,385,[35,51],[13,29,40,47,49]],[68,522,[36,63],[18,32,34,61,67,69]],[32,552,[72],[18,53,54,67,68]],[68,552,[54],[18,32,53,67,72]],[39,608,[72],[19,53,56,68]],[68,608,[56],[19,39,53,72]],[35,394,[62],[]],[36,648,[71,72],[54,55,63,69]],[54,648,[63,69,71],[36,55,72]],[72,648,[36,63],[54,55,69,71]],[56,704,[66,69,71],[41,55,72]],[72,704,[41,66],[55,56,69,71]],[45,108,[59],[]],[48,116,[64],[]],[64,116,[48],[]],[51,408,[70],[]],[72,232,[52],[]],[56,673,[54],[]]],\"edges\":[[30,[6,14,17,24,37,38,42,48,57,64,67]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00015.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00015.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-1],[-11,-4],[-11,-6],[-12,-4],[-15,-11],[-16,-11],[-17,-14],[-18,-7],[-19,-17],[-24,-9],[-30,-12],[-33,-18],[-36,-11],[-36,-12],[-37,-22],[-38,-37],[-40,-11],[-40,-37],[-41,-5],[-41,-22],[-41,-40],[-2,1,6,15,16,23],[-20,1,15,16],[-3,1,6,15,16,34],[-30,1,15,16],[-11,23,29],[-17,21,23,27],[-8,40],[-10,26],[-24,13,18],[-25,13,26],[-37,14,33],[-12,41],[-37,28],[-17,41],[-37,29],[-13,32],[-14,40,41],[-28,33,38,40],[-41,14,33],[-29,35,38,40],[-41,19,35],[-21,31],[-23,34],[-34,23],[-26,39],[-41,27],[-29,28],[-42,11,12,17,37],[-43,4,30,36],[-44,10,22,24,25],[-45,5,7,8,9],[-46,42],[-46,43],[-47,46],[-48,44],[-48,45],[-49,48],[-50,47],[-50,49],[50],[-51,21,23],[-21,51],[-23,51],[-52,13,26],[-13,52],[-26,52],[-31,53],[-34,53],[-32,54],[-39,54],[-27,55],[-28,55],[-29,56],[-41,56],[-33,57],[-35,58],[-59,51,52],[-52,59],[-51,59],[-55,60],[-54,60],[-60,61],[-53,61],[-62,59,61],[-61,62],[-59,62],[-59,-61,63],[-56,-57,64],[-58,65],[-64,-65,66],[-63,-66,67],[-67],[1,2,3,6,15,16,20,23,30,34,36]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":31,\"b\":6},{\"tag\":\"incompatible\",\"a\":31,\"b\":20},{\"tag\":\"incompatible\",\"a\":31,\"b\":24},{\"tag\":\"incompatible\",\"a\":32,\"b\":20},{\"tag\":\"incompatible\",\"a\":37,\"b\":31},{\"tag\":\"incompatible\",\"a\":38,\"b\":31},{\"tag\":\"incompatible\",\"a\":39,\"b\":36},{\"tag\":\"incompatible\",\"a\":40,\"b\":26},{\"tag\":\"incompatible\",\"a\":41,\"b\":39},{\"tag\":\"incompatible\",\"a\":49,\"b\":28},{\"tag\":\"incompatible\",\"a\":57,\"b\":32},{\"tag\":\"incompatible\",\"a\":63,\"b\":40},{\"tag\":\"incompatible\",\"a\":67,\"b\":31},{\"tag\":\"incompatible\",\"a\":67,\"b\":32},{\"tag\":\"incompatible\",\"a\":68,\"b\":46},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":71,\"b\":31},{\"tag\":\"incompatible\",\"a\":71,\"b\":68},{\"tag\":\"incompatible\",\"a\":72,\"b\":21},{\"tag\":\"incompatible\",\"a\":72,\"b\":46},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"mate\",\"ridge\":49,\"a\":14,\"owners\":[6,24,37,38,48]},{\"tag\":\"mate\",\"ridge\":49,\"a\":42,\"owners\":[6,37,38]},{\"tag\":\"mate\",\"ridge\":50,\"a\":17,\"owners\":[6,24,37,38,64]},{\"tag\":\"mate\",\"ridge\":50,\"a\":57,\"owners\":[6,37,38]},{\"tag\":\"mate\",\"ridge\":97,\"a\":31,\"owners\":[48,56]},{\"tag\":\"mate\",\"ridge\":97,\"a\":39,\"owners\":[45,48,52]},{\"tag\":\"mate\",\"ridge\":196,\"a\":27,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":385,\"a\":29,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":385,\"a\":49,\"owners\":[35,40]},{\"tag\":\"mate\",\"ridge\":385,\"a\":50,\"owners\":[35,51]},{\"tag\":\"mate\",\"ridge\":522,\"a\":68,\"owners\":[36,63]},{\"tag\":\"mate\",\"ridge\":552,\"a\":32,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":552,\"a\":68,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":608,\"a\":39,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":608,\"a\":68,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":394,\"a\":35,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":648,\"a\":36,\"owners\":[71,72]},{\"tag\":\"mate\",\"ridge\":648,\"a\":54,\"owners\":[63,69,71]},{\"tag\":\"mate\",\"ridge\":648,\"a\":72,\"owners\":[36,63]},{\"tag\":\"mate\",\"ridge\":704,\"a\":56,\"owners\":[66,69,71]},{\"tag\":\"mate\",\"ridge\":704,\"a\":72,\"owners\":[41,66]},{\"tag\":\"mate\",\"ridge\":108,\"a\":45,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":116,\"a\":48,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":116,\"a\":64,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":408,\"a\":51,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":232,\"a\":72,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":673,\"a\":56,\"owners\":[54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[31,32,39,68],\"full_literals\":[-42,11,12,17,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[20,57,67],\"full_literals\":[-43,4,30,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[29,46,49,50],\"full_literals\":[-44,10,22,24,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[21,26,27,28],\"full_literals\":[-45,5,7,8,9]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-50,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-50,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[45,48],\"full_literals\":[-51,21,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":45,\"full_literals\":[-21,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":48,\"full_literals\":[-23,51]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[35,51],\"full_literals\":[-52,13,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":35,\"full_literals\":[-13,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":51,\"full_literals\":[-26,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":59,\"full_literals\":[-31,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":64,\"full_literals\":[-34,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":62,\"full_literals\":[-32,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":70,\"full_literals\":[-39,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":52,\"full_literals\":[-27,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":54,\"full_literals\":[-28,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":56,\"full_literals\":[-29,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":72,\"full_literals\":[-41,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":63,\"full_literals\":[-33,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":66,\"full_literals\":[-35,58]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-57,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-63,-66,67],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":30,\"owners\":[6,14,17,24,37,38,42,48,57,64,67]}]}"
  "95 47 0 61 59 0\n96 49 0 61 60 0\n97 46 0 95 55 0\n98 48 0 96 58 0\n99 42 0 97 53 0\n100 43 0 97 54 0\n101 44 0 98 56 0\n102 45 0 98 57 0\n103 62 0 99 86 87 83 80 81 63 64 72 73 47 27 34 48 33 26 49 0\n104 -40 0 99 17 18 21 33 35 49 0\n105 -8 0 104 28 0\n106 61 0 103 83 84 85 82 68 69 70 71 43 44 37 46 62 65 78 0\n107 16 36 1 6 15 2 20 23 30 34 0 94 24 0\n108 -11 23 0 45 1 3 5 6 13 22 23 25 107 0\n109 41 59 0 104 99 101 80 64 108 79 67 29 66 31 33 35 38 49 15 32 51 12 30 0\n110 59 0 101 105 102 79 66 67 31 29 109 19 20 51 10 30 52 8 0\n111 63 0 110 106 88 0\n112 -66 0 111 93 92 0\n113 -12 0 100 4 11 14 50 0\n114 -11 0 100 1 2 5 6 13 50 25 0\n115 -17 0 112 7 9 35 40 42 75 76 77 89 90 91 0\n116 37 0 115 99 114 113 49 0\n117 -38 0 116 16 0\n118 28 0 116 34 0\n119 29 0 116 36 0\n120 33 0 118 117 104 39 0\n121 35 0 119 117 104 41 0\n122 56 0 119 74 0\n123 57 0 120 76 0\n124 58 0 121 77 0\n125 64 0 122 123 89 0\n126 65 0 124 90 0\n127 0 125 126 112 91 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00015.record011
