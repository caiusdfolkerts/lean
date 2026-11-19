module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00029Frames
public import GraphInputsRow19Part00029Leaves
public import GraphInputsRow19Part00029Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00029.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1723ab46b19c68da2e4789e0f9713a745b15c58d62d4749d0f743b0dc358ce354e334cc7332e2b2ac6b46c9bc1e8761e4751cc789e1725c3783d0f0be620e9162381e984394548d0764350cc388c6344c3322c2b06e0741c8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6d24db6db492492492492492492492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.branch 2
 (.leaf ([(facetIndex 1)]))
 (.leaf ([(facetIndex 2)]))))
 (.branch 4
 (.leaf ([(facetIndex 3)]))
 (.branch 5
 (.leaf ([(facetIndex 4)]))
 (.leaf ([(facetIndex 5)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 6)]))
 (.branch 8
 (.leaf ([(facetIndex 7)]))
 (.leaf ([(facetIndex 8)]))))
 (.branch 10
 (.leaf ([(facetIndex 9)]))
 (.branch 11
 (.leaf ([(facetIndex 10)]))
 (.leaf ([(facetIndex 11)]))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ([(facetIndex 12)]))
 (.branch 14
 (.leaf ([(facetIndex 13)]))
 (.leaf ([(facetIndex 14)]))))
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.branch 17
 (.leaf ([(facetIndex 16)]))
 (.leaf ([(facetIndex 17)])))))
 (.branch 21
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.branch 20
 (.leaf ([(facetIndex 19)]))
 (.leaf ([(facetIndex 20)]))))
 (.branch 23
 (.branch 22
 (.leaf ([(facetIndex 21)]))
 (.leaf ([(facetIndex 22)])))
 (.branch 24
 (.leaf ([(facetIndex 23)]))
 (.leaf ([(facetIndex 24)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "18bdab49ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 25
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 53), (facetIndex 54), (facetIndex 55)]))
 (.branch 2
 (.leaf ([(facetIndex 63), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 44), (facetIndex 46), (facetIndex 48)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 33), (facetIndex 45), (facetIndex 47), (facetIndex 49)]))
 (.leaf ([(facetIndex 32), (facetIndex 43), (facetIndex 50), (facetIndex 51), (facetIndex 52)])))
 (.branch 6
 (.leaf ([(facetIndex 26), (facetIndex 27), (facetIndex 29), (facetIndex 30), (facetIndex 31), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37)]))
 (.leaf ([(facetIndex 25), (facetIndex 28), (facetIndex 38), (facetIndex 39)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "920000000491a69a892dadb5cb6eb7z13;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped1_0000 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
def grouped1_0002 : List Nat := [12, 13, 14]
def grouped1_0003 : List Nat := [12, 13, 14, 15, 16, 17]
def grouped1_0004 : List Nat := [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
def grouped1_0005 : List Nat := [15]
def grouped1_0006 : List Nat := [15, 16, 17]
def grouped1_0007 : List Nat := [16]
def grouped1_0008 : List Nat := [16, 17]
def grouped1_0009 : List Nat := [17]
def grouped1_0010 : List Nat := [18]
def grouped1_0011 : List Nat := [18, 19, 20]
def grouped1_0012 : List Nat := [18, 19, 20, 21, 22, 23, 24]
def grouped1_0013 : List Nat := [19]
def grouped1_0014 : List Nat := [19, 20]
def grouped1_0015 : List Nat := [20]
def grouped1_0016 : List Nat := [21, 22]
def grouped1_0017 : List Nat := [21, 22, 23, 24]
def grouped1_0018 : List Nat := [23]
def grouped1_0019 : List Nat := [23, 24]
def grouped1_0020 : List Nat := [24]
def grouped2_0021 : List Nat := [0]
def grouped2_0022 : List Nat := [0, 1, 2]
def grouped2_0024 : List Nat := [1]
def grouped2_0025 : List Nat := [1, 2]
def grouped2_0026 : List Nat := [2]
def grouped2_0027 : List Nat := [3]
def grouped2_0028 : List Nat := [3, 4]
def grouped2_0029 : List Nat := [3, 4, 5, 6]
def grouped2_0030 : List Nat := [4]
def grouped2_0031 : List Nat := [5]
def grouped2_0032 : List Nat := [5, 6]
def grouped2_0033 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00029.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"kind\":1,\"index\":16},{\"tag\":\"group\",\"kind\":1,\"index\":17},{\"tag\":\"group\",\"kind\":1,\"index\":18},{\"tag\":\"group\",\"kind\":1,\"index\":19},{\"tag\":\"group\",\"kind\":1,\"index\":24},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0008\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0006\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0017\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0025\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0022\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0028\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0032\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0029\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00029.record005" 70

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00029.record005" "{\"ridges\":[[10,35],[19,608],[24,608],[28,35],[31,546],[34,578],[40,97],[41,35],[44,97],[48,97],[49,97],[61,97],[63,56],[64,140],[65,276],[71,232],[72,368]],\"owners\":[[40,97,[19,62],[10,44,48,49,61]],[44,97,[19,61],[10,40,48,49,62]],[48,97,[19,62],[10,40,44,49,61]],[49,97,[19,61],[10,40,44,48,62]],[61,97,[10,19,44,49,62],[40,48]],[31,546,[24],[11,42,46,66,67]],[34,578,[24],[14,51,52,69,70]],[64,140,[16],[21,54]],[65,276,[17],[22,55]],[63,56,[18],[23,53]],[19,608,[24],[]],[24,608,[19],[]],[71,232,[61],[]],[72,368,[62],[]]],\"edges\":[[35,[10,19,24,40,44,48,49,61,62,71,72]]],\"groupings\":[1,2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00029.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00029.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-15,-8],[-15,-9],[-15,-11],[-15,-12],[-17,-15],[-18,-15],[-19,-15],[-22,-1],[-23,-7],[-23,-20],[-23,-21],[-24,-1],[-26,-1],[-27,-26],[-28,-1],[-29,-26],[-30,-1],[-31,-14],[-31,-25],[-32,-31],[-33,-31],[-34,-31],[-36,-27],[-36,-29],[-1,-10,-23],[-22,5,36],[-26,5,35],[-30,5,36],[-31,5,35],[-35,1,5,26,31,36],[-13,6],[-16,6],[-38,2],[-39,3],[-37,4],[-5,6],[-6,5],[-40,35],[-41,36],[-2,42],[-3,43],[-4,44],[-5,45],[-6,46],[-43,47],[-42,47],[-47,48],[-48,49],[-45,50],[-50,51],[-44,-50,52],[-46,53],[-53,54],[-51,-54,55],[-52,-54,56],[-56,57],[-49,-55,57],[-57,58],[-58],[-59,37,38,39],[-60,22,23,24,26,28,30],[-61,15,27,29,31],[-62,14,25,32,33,34],[-63,8,9,11,12,13,16,17,18,19],[-64,7,10,20,21],[-65,59],[-65,60],[-66,65],[-67,61],[-67,62],[-68,63],[-68,64],[-69,67],[-69,68],[-70,66],[-70,69],[70],[1,5,6,22,26,30,31,35,36,40,41]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"index\":16,\"kind\":1},{\"tag\":\"group\",\"index\":17,\"kind\":1},{\"tag\":\"group\",\"index\":18,\"kind\":1},{\"tag\":\"group\",\"index\":19,\"kind\":1},{\"tag\":\"group\",\"index\":24,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":33,\"b\":26},{\"tag\":\"incompatible\",\"a\":33,\"b\":27},{\"tag\":\"incompatible\",\"a\":33,\"b\":29},{\"tag\":\"incompatible\",\"a\":33,\"b\":30},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":36,\"b\":33},{\"tag\":\"incompatible\",\"a\":37,\"b\":33},{\"tag\":\"incompatible\",\"a\":40,\"b\":10},{\"tag\":\"incompatible\",\"a\":41,\"b\":25},{\"tag\":\"incompatible\",\"a\":41,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":10},{\"tag\":\"incompatible\",\"a\":44,\"b\":10},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":10},{\"tag\":\"incompatible\",\"a\":47,\"b\":44},{\"tag\":\"incompatible\",\"a\":48,\"b\":10},{\"tag\":\"incompatible\",\"a\":49,\"b\":32},{\"tag\":\"incompatible\",\"a\":49,\"b\":43},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":62,\"b\":45},{\"tag\":\"incompatible\",\"a\":62,\"b\":47},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[10,28,41]},{\"tag\":\"mate\",\"ridge\":97,\"a\":40,\"owners\":[19,62]},{\"tag\":\"mate\",\"ridge\":97,\"a\":44,\"owners\":[19,61]},{\"tag\":\"mate\",\"ridge\":97,\"a\":48,\"owners\":[19,62]},{\"tag\":\"mate\",\"ridge\":97,\"a\":49,\"owners\":[19,61]},{\"tag\":\"mate\",\"ridge\":97,\"a\":61,\"owners\":[10,19,44,49,62]},{\"tag\":\"mate\",\"ridge\":546,\"a\":31,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":578,\"a\":34,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":140,\"a\":64,\"owners\":[16]},{\"tag\":\"mate\",\"ridge\":276,\"a\":65,\"owners\":[17]},{\"tag\":\"mate\",\"ridge\":56,\"a\":63,\"owners\":[18]},{\"tag\":\"mate\",\"ridge\":608,\"a\":19,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":608,\"a\":24,\"owners\":[19]},{\"tag\":\"mate\",\"ridge\":232,\"a\":71,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":368,\"a\":72,\"owners\":[62]},{\"tag\":\"group_take\",\"kind\":1,\"index\":16,\"member\":16,\"full_literals\":[-2,42]},{\"tag\":\"group_take\",\"kind\":1,\"index\":17,\"member\":17,\"full_literals\":[-3,43]},{\"tag\":\"group_take\",\"kind\":1,\"index\":18,\"member\":18,\"full_literals\":[-4,44]},{\"tag\":\"group_take\",\"kind\":1,\"index\":19,\"member\":19,\"full_literals\":[-5,45]},{\"tag\":\"group_take\",\"kind\":1,\"index\":24,\"member\":24,\"full_literals\":[-6,46]},{\"tag\":\"merge\",\"left\":[16],\"right\":[17],\"left_name\":\"grouped1_0007\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,47],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16],\"right\":[17],\"left_name\":\"grouped1_0007\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,47],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16,17],\"left_name\":\"grouped1_0005\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,48],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13,14],\"right\":[15,16,17],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,49],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[19],\"right\":[20],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"grouped1_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,50],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19,20],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,51],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19,20],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-50,52],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23],\"right\":[24],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,53],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22],\"right\":[23,24],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,54],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18,19,20],\"right\":[21,22,23,24],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-54,55],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18,19,20],\"right\":[21,22,23,24],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0012\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-54,56],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13,14,15,16,17],\"right\":[18,19,20,21,22,23,24],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0012\",\"joined_name\":\"grouped1_0004\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-56,57],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13,14,15,16,17],\"right\":[18,19,20,21,22,23,24],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0012\",\"joined_name\":\"grouped1_0004\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-49,-55,57],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11],\"right\":[12,13,14,15,16,17,18,19,20,21,22,23,24],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0004\",\"joined_name\":\"groupKind1\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":2,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[63,64,65],\"full_literals\":[-59,37,38,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[40,41,42,44,46,48],\"full_literals\":[-60,22,23,24,26,28,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[33,45,47,49],\"full_literals\":[-61,15,27,29,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[32,43,50,51,52],\"full_literals\":[-62,14,25,32,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[26,27,29,30,31,34,35,36,37],\"full_literals\":[-63,8,9,11,12,13,16,17,18,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[25,28,38,39],\"full_literals\":[-64,7,10,20,21]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0024\",\"right_name\":\"grouped2_0026\",\"joined_name\":\"grouped2_0025\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0024\",\"right_name\":\"grouped2_0026\",\"joined_name\":\"grouped2_0025\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0021\",\"right_name\":\"grouped2_0025\",\"joined_name\":\"grouped2_0022\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0027\",\"right_name\":\"grouped2_0030\",\"joined_name\":\"grouped2_0028\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0027\",\"right_name\":\"grouped2_0030\",\"joined_name\":\"grouped2_0028\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0031\",\"right_name\":\"grouped2_0033\",\"joined_name\":\"grouped2_0032\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0031\",\"right_name\":\"grouped2_0033\",\"joined_name\":\"grouped2_0032\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0028\",\"right_name\":\"grouped2_0032\",\"joined_name\":\"grouped2_0029\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-69,67,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0028\",\"right_name\":\"grouped2_0032\",\"joined_name\":\"grouped2_0029\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0022\",\"right_name\":\"grouped2_0029\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-70,66,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0022\",\"right_name\":\"grouped2_0029\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-70,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":35,\"owners\":[10,19,24,40,44,48,49,61,62,71,72]}]}"
  "p cnf 70 78\n-15 -8 0\n-15 -9 0\n-15 -11 0\n-15 -12 0\n-17 -15 0\n-18 -15 0\n-19 -15 0\n-22 -1 0\n-23 -7 0\n-23 -20 0\n-23 -21 0\n-24 -1 0\n-26 -1 0\n-27 -26 0\n-28 -1 0\n-29 -26 0\n-30 -1 0\n-31 -14 0\n-31 -25 0\n-32 -31 0\n-33 -31 0\n-34 -31 0\n-36 -27 0\n-36 -29 0\n-1 -10 -23 0\n-22 5 36 0\n-26 5 35 0\n-30 5 36 0\n-31 5 35 0\n-35 1 5 26 31 36 0\n-13 6 0\n-16 6 0\n-38 2 0\n-39 3 0\n-37 4 0\n-5 6 0\n-6 5 0\n-40 35 0\n-41 36 0\n-2 42 0\n-3 43 0\n-4 44 0\n-5 45 0\n-6 46 0\n-43 47 0\n-42 47 0\n-47 48 0\n-48 49 0\n-45 50 0\n-50 51 0\n-44 -50 52 0\n-46 53 0\n-53 54 0\n-51 -54 55 0\n-52 -54 56 0\n-56 57 0\n-49 -55 57 0\n-57 58 0\n-58 0\n-59 37 38 39 0\n-60 22 23 24 26 28 30 0\n-61 15 27 29 31 0\n-62 14 25 32 33 34 0\n-63 8 9 11 12 13 16 17 18 19 0\n-64 7 10 20 21 0\n-65 59 0\n-65 60 0\n-66 65 0\n-67 61 0\n-67 62 0\n-68 63 0\n-68 64 0\n-69 67 0\n-69 68 0\n-70 66 0\n-70 69 0\n70 0\n1 5 6 22 26 30 31 35 36 40 41 0\n"
  "79 -57 0 59 58 0\n80 -56 0 79 56 0\n81 66 0 77 75 0\n82 69 0 77 76 0\n83 65 0 81 68 0\n84 67 0 82 73 0\n85 68 0 82 74 0\n86 59 0 83 66 0\n87 60 0 83 67 0\n88 61 0 84 69 0\n89 62 0 84 70 0\n90 63 0 85 71 0\n91 64 0 85 72 0\n92 -6 55 0 37 44 43 52 49 53 50 54 0\n93 35 36 1 6 0 36 28 26 39 38 27 29 78 0\n94 -15 6 0 90 32 31 1 2 3 4 5 6 7 64 0\n95 -27 31 1 6 0 36 14 23 93 30 0\n96 31 1 6 0 88 94 36 95 62 16 24 93 30 0\n97 -31 0 89 18 19 20 21 22 63 0\n98 -1 0 87 91 8 12 13 15 17 61 9 10 11 25 65 0\n99 6 0 98 97 96 0\n100 5 0 99 37 0\n101 46 0 99 44 0\n102 55 0 99 92 0\n103 45 0 100 43 0\n104 53 0 101 52 0\n105 -49 0 102 79 57 0\n106 50 0 103 49 0\n107 54 0 104 53 0\n108 -48 0 105 48 0\n109 -52 0 107 80 55 0\n110 -47 0 108 47 0\n111 -44 0 109 106 51 0\n112 -43 0 110 45 0\n113 -42 0 110 46 0\n114 -4 0 111 42 0\n115 -3 0 112 41 0\n116 -2 0 113 40 0\n117 -37 0 114 35 0\n118 -39 0 115 34 0\n119 -38 0 116 33 0\n120 0 119 118 86 117 60 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00029.record005
