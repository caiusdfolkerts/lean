module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00133Frames
public import GraphInputsRow29Part00133Leaves
public import GraphInputsRow29Part00133Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00133.record026
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1786d174ab26c5b29c9715c4f0bc1f2e2b49723caaa9aa9a968ba1eaa699966a5a56559362d876a3a4e8b8ae1ba1e2785e0f9b15c4f15a5594e4b91e5a559595555352d475a364d5352d2b46d4749d1743db0d6338d5334d332cc73a2e4b2ac9b0ee8791d4749c6745c570de0f23c4f9286a16a86298968382e079615446916525295152542d074a318c9314c4b0ac1b21c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6db6db6d34d26d36d34924924d349b4924936da49249a49349a4926d2492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 53), (facetIndex 76), (facetIndex 105), (facetIndex 106)]))
 (.leaf ([(facetIndex 45), (facetIndex 72), (facetIndex 100), (facetIndex 102)])))
 (.branch 3
 (.leaf ([(facetIndex 63), (facetIndex 98), (facetIndex 112), (facetIndex 115)]))
 (.leaf ([(facetIndex 48), (facetIndex 64), (facetIndex 73), (facetIndex 78), (facetIndex 103), (facetIndex 108)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 88), (facetIndex 90), (facetIndex 109), (facetIndex 117)]))
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 61), (facetIndex 92), (facetIndex 95), (facetIndex 107)])))
 (.branch 7
 (.leaf ([(facetIndex 62), (facetIndex 91), (facetIndex 110), (facetIndex 111), (facetIndex 114), (facetIndex 116)]))
 (.branch 8
 (.leaf ([(facetIndex 94), (facetIndex 113)]))
 (.leaf ([(facetIndex 104), (facetIndex 118)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "846267266435008310102005705640400000000030000310000000326500000000000030010000055z26;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00133.record026" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00133.record026" 61

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00133.record026" "{\"ridges\":[[14,276],[19,336],[26,644],[29,578],[35,276],[40,644],[44,578],[48,306],[50,336],[53,705],[57,276],[62,581],[66,276],[67,276],[68,276],[73,312],[74,336],[77,336],[78,432],[86,584],[87,644],[93,644],[96,644],[99,578],[101,578],[105,720],[106,736],[111,596],[114,612]],\"owners\":[[14,276,[90,91,109,110,116,117],[35,57,66,67,68]],[35,276,[109,110,116,117],[14,57,66,67,68,90,91]],[57,276,[90,91,116,117],[14,35,66,67,68,109,110]],[66,276,[91,110],[14,35,57,67,68,90,109,116,117]],[67,276,[90,109,117],[14,35,57,66,68,91,110,116]],[68,276,[90,91,109,110,116],[14,35,57,66,67,117]],[19,336,[91,104,110,116,118],[50,67,74,77]],[50,336,[110,116,118],[19,67,74,77,91,104]],[74,336,[91,104,116],[19,50,67,77,110,118]],[77,336,[91,110],[19,50,67,74,104,116,118]],[26,644,[63,112,115],[40,87,93,96]],[40,644,[112,115],[26,63,87,93,96]],[87,644,[],[26,40,63,93,96,112,115]],[93,644,[63,115],[26,40,87,96,112]],[96,644,[63,112],[26,40,87,93,115]],[29,578,[39,53,92,95,105,106],[44,86,99,101]],[44,578,[92,95,105,106],[29,39,53,86,99,101]],[99,578,[39,53,95,106],[29,44,86,92,101,105]],[101,578,[39,53,92,105],[29,44,86,95,99,106]],[86,584,[],[29,44,62,99,101,111,114]],[62,581,[39],[]],[48,306,[90,104],[]],[53,705,[],[]],[73,312,[109,118],[]],[78,432,[117],[]],[111,596,[92],[]],[114,612,[95],[]],[105,720,[],[]],[106,736,[],[]]],\"edges\":[[33,[14,19,35,48,50,57,66,67,68,73,74,77,78,90,91,104,109,110,116,117,118]],[41,[29,39,44,53,62,86,92,95,99,101,105,106,111,114]],[43,[26,40,45,53,63,87,93,96,100,102,105,106,112,115]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00133.record026" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00133.record026\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,25,26,38,39,44,45],[-5,38,39,44,45],[-13,25,26,44,45],[-16,26,39],[-17,25,38,45],[-18,25,26,38,39,44],[-2,26,35,39,44,46],[-11,39,44,46],[-20,26,35,44],[-21,26,39],[-3,15,41,43],[-7,41,43],[-24],[-28,15,43],[-30,15,41],[-4,6,12,27,29,36,37],[-8,27,29,36,37],[-31,6,12,29,37],[-33,6,12,27,36],[-23],[-14,6],[-10,25,35],[-12],[-19,38,46],[-22,45],[-40,27],[-42,29],[-36],[-37],[-9,47],[-32,47],[-34,47],[-15,48],[-41,48],[-43,48],[-25,49],[-38,49],[-45,49],[-6,50],[-27,50],[-29,50],[-26,51],[-39,51],[-44,51],[-35,52],[-46,52],[-47,53],[-48,54],[-54,55],[-53,55],[-50,56],[-49,-50,57],[-52,58],[-58,59],[-51,59],[-56,-59,60],[-57,60],[-55,-60,61],[-61],[1,2,5,10,11,13,16,17,18,19,20,21,22,25,26,35,38,39,44,45,46],[4,6,8,12,14,23,27,29,31,33,36,37,40,42],[3,7,9,12,15,24,28,30,32,34,36,37,41,43]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":276,\"a\":14,\"owners\":[90,91,109,110,116,117]},{\"tag\":\"mate\",\"ridge\":276,\"a\":35,\"owners\":[109,110,116,117]},{\"tag\":\"mate\",\"ridge\":276,\"a\":57,\"owners\":[90,91,116,117]},{\"tag\":\"mate\",\"ridge\":276,\"a\":66,\"owners\":[91,110]},{\"tag\":\"mate\",\"ridge\":276,\"a\":67,\"owners\":[90,109,117]},{\"tag\":\"mate\",\"ridge\":276,\"a\":68,\"owners\":[90,91,109,110,116]},{\"tag\":\"mate\",\"ridge\":336,\"a\":19,\"owners\":[91,104,110,116,118]},{\"tag\":\"mate\",\"ridge\":336,\"a\":50,\"owners\":[110,116,118]},{\"tag\":\"mate\",\"ridge\":336,\"a\":74,\"owners\":[91,104,116]},{\"tag\":\"mate\",\"ridge\":336,\"a\":77,\"owners\":[91,110]},{\"tag\":\"mate\",\"ridge\":644,\"a\":26,\"owners\":[63,112,115]},{\"tag\":\"mate\",\"ridge\":644,\"a\":40,\"owners\":[112,115]},{\"tag\":\"mate\",\"ridge\":644,\"a\":87,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":644,\"a\":93,\"owners\":[63,115]},{\"tag\":\"mate\",\"ridge\":644,\"a\":96,\"owners\":[63,112]},{\"tag\":\"mate\",\"ridge\":578,\"a\":29,\"owners\":[39,53,92,95,105,106]},{\"tag\":\"mate\",\"ridge\":578,\"a\":44,\"owners\":[92,95,105,106]},{\"tag\":\"mate\",\"ridge\":578,\"a\":99,\"owners\":[39,53,95,106]},{\"tag\":\"mate\",\"ridge\":578,\"a\":101,\"owners\":[39,53,92,105]},{\"tag\":\"mate\",\"ridge\":584,\"a\":86,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":581,\"a\":62,\"owners\":[39]},{\"tag\":\"mate\",\"ridge\":306,\"a\":48,\"owners\":[90,104]},{\"tag\":\"mate\",\"ridge\":705,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":312,\"a\":73,\"owners\":[109,118]},{\"tag\":\"mate\",\"ridge\":432,\"a\":78,\"owners\":[117]},{\"tag\":\"mate\",\"ridge\":596,\"a\":111,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":612,\"a\":114,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":720,\"a\":105,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":106,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":45,\"full_literals\":[-9,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":100,\"full_literals\":[-32,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":102,\"full_literals\":[-34,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":63,\"full_literals\":[-15,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":112,\"full_literals\":[-41,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":115,\"full_literals\":[-43,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":90,\"full_literals\":[-25,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":109,\"full_literals\":[-38,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":117,\"full_literals\":[-45,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":39,\"full_literals\":[-6,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":92,\"full_literals\":[-27,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":95,\"full_literals\":[-29,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":91,\"full_literals\":[-26,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":110,\"full_literals\":[-39,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":116,\"full_literals\":[-44,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":104,\"full_literals\":[-35,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":118,\"full_literals\":[-46,52]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-50,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-55,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[14,19,35,48,50,57,66,67,68,73,74,77,78,90,91,104,109,110,116,117,118]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[29,39,44,53,62,86,92,95,99,101,105,106,111,114]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[26,40,45,53,63,87,93,96,100,102,105,106,112,115]}]}"
  "63 4 6 8 14 27 29 31 33 40 42 0 23 20 28 29 61 0\n64 3 7 9 15 28 30 32 34 41 43 0 23 13 28 29 62 0\n65 55 0 49 50 48 47 33 34 35 30 31 32 12 15 14 11 64 0\n66 -60 0 65 59 58 0\n67 -57 0 66 57 0\n68 50 0 28 29 23 39 40 41 21 17 26 16 19 27 18 63 0\n69 56 0 68 51 0\n70 -49 0 68 67 52 0\n71 -59 0 69 66 56 0\n72 -25 0 70 36 0\n73 -38 0 70 37 0\n74 -45 0 70 38 0\n75 -58 0 71 54 0\n76 -51 0 71 55 0\n77 -17 0 73 72 74 5 0\n78 -22 0 74 25 0\n79 -52 0 75 53 0\n80 -26 0 76 42 0\n81 -39 0 76 43 0\n82 -44 0 76 44 0\n83 -35 0 79 45 0\n84 -46 0 79 46 0\n85 -21 0 80 81 10 0\n86 -16 0 81 80 4 0\n87 -2 0 81 83 80 82 84 7 0\n88 -5 0 81 73 82 74 2 0\n89 -11 0 82 81 84 8 0\n90 -13 0 82 80 72 74 3 0\n91 -20 0 82 83 80 9 0\n92 -1 0 82 80 72 81 73 74 1 0\n93 -18 0 82 80 72 81 73 6 0\n94 -10 0 83 72 22 0\n95 -19 0 84 73 24 0\n96 0 86 93 88 94 92 89 87 77 90 95 91 85 78 72 80 83 73 81 82 74 84 60 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00133.record026_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00133.record026
