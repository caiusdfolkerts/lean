module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00043Frames
public import GraphInputsRow26Part00043Leaves
public import GraphInputsRow26Part00043Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00043.record028
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "b52b4b313cb28ea5693a1eac6a9b1695a364da8e938ce4b8ae4785e0fad13c4e9565391e6c5a5655355352d58d3352d4745d0f6c338e5354d331cd4b32d2b2ac6b46c5b0ee8791cc749ca785c5723c4f07cac94a16458364382e324a9295150d50d2342d44c530cd0b12c2b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6924db4934da6db6da4924d36924924924db492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 49), (facetIndex 52), (facetIndex 55), (facetIndex 56)]))
 (.branch 2
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46)]))
 (.leaf ([(facetIndex 27), (facetIndex 53), (facetIndex 54), (facetIndex 64)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 67), (facetIndex 70), (facetIndex 71)]))
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 78)])))
 (.branch 6
 (.leaf ([(facetIndex 26), (facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 42)]))
 (.leaf ([(facetIndex 25), (facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 51), (facetIndex 69)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1248006f0602000000090c0004936db76c0000957z13;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 50), (facetIndex 61), (facetIndex 62), (facetIndex 63)]))
 (.leaf ([(facetIndex 68), (facetIndex 81), (facetIndex 82), (facetIndex 83)])))
 (.branch 3
 (.leaf ([(facetIndex 86)]))
 (.leaf ([(facetIndex 57), (facetIndex 59), (facetIndex 65), (facetIndex 88)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 32), (facetIndex 34), (facetIndex 47), (facetIndex 74), (facetIndex 79)]))
 (.leaf ([(facetIndex 48), (facetIndex 72), (facetIndex 84), (facetIndex 85)])))
 (.branch 7
 (.leaf ([(facetIndex 33), (facetIndex 73), (facetIndex 80), (facetIndex 89)]))
 (.branch 8
 (.leaf ([(facetIndex 58), (facetIndex 87)]))
 (.leaf ([(facetIndex 60), (facetIndex 66)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "6372551116400004650001083000083730000000054000000000000464z20;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [1, 2]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [3]
def grouped2_0007 : List Nat := [3, 4]
def grouped2_0008 : List Nat := [3, 4, 5, 6]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00043.record028" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":3}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00043.record028" 68

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00043.record028" "{\"ridges\":[[0,14],[11,140],[12,268],[19,14],[22,532],[23,592],[29,532],[34,133],[34,644],[42,265],[46,592],[48,704],[51,13],[54,133],[54,140],[57,133],[57,212],[59,644],[60,644],[64,200],[65,240],[66,657],[69,14],[70,14],[70,140],[73,14],[76,532],[77,532],[78,532],[79,674],[80,644],[85,650],[87,140],[87,588],[88,688],[89,212],[89,644]],\"owners\":[[51,13,[0,10,11,26,53],[12,25,49,50]],[42,265,[12,51,52,54,62],[6,37,40,63]],[12,268,[19,69,71,86],[51,52,54]],[64,200,[72,85,87],[17,41,53,84]],[22,532,[58,59,88,89],[29,76,77,78]],[29,532,[88,89],[22,58,59,76,77,78]],[76,532,[58,59,89],[22,29,77,78,88]],[77,532,[59,88],[22,29,58,76,78,89]],[78,532,[58,59,88,89],[22,29,76,77]],[23,592,[58,66,89],[46,77]],[46,592,[89],[23,58,66,77]],[34,644,[87,88,89],[59,60,74,79,80]],[59,644,[74,79,80,87],[34,60,88,89]],[60,644,[74,79,88],[34,59,80,87,89]],[80,644,[59,88],[34,60,74,79,87,89]],[89,644,[34,74,79],[59,60,80,87,88]],[48,704,[87,89],[60,66,80,85]],[57,212,[89],[]],[89,212,[57],[]],[66,657,[59],[]],[65,240,[],[]],[87,588,[73],[]],[85,650,[74],[]],[79,674,[],[]],[88,688,[],[]]],\"edges\":[[34,[22,23,29,46,58,59,66,76,77,78,88,89]],[43,[34,48,59,60,66,74,79,80,85,87,88,89]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00043.record028" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00043.record028\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-10],[-20,-13],[-29,-25],[-32,-28],[-34,-30],[-34,-31],[-36,-13],[-37,-18],[-40,-8],[-40,-15],[-40,-16],[-40,-17],[-40,-26],[-41,-40],[-42,-2],[-42,-10],[-42,-12],[-42,-19],[-42,-21],[-42,-25],[-42,-27],[-43,-13],[-43,-27],[-44,-32],[-44,-43],[-45,-43],[-46,-42],[-46,-43],[-51,-10],[-51,-12],[-51,-28],[-51,-42],[-53,-42],[-54,-9],[-54,-28],[-54,-32],[-54,-33],[-26,1,2,3,9,28],[-1,-42,-45],[-5,-42,-45],[-41,-42,-45],[-22,4,26,27,29,36],[-14,-29,-32],[-3,-42,-54],[-29,-42,-54],[-4,5,41,43,53],[-37,44,52,54],[-6,33,34,55,56],[-11,55,56],[-47,33,34,56],[-48,34,55],[-49,33,34,55,56],[-7,33,39,56],[-23,56],[-14,54,55,56],[-34,46,50,51,54],[-35,46,50,55],[-51,34,55],[-56,14,46,50],[-24,54,56],[-32,56],[-56,32],[-39,34],[-38],[-54,45],[-52,46],[-50],[-55],[-57,12,13,25,27,30,31],[-58,10,28,29,37],[-59,40,42,43],[-60,9,18,19,20,21,22],[-61,8,15,16,17,26,41],[-62,58],[-63,57],[-63,62],[-64,59],[-65,60],[-65,61],[-66,64],[-66,65],[-67,63],[-67,66],[67],[-68,32,34,38,55],[-32,68],[-34,68],[6,7,11,23,33,34,39,47,48,49,55,56],[14,24,34,35,39,46,50,51,52,54,55,56]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":34,\"b\":27},{\"tag\":\"incompatible\",\"a\":40,\"b\":31},{\"tag\":\"incompatible\",\"a\":54,\"b\":49},{\"tag\":\"incompatible\",\"a\":57,\"b\":53},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":56},{\"tag\":\"incompatible\",\"a\":62,\"b\":31},{\"tag\":\"incompatible\",\"a\":64,\"b\":38},{\"tag\":\"incompatible\",\"a\":67,\"b\":25},{\"tag\":\"incompatible\",\"a\":67,\"b\":35},{\"tag\":\"incompatible\",\"a\":67,\"b\":36},{\"tag\":\"incompatible\",\"a\":67,\"b\":37},{\"tag\":\"incompatible\",\"a\":67,\"b\":51},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":10},{\"tag\":\"incompatible\",\"a\":70,\"b\":27},{\"tag\":\"incompatible\",\"a\":70,\"b\":30},{\"tag\":\"incompatible\",\"a\":70,\"b\":39},{\"tag\":\"incompatible\",\"a\":70,\"b\":41},{\"tag\":\"incompatible\",\"a\":70,\"b\":49},{\"tag\":\"incompatible\",\"a\":70,\"b\":52},{\"tag\":\"incompatible\",\"a\":71,\"b\":31},{\"tag\":\"incompatible\",\"a\":71,\"b\":52},{\"tag\":\"incompatible\",\"a\":72,\"b\":57},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":71},{\"tag\":\"incompatible\",\"a\":80,\"b\":27},{\"tag\":\"incompatible\",\"a\":80,\"b\":30},{\"tag\":\"incompatible\",\"a\":80,\"b\":53},{\"tag\":\"incompatible\",\"a\":80,\"b\":70},{\"tag\":\"incompatible\",\"a\":86,\"b\":70},{\"tag\":\"incompatible\",\"a\":87,\"b\":26},{\"tag\":\"incompatible\",\"a\":87,\"b\":53},{\"tag\":\"incompatible\",\"a\":87,\"b\":57},{\"tag\":\"incompatible\",\"a\":87,\"b\":58},{\"tag\":\"mate\",\"ridge\":13,\"a\":51,\"owners\":[0,10,11,26,53]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[0,70,73]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[19,70,73]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[69,70,73]},{\"tag\":\"mate\",\"ridge\":265,\"a\":42,\"owners\":[12,51,52,54,62]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[34,54,57]},{\"tag\":\"three\",\"ridge\":140,\"vertices\":[11,70,87]},{\"tag\":\"three\",\"ridge\":140,\"vertices\":[54,70,87]},{\"tag\":\"mate\",\"ridge\":268,\"a\":12,\"owners\":[19,69,71,86]},{\"tag\":\"mate\",\"ridge\":200,\"a\":64,\"owners\":[72,85,87]},{\"tag\":\"mate\",\"ridge\":532,\"a\":22,\"owners\":[58,59,88,89]},{\"tag\":\"mate\",\"ridge\":532,\"a\":29,\"owners\":[88,89]},{\"tag\":\"mate\",\"ridge\":532,\"a\":76,\"owners\":[58,59,89]},{\"tag\":\"mate\",\"ridge\":532,\"a\":77,\"owners\":[59,88]},{\"tag\":\"mate\",\"ridge\":532,\"a\":78,\"owners\":[58,59,88,89]},{\"tag\":\"mate\",\"ridge\":592,\"a\":23,\"owners\":[58,66,89]},{\"tag\":\"mate\",\"ridge\":592,\"a\":46,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":644,\"a\":34,\"owners\":[87,88,89]},{\"tag\":\"mate\",\"ridge\":644,\"a\":59,\"owners\":[74,79,80,87]},{\"tag\":\"mate\",\"ridge\":644,\"a\":60,\"owners\":[74,79,88]},{\"tag\":\"mate\",\"ridge\":644,\"a\":80,\"owners\":[59,88]},{\"tag\":\"mate\",\"ridge\":644,\"a\":89,\"owners\":[34,74,79]},{\"tag\":\"mate\",\"ridge\":704,\"a\":48,\"owners\":[87,89]},{\"tag\":\"mate\",\"ridge\":212,\"a\":57,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":212,\"a\":89,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":657,\"a\":66,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":240,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":588,\"a\":87,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":650,\"a\":85,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":674,\"a\":79,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":688,\"a\":88,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[30,31,49,52,55,56],\"full_literals\":[-57,12,13,25,27,30,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[27,53,54,64],\"full_literals\":[-58,10,28,29,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[67,70,71],\"full_literals\":[-59,40,42,43]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[26,38,39,40,41,42],\"full_literals\":[-60,9,18,19,20,21,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[25,35,36,37,51,69],\"full_literals\":[-61,8,15,16,17,26,41]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-63,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-67,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-67,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[57,59,65,88],\"full_literals\":[-68,32,34,38,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":57,\"full_literals\":[-32,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":59,\"full_literals\":[-34,68]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[22,23,29,46,58,59,66,76,77,78,88,89]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[34,48,59,60,66,74,79,80,85,87,88,89]}]}"
  "p cnf 68 89\n-14 -10 0\n-20 -13 0\n-29 -25 0\n-32 -28 0\n-34 -30 0\n-34 -31 0\n-36 -13 0\n-37 -18 0\n-40 -8 0\n-40 -15 0\n-40 -16 0\n-40 -17 0\n-40 -26 0\n-41 -40 0\n-42 -2 0\n-42 -10 0\n-42 -12 0\n-42 -19 0\n-42 -21 0\n-42 -25 0\n-42 -27 0\n-43 -13 0\n-43 -27 0\n-44 -32 0\n-44 -43 0\n-45 -43 0\n-46 -42 0\n-46 -43 0\n-51 -10 0\n-51 -12 0\n-51 -28 0\n-51 -42 0\n-53 -42 0\n-54 -9 0\n-54 -28 0\n-54 -32 0\n-54 -33 0\n-26 1 2 3 9 28 0\n-1 -42 -45 0\n-5 -42 -45 0\n-41 -42 -45 0\n-22 4 26 27 29 36 0\n-14 -29 -32 0\n-3 -42 -54 0\n-29 -42 -54 0\n-4 5 41 43 53 0\n-37 44 52 54 0\n-6 33 34 55 56 0\n-11 55 56 0\n-47 33 34 56 0\n-48 34 55 0\n-49 33 34 55 56 0\n-7 33 39 56 0\n-23 56 0\n-14 54 55 56 0\n-34 46 50 51 54 0\n-35 46 50 55 0\n-51 34 55 0\n-56 14 46 50 0\n-24 54 56 0\n-32 56 0\n-56 32 0\n-39 34 0\n-38 0\n-54 45 0\n-52 46 0\n-50 0\n-55 0\n-57 12 13 25 27 30 31 0\n-58 10 28 29 37 0\n-59 40 42 43 0\n-60 9 18 19 20 21 22 0\n-61 8 15 16 17 26 41 0\n-62 58 0\n-63 57 0\n-63 62 0\n-64 59 0\n-65 60 0\n-65 61 0\n-66 64 0\n-66 65 0\n-67 63 0\n-67 66 0\n67 0\n-68 32 34 38 55 0\n-32 68 0\n-34 68 0\n6 7 11 23 33 34 39 47 48 49 55 56 0\n14 24 34 35 39 46 50 51 52 54 55 56 0\n"
  "90 63 0 84 82 0\n91 66 0 84 83 0\n92 57 0 90 75 0\n93 62 0 90 76 0\n94 64 0 91 80 0\n95 65 0 91 81 0\n96 58 0 93 74 0\n97 59 0 94 77 0\n98 60 0 95 78 0\n99 61 0 95 79 0\n100 -68 32 34 0 64 68 85 0\n101 6 7 11 23 33 34 39 47 48 49 56 0 68 88 0\n102 14 24 34 35 39 46 51 52 54 56 0 67 68 89 0\n103 -40 0 99 9 10 11 12 13 14 73 0\n104 -46 0 103 97 27 28 71 0\n105 -35 0 104 67 68 57 0\n106 -52 0 104 66 0\n107 54 68 0 68 104 105 106 87 63 58 86 62 55 60 102 0\n108 68 0 68 86 87 107 62 51 63 37 54 49 48 50 52 53 101 0\n109 -54 -34 0 103 97 92 96 98 6 5 34 35 65 26 71 15 16 17 18 19 20 21 33 39 40 41 44 45 38 69 46 70 2 7 42 8 72 0\n110 -34 0 104 67 103 97 92 106 96 5 6 109 56 29 30 31 32 71 22 23 25 69 47 3 70 0\n111 32 0 110 108 100 0\n112 -28 0 111 4 0\n113 -44 0 111 24 0\n114 -54 0 111 36 0\n115 56 0 111 61 0\n116 -37 0 113 106 114 47 0\n117 14 0 115 104 67 59 0\n118 -10 0 117 1 0\n119 -29 0 117 111 43 0\n120 0 119 118 96 112 116 70 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00043.record028_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00043.record028
