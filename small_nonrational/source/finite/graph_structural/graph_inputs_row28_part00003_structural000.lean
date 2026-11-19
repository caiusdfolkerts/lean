module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow28Part00003Frames
public import GraphInputsRow28Part00003Leaves
public import GraphInputsRow28Part00003Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00003.record077
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f07c2e87ae1b46719a6558b61db0ea398e9394e33a2e1ba1e278b91e785d15c5695552d475c368d6364d534cd8b46d8749de0f4370da354cb31cf0ba2d8b92d4b32e2b1ae1b26e8791cc789d2719e1745c9743cac1703c2a85a0eb0661946298560da0e2384e0b81e2a4590e70561545294550d60d2344d0b41dc0d8350ca314c3382c8b12c2b06e0741c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "492492492492492492492492492492492492492492492492491249249249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 51), (facetIndex 53), (facetIndex 56), (facetIndex 57), (facetIndex 71), (facetIndex 88), (facetIndex 107)]))
 (.leaf ([(facetIndex 66), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 61), (facetIndex 69), (facetIndex 78), (facetIndex 86), (facetIndex 93), (facetIndex 97), (facetIndex 105), (facetIndex 112), (facetIndex 114)]))
 (.branch 4
 (.leaf ([(facetIndex 50), (facetIndex 59), (facetIndex 70), (facetIndex 76), (facetIndex 87), (facetIndex 94), (facetIndex 95), (facetIndex 106), (facetIndex 113), (facetIndex 115)]))
 (.leaf ([(facetIndex 49), (facetIndex 77), (facetIndex 79), (facetIndex 80), (facetIndex 81), (facetIndex 82), (facetIndex 83), (facetIndex 84), (facetIndex 85)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 54), (facetIndex 89), (facetIndex 90), (facetIndex 91), (facetIndex 92)]))
 (.leaf ([(facetIndex 96), (facetIndex 98), (facetIndex 99), (facetIndex 100), (facetIndex 101), (facetIndex 102), (facetIndex 103), (facetIndex 104)])))
 (.branch 8
 (.leaf ([(facetIndex 108), (facetIndex 109), (facetIndex 110), (facetIndex 111)]))
 (.branch 9
 (.leaf ([(facetIndex 60), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 67), (facetIndex 68)]))
 (.leaf ([(facetIndex 52), (facetIndex 55), (facetIndex 58)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3232777703266666662633255550324444444243111103288188882839009509034z31;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0002 : List Nat := [5]
def grouped2_0003 : List Nat := [5, 6]
def grouped2_0004 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0005 : List Nat := [6]
def grouped2_0006 : List Nat := [7]
def grouped2_0007 : List Nat := [7, 8, 9]
def grouped2_0008 : List Nat := [8]
def grouped2_0009 : List Nat := [8, 9]
def grouped2_0010 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00003.record077" "{\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00003.record077" 45

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00003.record077" "{\"ridges\":[[15,321],[15,322],[16,386],[17,769],[17,770],[26,324],[27,388],[28,772],[40,324],[42,772],[64,321],[64,322],[66,386],[68,769],[68,770],[71,321],[71,322],[72,386],[73,321],[73,322],[73,386],[74,321],[74,322],[74,769],[74,770],[75,386],[75,769],[75,770],[81,324],[83,388],[85,772],[88,324],[89,388],[90,324],[90,388],[91,324],[91,772],[92,388],[92,772],[100,324],[107,324],[108,388]],\"owners\":[[15,321,[26,81,88,90,91],[64,71,73,74]],[64,321,[26,88,90,91],[15,71,73,74,81]],[71,321,[26,81,90,91],[15,64,73,74,88]],[73,321,[26,81,88,91],[15,64,71,74,90]],[74,321,[26,81,88,90],[15,64,71,73,91]],[15,322,[40,100,107,109,110],[64,71,73,74]],[64,322,[40,107,109,110],[15,71,73,74,100]],[71,322,[40,100,109,110],[15,64,73,74,107]],[73,322,[40,100,107,110],[15,64,71,74,109]],[74,322,[40,100,107,109],[15,64,71,73,110]],[16,386,[41,102,108,109,111],[66,72,73,75]],[66,386,[41,108,109,111],[16,72,73,75,102]],[72,386,[41,102,109,111],[16,66,73,75,108]],[73,386,[41,102,108,111],[16,66,72,75,109]],[75,386,[41,102,108,109],[16,66,72,73,111]],[17,769,[28,85,91,92],[68,74,75]],[68,769,[28,91,92],[17,74,75,85]],[74,769,[28,85,92],[17,68,75,91]],[75,769,[28,85,91],[17,68,74,92]],[17,770,[42,104,110,111],[68,74,75]],[68,770,[42,110,111],[17,74,75,104]],[74,770,[42,104,111],[17,68,75,110]],[75,770,[42,104,110],[17,68,74,111]],[26,324,[40,100,107,109,110],[81,88,90,91]],[40,324,[26,81,88,90,91],[100,107,109,110]],[81,324,[40,107,109,110],[26,88,90,91,100]],[88,324,[40,100,109,110],[26,81,90,91,107]],[90,324,[40,100,107,110],[26,81,88,91,109]],[91,324,[40,100,107,109],[26,81,88,90,110]],[100,324,[26,88,90,91],[40,81,107,109,110]],[107,324,[26,81,90,91],[40,88,100,109,110]],[27,388,[41,102,108,109,111],[83,89,90,92]],[83,388,[41,108,109,111],[27,89,90,92,102]],[89,388,[41,102,109,111],[27,83,90,92,108]],[90,388,[41,102,108,111],[27,83,89,92,109]],[92,388,[41,102,108,109],[27,83,89,90,111]],[108,388,[27,83,90,92],[41,89,102,109,111]],[28,772,[42,104,110,111],[85,91,92]],[42,772,[28,85,91,92],[104,110,111]],[85,772,[42,110,111],[28,91,92,104]],[91,772,[42,104,111],[28,85,92,110]],[92,772,[42,104,110],[28,85,91,111]]],\"edges\":[[40,[15,26,40,64,71,73,74,81,88,90,91,100,107,109,110]],[42,[16,27,41,66,72,73,75,83,89,90,92,102,108,109,111]],[44,[17,28,42,68,74,75,85,91,92,104,110,111]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00003.record077" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00003.record077\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-27,-6],[-27,-24],[-28,-5],[-28,-23],[-28,-27],[-29,-4],[-29,-22],[-29,-25],[-29,-27],[-29,-28],[-32,-10],[-32,-12],[-32,-13],[-34,-11],[-34,-26],[-35,-9],[-36,-8],[-36,-31],[-36,-34],[-36,-35],[-37,-7],[-37,-30],[-37,-33],[-37,-35],[-37,-36],[-1,4,22,25,27,28],[-14,4,25,27,28],[-17,4,22,27,28],[-19,4,22,25,28],[-20,4,22,25,27],[-1,7,30,33,35,36],[-14,7,33,35,36],[-17,7,30,35,36],[-19,7,30,33,36],[-20,7,30,33,35],[-2,8,31,34,35,37],[-15,8,34,35,37],[-18,8,31,35,37],[-19,8,31,34,37],[-21,8,31,34,35],[-3,6,24,28,29],[-16,6,28,29],[-20,6,24,29],[-21,6,24,28],[-3,9,32,36,37],[-16,9,36,37],[-20,9,32,37],[-21,9,32,36],[-4,7,30,33,35,36],[-7,4,22,25,27,28],[-22,7,33,35,36],[-25,7,30,35,36],[-27,7,30,33,36],[-28,7,30,33,35],[-30,4,25,27,28],[-33,4,22,27,28],[-5,8,31,34,35,37],[-23,8,34,35,37],[-26,8,31,35,37],[-27,8,31,34,37],[-29,8,31,34,35],[-34,5,23,27,29],[-6,9,32,36,37],[-9,6,24,28,29],[-24,9,36,37],[-28,9,32,37],[-29,9,32,36],[-38,11,26,27,28,29],[-39,34,35,36,37],[-40,10,12,13],[-41,38],[-42,40],[-43,39],[-43,42],[-44,41],[-44,43],[-45,44],[45],[1,4,7,14,17,19,20,22,25,27,28,30,33,35,36],[2,5,8,15,18,19,21,23,26,27,29,31,34,35,37],[3,6,9,16,20,21,24,28,29,32,36,37]],\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":90,\"b\":28},{\"tag\":\"incompatible\",\"a\":90,\"b\":85},{\"tag\":\"incompatible\",\"a\":91,\"b\":27},{\"tag\":\"incompatible\",\"a\":91,\"b\":83},{\"tag\":\"incompatible\",\"a\":91,\"b\":90},{\"tag\":\"incompatible\",\"a\":92,\"b\":26},{\"tag\":\"incompatible\",\"a\":92,\"b\":81},{\"tag\":\"incompatible\",\"a\":92,\"b\":88},{\"tag\":\"incompatible\",\"a\":92,\"b\":90},{\"tag\":\"incompatible\",\"a\":92,\"b\":91},{\"tag\":\"incompatible\",\"a\":104,\"b\":52},{\"tag\":\"incompatible\",\"a\":104,\"b\":55},{\"tag\":\"incompatible\",\"a\":104,\"b\":58},{\"tag\":\"incompatible\",\"a\":108,\"b\":54},{\"tag\":\"incompatible\",\"a\":108,\"b\":89},{\"tag\":\"incompatible\",\"a\":109,\"b\":42},{\"tag\":\"incompatible\",\"a\":110,\"b\":41},{\"tag\":\"incompatible\",\"a\":110,\"b\":102},{\"tag\":\"incompatible\",\"a\":110,\"b\":108},{\"tag\":\"incompatible\",\"a\":110,\"b\":109},{\"tag\":\"incompatible\",\"a\":111,\"b\":40},{\"tag\":\"incompatible\",\"a\":111,\"b\":100},{\"tag\":\"incompatible\",\"a\":111,\"b\":107},{\"tag\":\"incompatible\",\"a\":111,\"b\":109},{\"tag\":\"incompatible\",\"a\":111,\"b\":110},{\"tag\":\"mate\",\"ridge\":321,\"a\":15,\"owners\":[26,81,88,90,91]},{\"tag\":\"mate\",\"ridge\":321,\"a\":64,\"owners\":[26,88,90,91]},{\"tag\":\"mate\",\"ridge\":321,\"a\":71,\"owners\":[26,81,90,91]},{\"tag\":\"mate\",\"ridge\":321,\"a\":73,\"owners\":[26,81,88,91]},{\"tag\":\"mate\",\"ridge\":321,\"a\":74,\"owners\":[26,81,88,90]},{\"tag\":\"mate\",\"ridge\":322,\"a\":15,\"owners\":[40,100,107,109,110]},{\"tag\":\"mate\",\"ridge\":322,\"a\":64,\"owners\":[40,107,109,110]},{\"tag\":\"mate\",\"ridge\":322,\"a\":71,\"owners\":[40,100,109,110]},{\"tag\":\"mate\",\"ridge\":322,\"a\":73,\"owners\":[40,100,107,110]},{\"tag\":\"mate\",\"ridge\":322,\"a\":74,\"owners\":[40,100,107,109]},{\"tag\":\"mate\",\"ridge\":386,\"a\":16,\"owners\":[41,102,108,109,111]},{\"tag\":\"mate\",\"ridge\":386,\"a\":66,\"owners\":[41,108,109,111]},{\"tag\":\"mate\",\"ridge\":386,\"a\":72,\"owners\":[41,102,109,111]},{\"tag\":\"mate\",\"ridge\":386,\"a\":73,\"owners\":[41,102,108,111]},{\"tag\":\"mate\",\"ridge\":386,\"a\":75,\"owners\":[41,102,108,109]},{\"tag\":\"mate\",\"ridge\":769,\"a\":17,\"owners\":[28,85,91,92]},{\"tag\":\"mate\",\"ridge\":769,\"a\":68,\"owners\":[28,91,92]},{\"tag\":\"mate\",\"ridge\":769,\"a\":74,\"owners\":[28,85,92]},{\"tag\":\"mate\",\"ridge\":769,\"a\":75,\"owners\":[28,85,91]},{\"tag\":\"mate\",\"ridge\":770,\"a\":17,\"owners\":[42,104,110,111]},{\"tag\":\"mate\",\"ridge\":770,\"a\":68,\"owners\":[42,110,111]},{\"tag\":\"mate\",\"ridge\":770,\"a\":74,\"owners\":[42,104,111]},{\"tag\":\"mate\",\"ridge\":770,\"a\":75,\"owners\":[42,104,110]},{\"tag\":\"mate\",\"ridge\":324,\"a\":26,\"owners\":[40,100,107,109,110]},{\"tag\":\"mate\",\"ridge\":324,\"a\":40,\"owners\":[26,81,88,90,91]},{\"tag\":\"mate\",\"ridge\":324,\"a\":81,\"owners\":[40,107,109,110]},{\"tag\":\"mate\",\"ridge\":324,\"a\":88,\"owners\":[40,100,109,110]},{\"tag\":\"mate\",\"ridge\":324,\"a\":90,\"owners\":[40,100,107,110]},{\"tag\":\"mate\",\"ridge\":324,\"a\":91,\"owners\":[40,100,107,109]},{\"tag\":\"mate\",\"ridge\":324,\"a\":100,\"owners\":[26,88,90,91]},{\"tag\":\"mate\",\"ridge\":324,\"a\":107,\"owners\":[26,81,90,91]},{\"tag\":\"mate\",\"ridge\":388,\"a\":27,\"owners\":[41,102,108,109,111]},{\"tag\":\"mate\",\"ridge\":388,\"a\":83,\"owners\":[41,108,109,111]},{\"tag\":\"mate\",\"ridge\":388,\"a\":89,\"owners\":[41,102,109,111]},{\"tag\":\"mate\",\"ridge\":388,\"a\":90,\"owners\":[41,102,108,111]},{\"tag\":\"mate\",\"ridge\":388,\"a\":92,\"owners\":[41,102,108,109]},{\"tag\":\"mate\",\"ridge\":388,\"a\":108,\"owners\":[27,83,90,92]},{\"tag\":\"mate\",\"ridge\":772,\"a\":28,\"owners\":[42,104,110,111]},{\"tag\":\"mate\",\"ridge\":772,\"a\":42,\"owners\":[28,85,91,92]},{\"tag\":\"mate\",\"ridge\":772,\"a\":85,\"owners\":[42,110,111]},{\"tag\":\"mate\",\"ridge\":772,\"a\":91,\"owners\":[42,104,111]},{\"tag\":\"mate\",\"ridge\":772,\"a\":92,\"owners\":[42,104,110]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[54,89,90,91,92],\"full_literals\":[-38,11,26,27,28,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[108,109,110,111],\"full_literals\":[-39,34,35,36,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[52,55,58],\"full_literals\":[-40,10,12,13]},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-42,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-43,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-44,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-44,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-45,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[15,26,40,64,71,73,74,81,88,90,91,100,107,109,110]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[16,27,41,66,72,73,75,83,89,90,92,102,108,109,111]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[17,28,42,68,74,75,85,91,92,104,110,111]}]}"
  "p cnf 45 81\n-27 -6 0\n-27 -24 0\n-28 -5 0\n-28 -23 0\n-28 -27 0\n-29 -4 0\n-29 -22 0\n-29 -25 0\n-29 -27 0\n-29 -28 0\n-32 -10 0\n-32 -12 0\n-32 -13 0\n-34 -11 0\n-34 -26 0\n-35 -9 0\n-36 -8 0\n-36 -31 0\n-36 -34 0\n-36 -35 0\n-37 -7 0\n-37 -30 0\n-37 -33 0\n-37 -35 0\n-37 -36 0\n-1 4 22 25 27 28 0\n-14 4 25 27 28 0\n-17 4 22 27 28 0\n-19 4 22 25 28 0\n-20 4 22 25 27 0\n-1 7 30 33 35 36 0\n-14 7 33 35 36 0\n-17 7 30 35 36 0\n-19 7 30 33 36 0\n-20 7 30 33 35 0\n-2 8 31 34 35 37 0\n-15 8 34 35 37 0\n-18 8 31 35 37 0\n-19 8 31 34 37 0\n-21 8 31 34 35 0\n-3 6 24 28 29 0\n-16 6 28 29 0\n-20 6 24 29 0\n-21 6 24 28 0\n-3 9 32 36 37 0\n-16 9 36 37 0\n-20 9 32 37 0\n-21 9 32 36 0\n-4 7 30 33 35 36 0\n-7 4 22 25 27 28 0\n-22 7 33 35 36 0\n-25 7 30 35 36 0\n-27 7 30 33 36 0\n-28 7 30 33 35 0\n-30 4 25 27 28 0\n-33 4 22 27 28 0\n-5 8 31 34 35 37 0\n-23 8 34 35 37 0\n-26 8 31 35 37 0\n-27 8 31 34 37 0\n-29 8 31 34 35 0\n-34 5 23 27 29 0\n-6 9 32 36 37 0\n-9 6 24 28 29 0\n-24 9 36 37 0\n-28 9 32 37 0\n-29 9 32 36 0\n-38 11 26 27 28 29 0\n-39 34 35 36 37 0\n-40 10 12 13 0\n-41 38 0\n-42 40 0\n-43 39 0\n-43 42 0\n-44 41 0\n-44 43 0\n-45 44 0\n45 0\n1 4 7 14 17 19 20 22 25 27 28 30 33 35 36 0\n2 5 8 15 18 19 21 23 26 27 29 31 34 35 37 0\n3 6 9 16 20 21 24 28 29 32 36 37 0\n"
  "82 44 0 78 77 0\n83 41 0 82 75 0\n84 43 0 82 76 0\n85 38 0 83 71 0\n86 39 0 84 73 0\n87 42 0 84 74 0\n88 40 0 87 72 0\n89 -32 0 88 11 12 13 70 0\n90 8 37 31 34 35 0 36 37 57 58 38 59 40 61 39 60 80 0\n91 -36 0 17 18 19 20 25 90 0\n92 27 29 -34 0 85 15 14 68 3 4 62 0\n93 29 21 -34 37 0 91 89 92 1 2 5 41 42 43 64 81 0\n94 -29 35 0 91 6 7 8 9 10 26 27 28 50 55 29 30 56 79 0\n95 35 37 0 86 91 69 94 92 93 1 2 5 44 0\n96 9 37 0 89 91 45 46 65 63 47 66 48 67 81 0\n97 37 0 95 16 96 0\n98 -7 0 97 21 0\n99 -30 0 97 22 0\n100 -33 0 97 23 0\n101 -35 0 97 24 0\n102 -1 0 98 99 100 101 91 31 0\n103 -14 0 98 100 101 91 32 0\n104 -22 0 98 100 101 91 51 0\n105 -17 0 99 101 98 91 33 0\n106 -25 0 99 101 98 91 52 0\n107 -19 0 100 99 98 91 34 0\n108 -20 0 100 99 98 101 35 0\n109 -27 0 100 99 98 91 53 0\n110 -28 0 100 99 98 101 54 0\n111 -4 0 100 99 98 101 91 49 0\n112 0 107 105 102 103 111 98 108 104 106 109 110 99 100 101 91 79 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077 Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077_validity Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00003.record077
