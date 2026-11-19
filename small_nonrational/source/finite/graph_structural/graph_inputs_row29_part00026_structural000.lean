module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00026Frames
public import GraphInputsRow29Part00026Leaves
public import GraphInputsRow29Part00026Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "bc1f38ad2aca2e87ae1b46b18b61d98e538ce4b86e4789ee2749b24b91e785d16c52d4756354d3352d1b51d27783d0ec3a8e532cc73c2e8b62e4b52ccb4ac6b46c9bc1e8761e4751cc749c6745c972b05c0f0aa1683a298560d90e2384e0b81e2a4590e4a5154354348d1342d07703a0e4328c530cd0b22c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "24db49b69249249b6936d2492492492492492492492492489249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 75)]))
 (.leaf ([(facetIndex 86), (facetIndex 87), (facetIndex 88), (facetIndex 89), (facetIndex 90), (facetIndex 91), (facetIndex 92)])))
 (.branch 3
 (.leaf ([(facetIndex 48), (facetIndex 58), (facetIndex 64), (facetIndex 66), (facetIndex 67), (facetIndex 68)]))
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 59), (facetIndex 60), (facetIndex 65)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 44), (facetIndex 54), (facetIndex 62), (facetIndex 76), (facetIndex 81), (facetIndex 93), (facetIndex 98), (facetIndex 103)]))
 (.leaf ([(facetIndex 42), (facetIndex 52), (facetIndex 63), (facetIndex 77), (facetIndex 82), (facetIndex 94), (facetIndex 99), (facetIndex 104)])))
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 51)]))
 (.leaf ([(facetIndex 53), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 61)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "5800b0016124924016002c00000249ab3b6bff3dcdadb4d4z1f;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 83), (facetIndex 84), (facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 95), (facetIndex 96), (facetIndex 97)]))
 (.leaf ([(facetIndex 100), (facetIndex 101), (facetIndex 102)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "3f0a8000054z29;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4, 5, 6, 7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1]
def grouped3_0010 : List Nat := [1]
def grouped3_0011 : List Nat := [2]
def grouped3_0012 : List Nat := [2, 3]
def grouped3_0013 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record003" 36

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record003" "{\"ridges\":[[14,577],[15,641],[16,769],[16,770],[48,577],[48,578],[50,641],[50,642],[51,769],[51,770],[58,577],[58,578],[60,641],[60,642],[61,770],[64,577],[65,641],[66,577],[66,641],[66,642],[67,577],[67,770],[68,641],[68,769],[78,708],[79,836],[80,900],[83,712],[84,840],[85,904],[96,836],[97,642],[100,712],[101,840],[102,904]],\"owners\":[[14,577,[78,79,83,84],[48,58,64,66,67]],[48,577,[83,84],[14,58,64,66,67,78,79]],[58,577,[78,79],[14,48,64,66,67,83,84]],[64,577,[78,79,83,84],[14,48,58,66,67]],[66,577,[79,84],[14,48,58,64,67,78,83]],[67,577,[78,83],[14,48,58,64,66,79,84]],[48,578,[100,101],[14,58,64,66,67,95,96]],[58,578,[95,96],[14,48,64,66,67,100,101]],[15,641,[78,80,83,85],[50,60,65,66,68]],[50,641,[83,85],[15,60,65,66,68,78,80]],[60,641,[78,80],[15,50,65,66,68,83,85]],[65,641,[78,80,83,85],[15,50,60,66,68]],[66,641,[80,85],[15,50,60,65,68,78,83]],[68,641,[78,83],[15,50,60,65,66,80,85]],[50,642,[100,102],[15,60,65,66,68,95,97]],[60,642,[95,97],[15,50,65,66,68,100,102]],[66,642,[97,102],[15,50,60,65,68,95,100]],[97,642,[15,60,65,66,100],[50,68,95,102]],[16,769,[79,80,84,85],[51,61,67,68]],[51,769,[84,85],[16,61,67,68,79,80]],[68,769,[79,84],[16,51,61,67,80,85]],[16,770,[96,97,101,102],[51,61,67,68]],[51,770,[101,102],[16,61,67,68,96,97]],[61,770,[96,97],[16,51,67,68,101,102]],[67,770,[97,102],[16,51,61,68,96,101]],[78,708,[95],[]],[79,836,[96],[]],[96,836,[79],[]],[80,900,[97],[]],[83,712,[100],[]],[100,712,[83],[]],[84,840,[101],[]],[101,840,[84],[]],[85,904,[102],[]],[102,904,[85],[]]],\"edges\":[[41,[14,48,58,64,66,67,78,79,83,84,95,96,100,101]],[43,[15,50,60,65,66,68,78,80,83,85,95,97,100,102]],[44,[16,51,61,67,68,79,80,84,85,96,97,101,102]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-2],[-13,-8],[-13,-11],[-16,-15],[-17,-16],[-19,-18],[-21,-16],[-23,-15],[-23,-16],[-24,-19],[-26,-18],[-26,-19],[-26,-24],[-26,-25],[-1,15,16,18,19],[-4,18,19],[-7,15,16],[-10,15,16,18,19],[-12,16,19],[-13,15,18],[-4,24,25],[-7,21,22],[-2,15,17,18,20],[-5,18,20],[-8,15,17],[-11,15,17,18,20],[-12,17,20],[-14,15,18],[-5,24,26],[-8,21,23],[-12,23,26],[-23,2,8,11,12,24],[-3,16,17,19,20],[-6,19,20],[-14,16,19],[-3,22,23,25,26],[-6,25,26],[-9,22,23],[-13,23,26],[-15,21],[-16,22],[-22,16],[-17,23],[-18,24],[-24,18],[-19,25],[-25,19],[-20,26],[-26,20],[-27,4,7,10,12,13,14],[-28,27],[-29,28],[-30,29],[30],[-18,31],[-19,31],[-20,31],[-21,32],[-22,32],[-23,32],[-33,24,25,26],[-24,33],[-25,33],[-26,33],[-31,34],[-35,33],[-32,-33,35],[-34,-35,36],[-36],[1,4,7,10,12,13,15,16,18,19,21,22,24,25],[2,5,8,11,12,14,15,17,18,20,21,23,24,26],[3,6,9,13,14,16,17,19,20,22,23,25,26]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":67,\"b\":15},{\"tag\":\"incompatible\",\"a\":67,\"b\":60},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"incompatible\",\"a\":95,\"b\":79},{\"tag\":\"incompatible\",\"a\":97,\"b\":78},{\"tag\":\"incompatible\",\"a\":97,\"b\":79},{\"tag\":\"incompatible\",\"a\":100,\"b\":84},{\"tag\":\"incompatible\",\"a\":102,\"b\":83},{\"tag\":\"incompatible\",\"a\":102,\"b\":84},{\"tag\":\"incompatible\",\"a\":102,\"b\":100},{\"tag\":\"incompatible\",\"a\":102,\"b\":101},{\"tag\":\"mate\",\"ridge\":577,\"a\":14,\"owners\":[78,79,83,84]},{\"tag\":\"mate\",\"ridge\":577,\"a\":48,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":577,\"a\":58,\"owners\":[78,79]},{\"tag\":\"mate\",\"ridge\":577,\"a\":64,\"owners\":[78,79,83,84]},{\"tag\":\"mate\",\"ridge\":577,\"a\":66,\"owners\":[79,84]},{\"tag\":\"mate\",\"ridge\":577,\"a\":67,\"owners\":[78,83]},{\"tag\":\"mate\",\"ridge\":578,\"a\":48,\"owners\":[100,101]},{\"tag\":\"mate\",\"ridge\":578,\"a\":58,\"owners\":[95,96]},{\"tag\":\"mate\",\"ridge\":641,\"a\":15,\"owners\":[78,80,83,85]},{\"tag\":\"mate\",\"ridge\":641,\"a\":50,\"owners\":[83,85]},{\"tag\":\"mate\",\"ridge\":641,\"a\":60,\"owners\":[78,80]},{\"tag\":\"mate\",\"ridge\":641,\"a\":65,\"owners\":[78,80,83,85]},{\"tag\":\"mate\",\"ridge\":641,\"a\":66,\"owners\":[80,85]},{\"tag\":\"mate\",\"ridge\":641,\"a\":68,\"owners\":[78,83]},{\"tag\":\"mate\",\"ridge\":642,\"a\":50,\"owners\":[100,102]},{\"tag\":\"mate\",\"ridge\":642,\"a\":60,\"owners\":[95,97]},{\"tag\":\"mate\",\"ridge\":642,\"a\":66,\"owners\":[97,102]},{\"tag\":\"mate\",\"ridge\":642,\"a\":97,\"owners\":[15,60,65,66,100]},{\"tag\":\"mate\",\"ridge\":769,\"a\":16,\"owners\":[79,80,84,85]},{\"tag\":\"mate\",\"ridge\":769,\"a\":51,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":769,\"a\":68,\"owners\":[79,84]},{\"tag\":\"mate\",\"ridge\":770,\"a\":16,\"owners\":[96,97,101,102]},{\"tag\":\"mate\",\"ridge\":770,\"a\":51,\"owners\":[101,102]},{\"tag\":\"mate\",\"ridge\":770,\"a\":61,\"owners\":[96,97]},{\"tag\":\"mate\",\"ridge\":770,\"a\":67,\"owners\":[97,102]},{\"tag\":\"mate\",\"ridge\":708,\"a\":78,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":836,\"a\":79,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":836,\"a\":96,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":900,\"a\":80,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":712,\"a\":83,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":712,\"a\":100,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":840,\"a\":84,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":840,\"a\":101,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":904,\"a\":85,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":904,\"a\":102,\"owners\":[85]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[48,58,64,66,67,68],\"full_literals\":[-27,4,7,10,12,13,14]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-28,27,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-29,false,28],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-30,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-18,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":84,\"full_literals\":[-19,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-20,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":95,\"full_literals\":[-21,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":96,\"full_literals\":[-22,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":97,\"full_literals\":[-23,32]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[100,101,102],\"full_literals\":[-33,24,25,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":100,\"full_literals\":[-24,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":101,\"full_literals\":[-25,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":102,\"full_literals\":[-26,33]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-35,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-33,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-34,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[14,48,58,64,66,67,78,79,83,84,95,96,100,101]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[15,50,60,65,66,68,78,80,83,85,95,97,100,102]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[16,51,61,67,68,79,80,84,85,96,97,101,102]}]}"
  "p cnf 36 72\n-13 -2 0\n-13 -8 0\n-13 -11 0\n-16 -15 0\n-17 -16 0\n-19 -18 0\n-21 -16 0\n-23 -15 0\n-23 -16 0\n-24 -19 0\n-26 -18 0\n-26 -19 0\n-26 -24 0\n-26 -25 0\n-1 15 16 18 19 0\n-4 18 19 0\n-7 15 16 0\n-10 15 16 18 19 0\n-12 16 19 0\n-13 15 18 0\n-4 24 25 0\n-7 21 22 0\n-2 15 17 18 20 0\n-5 18 20 0\n-8 15 17 0\n-11 15 17 18 20 0\n-12 17 20 0\n-14 15 18 0\n-5 24 26 0\n-8 21 23 0\n-12 23 26 0\n-23 2 8 11 12 24 0\n-3 16 17 19 20 0\n-6 19 20 0\n-14 16 19 0\n-3 22 23 25 26 0\n-6 25 26 0\n-9 22 23 0\n-13 23 26 0\n-15 21 0\n-16 22 0\n-22 16 0\n-17 23 0\n-18 24 0\n-24 18 0\n-19 25 0\n-25 19 0\n-20 26 0\n-26 20 0\n-27 4 7 10 12 13 14 0\n-28 27 0\n-29 28 0\n-30 29 0\n30 0\n-18 31 0\n-19 31 0\n-20 31 0\n-21 32 0\n-22 32 0\n-23 32 0\n-33 24 25 26 0\n-24 33 0\n-25 33 0\n-26 33 0\n-31 34 0\n-35 33 0\n-32 -33 35 0\n-34 -35 36 0\n-36 0\n1 4 7 10 12 13 15 16 18 19 21 22 24 25 0\n2 5 8 11 12 14 15 17 18 20 21 23 24 26 0\n3 6 9 13 14 16 17 19 20 22 23 25 26 0\n"
  "73 29 0 54 53 0\n74 28 0 73 52 0\n75 27 0 74 51 0\n76 -35 0 69 66 68 65 55 56 57 45 47 49 61 0\n77 -26 32 0 59 41 58 40 22 11 12 13 14 16 15 20 19 18 70 0\n78 19 32 0 60 77 39 48 43 59 41 38 47 33 35 34 72 0\n79 32 0 58 60 30 40 43 77 48 31 78 6 10 24 23 26 28 71 0\n80 -33 0 79 76 67 0\n81 -24 0 80 62 0\n82 -25 0 80 63 0\n83 -26 0 80 64 0\n84 -4 0 81 82 21 0\n85 -5 0 81 83 29 0\n86 -18 0 81 44 0\n87 -6 0 82 83 37 0\n88 -19 0 82 46 0\n89 -20 0 83 48 0\n90 23 13 16 0 83 82 88 89 87 35 42 43 38 36 72 0\n91 13 16 0 86 88 84 75 35 19 90 8 17 18 50 0\n92 16 0 88 83 81 19 91 1 2 3 39 32 0\n93 -15 0 92 4 0\n94 -17 0 92 5 0\n95 -21 0 92 7 0\n96 -23 0 92 9 0\n97 -8 0 93 94 25 0\n98 -11 0 93 86 94 89 26 0\n99 -14 0 93 86 28 0\n100 -2 0 93 86 94 89 23 0\n101 -12 0 94 89 27 0\n102 0 97 100 85 86 101 98 93 94 99 89 95 96 81 83 71 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ce2ac5723c4f2aa56a3a4e8e6358ae1783ef07a178751b4731aa5598e539a956539695554d58d535a354d8b52d2b61d4745d0f6a358ce3a4d5334e334ce8b52e2b4acab86d1b16c3b19c970dc8f13f28c60c6298560b81ec86a1c4551c26294a619464c5294550b41d30ca314c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "136db6da49269a6924934d26db49249269a4db692492492449249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 77), (facetIndex 79)]))
 (.leaf ([(facetIndex 43), (facetIndex 45), (facetIndex 51)])))
 (.branch 3
 (.leaf ([(facetIndex 44), (facetIndex 61)]))
 (.leaf ([(facetIndex 60), (facetIndex 87)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 88), (facetIndex 92)]))
 (.leaf ([(facetIndex 49), (facetIndex 66), (facetIndex 75)])))
 (.branch 7
 (.leaf ([(facetIndex 62), (facetIndex 68), (facetIndex 91)]))
 (.branch 8
 (.leaf ([(facetIndex 46), (facetIndex 63), (facetIndex 85), (facetIndex 89)]))
 (.leaf ([(facetIndex 86), (facetIndex 90)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "46874387000000000500000060500762300000000105007121z2b;"⟩
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
def grouped3_0012 : List Nat := [6, 7, 8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record009" 36

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record009" "{\"ridges\":[[20,321],[22,641],[44,650],[48,321],[49,658],[51,354],[52,641],[61,652],[65,336],[66,660],[68,356],[69,641],[72,336],[73,672],[75,720],[76,321],[77,480],[78,641],[79,960],[88,650],[91,332],[92,652]],\"owners\":[[20,321,[43,51,60,68,77,79],[48,65,72,76]],[48,321,[60,68,77,79],[20,43,51,65,72,76]],[76,321,[43,51,60,68,77],[20,48,65,72,79]],[65,336,[87],[20,48,72,76,91]],[72,336,[],[20,48,65,76,87,91]],[22,641,[44,49,61,66,75,79],[52,69,73,78]],[52,641,[61,66,75,79],[22,44,49,69,73,78]],[69,641,[44,49,75,79],[22,52,61,66,73,78]],[78,641,[44,49,61,66,75],[22,52,69,73,79]],[73,672,[],[22,52,69,78,88,92]],[44,650,[88],[]],[88,650,[44],[]],[49,658,[],[]],[51,354,[],[]],[91,332,[60],[]],[61,652,[92],[]],[92,652,[61],[]],[66,660,[],[]],[68,356,[],[]],[75,720,[],[]],[77,480,[],[]],[79,960,[],[]]],\"edges\":[[40,[20,43,48,51,60,65,68,72,76,77,79,87,91]],[43,[22,44,49,52,61,66,69,73,75,78,79,88,92]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,3,7,9,13,19,21],[-5,9,13,19,21],[-18,3,7,9,13,19],[-11,22],[-15],[-2,4,6,10,12,17,21],[-8,10,12,17,21],[-14,4,6,17,21],[-20,4,6,10,12,17],[-16],[-4,23],[-23,4],[-6],[-7],[-24,9],[-10,25],[-25,10],[-12],[-13],[-17],[-19],[-21],[-3,26],[-27,4,10],[-4,27],[-10,27],[-9,28],[-22,28],[-23,29],[-25,29],[-26,30],[-27,31],[-27,-28,32],[-32,33],[-30,-31,33],[-29,34],[-34,35],[-33,-35,36],[-36],[1,3,5,7,9,11,13,15,18,19,21,22,24],[2,4,6,8,10,12,14,16,17,20,21,23,25]],\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":321,\"a\":20,\"owners\":[43,51,60,68,77,79]},{\"tag\":\"mate\",\"ridge\":321,\"a\":48,\"owners\":[60,68,77,79]},{\"tag\":\"mate\",\"ridge\":321,\"a\":76,\"owners\":[43,51,60,68,77]},{\"tag\":\"mate\",\"ridge\":336,\"a\":65,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":336,\"a\":72,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":641,\"a\":22,\"owners\":[44,49,61,66,75,79]},{\"tag\":\"mate\",\"ridge\":641,\"a\":52,\"owners\":[61,66,75,79]},{\"tag\":\"mate\",\"ridge\":641,\"a\":69,\"owners\":[44,49,75,79]},{\"tag\":\"mate\",\"ridge\":641,\"a\":78,\"owners\":[44,49,61,66,75]},{\"tag\":\"mate\",\"ridge\":672,\"a\":73,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":650,\"a\":44,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":650,\"a\":88,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":658,\"a\":49,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":354,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":332,\"a\":91,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":652,\"a\":61,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":652,\"a\":92,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":660,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":356,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":720,\"a\":75,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":480,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":960,\"a\":79,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":43,\"full_literals\":[-3,26]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[44,61],\"full_literals\":[-27,4,10]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":44,\"full_literals\":[-4,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":61,\"full_literals\":[-10,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":60,\"full_literals\":[-9,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":87,\"full_literals\":[-22,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":88,\"full_literals\":[-23,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":92,\"full_literals\":[-25,29]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-28,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-32,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-30,-31,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-33,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[20,43,48,51,60,65,68,72,76,77,79,87,91]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[22,44,49,52,61,66,69,73,75,78,79,88,92]}]}"
  "p cnf 36 41\n-1 3 7 9 13 19 21 0\n-5 9 13 19 21 0\n-18 3 7 9 13 19 0\n-11 22 0\n-15 0\n-2 4 6 10 12 17 21 0\n-8 10 12 17 21 0\n-14 4 6 17 21 0\n-20 4 6 10 12 17 0\n-16 0\n-4 23 0\n-23 4 0\n-6 0\n-7 0\n-24 9 0\n-10 25 0\n-25 10 0\n-12 0\n-13 0\n-17 0\n-19 0\n-21 0\n-3 26 0\n-27 4 10 0\n-4 27 0\n-10 27 0\n-9 28 0\n-22 28 0\n-23 29 0\n-25 29 0\n-26 30 0\n-27 31 0\n-27 -28 32 0\n-32 33 0\n-30 -31 33 0\n-29 34 0\n-34 35 0\n-33 -35 36 0\n-36 0\n1 3 5 7 9 11 13 15 18 19 21 22 24 0\n2 4 6 8 10 12 14 16 17 20 21 23 25 0\n"
  "42 1 3 5 9 11 18 22 24 0 14 19 5 21 22 40 0\n43 2 4 8 10 14 20 23 25 0 13 18 10 20 22 41 0\n44 27 0 22 20 18 13 25 26 8 12 7 17 6 9 43 0\n45 31 0 44 32 0\n46 33 0 45 44 22 21 19 14 34 35 33 31 27 28 23 2 15 1 3 4 42 0\n47 -35 0 46 39 38 0\n48 -34 0 47 37 0\n49 -29 0 48 36 0\n50 -23 0 49 29 0\n51 -25 0 49 30 0\n52 -4 0 50 11 0\n53 -10 0 51 16 0\n54 0 53 52 44 24 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "338cd32cc723c4f2aaa68da8e966399564d8ce2b85e0fbc1e85e1d46d1cc729c6699366394e725594e5c56354d70d3362d4b4ad8751d1743da8d6338e9354cd38cd33a2ccb8ae1b26c5b0ed4731d2729c6745c3723c4faa1542a8560b81ec86a1c4551a26292a61951525454550b41d30ca314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6da6db69b4934d349269a4d34da4924934d26d2492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 78), (facetIndex 80)]))
 (.branch 2
 (.leaf ([(facetIndex 61), (facetIndex 66)]))
 (.leaf ([(facetIndex 84), (facetIndex 87)]))))
 (.branch 4
 (.leaf ([(facetIndex 50), (facetIndex 71), (facetIndex 76)]))
 (.branch 5
 (.leaf ([(facetIndex 46), (facetIndex 52)]))
 (.leaf ([(facetIndex 85), (facetIndex 88)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 90), (facetIndex 91)]))
 (.branch 8
 (.leaf ([(facetIndex 62), (facetIndex 64), (facetIndex 69)]))
 (.leaf ([(facetIndex 93), (facetIndex 94), (facetIndex 95)]))))
 (.branch 10
 (.leaf ([(facetIndex 96), (facetIndex 97), (facetIndex 98)]))
 (.branch 11
 (.leaf ([(facetIndex 47)]))
 (.leaf ([(facetIndex 89)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "999888066b52052000000030000307001070710000000040300a4z2e;"⟩
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
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [6]
def grouped3_0011 : List Nat := [6, 7, 8]
def grouped3_0012 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0013 : List Nat := [7]
def grouped3_0014 : List Nat := [7, 8]
def grouped3_0015 : List Nat := [8]
def grouped3_0016 : List Nat := [9]
def grouped3_0017 : List Nat := [9, 10, 11]
def grouped3_0018 : List Nat := [10, 11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record011" 49

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record011" "{\"ridges\":[[9,194],[21,769],[21,784],[23,769],[23,800],[37,193],[44,194],[48,194],[51,194],[62,780],[64,564],[65,784],[68,800],[69,312],[73,784],[74,800],[75,784],[75,800],[76,720],[77,769],[77,784],[78,480],[79,769],[79,800],[80,960],[90,216],[95,780],[96,780],[97,564],[98,312]],\"owners\":[[37,193,[71,76,78,80],[9,44,48,51,61,66]],[9,194,[84,87,90],[37,44,48,51]],[44,194,[87],[9,37,48,51,84,90]],[48,194,[84,87],[9,37,44,51,90]],[51,194,[84,90],[9,37,44,48,87]],[21,769,[23,62,68,74,79,80],[65,73,77]],[23,769,[21,62,65,73,77,80],[68,74,79]],[77,769,[23,62,68,74,79],[21,65,73,80]],[79,769,[21,62,65,73,77],[23,68,74,80]],[21,784,[95,97,98],[65,73,75,77]],[65,784,[98],[21,73,75,77,95,97]],[73,784,[97],[21,65,75,77,95,98]],[75,784,[95],[21,65,73,77,97,98]],[77,784,[95,97,98],[21,65,73,75]],[23,800,[96,97,98],[68,74,75,79]],[68,800,[98],[23,74,75,79,96,97]],[74,800,[97],[23,68,75,79,96,98]],[75,800,[96],[23,68,74,79,97,98]],[79,800,[96,97,98],[23,68,74,75]],[62,780,[95,96],[]],[95,780,[62,96],[]],[96,780,[62,95],[]],[64,564,[94,97],[]],[97,564,[64,94],[]],[69,312,[93,98],[]],[98,312,[69,93],[]],[90,216,[71],[]],[76,720,[],[]],[78,480,[],[]],[80,960,[],[]]],\"edges\":[[39,[9,37,44,48,51,61,66,71,76,78,80,84,87,90]],[44,[21,23,62,65,68,73,74,75,77,79,80,95,96,97,98]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-4,15,19,21,23],[-1,24,25,26],[-5,25],[-6,24,25],[-7,24,26],[-2,3,9,13,17,22,23],[-3,2,9,11,16,20,23],[-20,3,9,13,17,22],[-22,2,9,11,16,20],[-2,29,31,32],[-11,32],[-16,31],[-18,29],[-20,29,31,32],[-3,30,31,32],[-13,32],[-17,31],[-18,30],[-22,30,31,32],[-9,29,30],[-29,9,30],[-30,9,29],[-10,28,31],[-31,10,28],[-14,27,32],[-32,14,27],[-26,15],[-19],[-21],[-23],[-8,33],[-12,33],[-24,34],[-25,34],[-15,35],[-36,9,10,14],[-9,36],[-10,36],[-14,36],[-27,37],[-28,37],[-29,37],[-30,38],[-31,38],[-32,38],[-34,39],[-33,39],[-39,40],[-35,41],[-41,42],[-40,42],[-43,36,37],[-37,43],[-36,43],[-36,-37,44],[-43,45],[-44,46],[-38,47],[-45,-47,48],[-46,48],[-42,-48,49],[-49],[1,4,5,6,7,8,12,15,19,21,23,24,25,26],[2,3,9,11,13,16,17,18,20,22,23,29,30,31,32]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":193,\"a\":37,\"owners\":[71,76,78,80]},{\"tag\":\"mate\",\"ridge\":194,\"a\":9,\"owners\":[84,87,90]},{\"tag\":\"mate\",\"ridge\":194,\"a\":44,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":194,\"a\":48,\"owners\":[84,87]},{\"tag\":\"mate\",\"ridge\":194,\"a\":51,\"owners\":[84,90]},{\"tag\":\"mate\",\"ridge\":769,\"a\":21,\"owners\":[23,62,68,74,79,80]},{\"tag\":\"mate\",\"ridge\":769,\"a\":23,\"owners\":[21,62,65,73,77,80]},{\"tag\":\"mate\",\"ridge\":769,\"a\":77,\"owners\":[23,62,68,74,79]},{\"tag\":\"mate\",\"ridge\":769,\"a\":79,\"owners\":[21,62,65,73,77]},{\"tag\":\"mate\",\"ridge\":784,\"a\":21,\"owners\":[95,97,98]},{\"tag\":\"mate\",\"ridge\":784,\"a\":65,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":784,\"a\":73,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":784,\"a\":75,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":784,\"a\":77,\"owners\":[95,97,98]},{\"tag\":\"mate\",\"ridge\":800,\"a\":23,\"owners\":[96,97,98]},{\"tag\":\"mate\",\"ridge\":800,\"a\":68,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":800,\"a\":74,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":800,\"a\":75,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":800,\"a\":79,\"owners\":[96,97,98]},{\"tag\":\"mate\",\"ridge\":780,\"a\":62,\"owners\":[95,96]},{\"tag\":\"mate\",\"ridge\":780,\"a\":95,\"owners\":[62,96]},{\"tag\":\"mate\",\"ridge\":780,\"a\":96,\"owners\":[62,95]},{\"tag\":\"mate\",\"ridge\":564,\"a\":64,\"owners\":[94,97]},{\"tag\":\"mate\",\"ridge\":564,\"a\":97,\"owners\":[64,94]},{\"tag\":\"mate\",\"ridge\":312,\"a\":69,\"owners\":[93,98]},{\"tag\":\"mate\",\"ridge\":312,\"a\":98,\"owners\":[69,93]},{\"tag\":\"mate\",\"ridge\":216,\"a\":90,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":720,\"a\":76,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":480,\"a\":78,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":960,\"a\":80,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":61,\"full_literals\":[-8,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-12,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":84,\"full_literals\":[-24,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":87,\"full_literals\":[-25,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-15,35]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[62,64,69],\"full_literals\":[-36,9,10,14]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":62,\"full_literals\":[-9,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":64,\"full_literals\":[-10,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":69,\"full_literals\":[-14,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":93,\"full_literals\":[-27,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":94,\"full_literals\":[-28,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":95,\"full_literals\":[-29,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":96,\"full_literals\":[-30,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":97,\"full_literals\":[-31,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":98,\"full_literals\":[-32,38]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-37,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-42,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[9,37,44,48,51,61,66,71,76,78,80,84,87,90]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[21,23,62,65,68,73,74,75,77,79,80,95,96,97,98]}]}"
  "p cnf 49 64\n-4 15 19 21 23 0\n-1 24 25 26 0\n-5 25 0\n-6 24 25 0\n-7 24 26 0\n-2 3 9 13 17 22 23 0\n-3 2 9 11 16 20 23 0\n-20 3 9 13 17 22 0\n-22 2 9 11 16 20 0\n-2 29 31 32 0\n-11 32 0\n-16 31 0\n-18 29 0\n-20 29 31 32 0\n-3 30 31 32 0\n-13 32 0\n-17 31 0\n-18 30 0\n-22 30 31 32 0\n-9 29 30 0\n-29 9 30 0\n-30 9 29 0\n-10 28 31 0\n-31 10 28 0\n-14 27 32 0\n-32 14 27 0\n-26 15 0\n-19 0\n-21 0\n-23 0\n-8 33 0\n-12 33 0\n-24 34 0\n-25 34 0\n-15 35 0\n-36 9 10 14 0\n-9 36 0\n-10 36 0\n-14 36 0\n-27 37 0\n-28 37 0\n-29 37 0\n-30 38 0\n-31 38 0\n-32 38 0\n-34 39 0\n-33 39 0\n-39 40 0\n-35 41 0\n-41 42 0\n-40 42 0\n-43 36 37 0\n-37 43 0\n-36 43 0\n-36 -37 44 0\n-43 45 0\n-44 46 0\n-38 47 0\n-45 -47 48 0\n-46 48 0\n-42 -48 49 0\n-49 0\n1 4 5 6 7 8 12 15 19 21 23 24 25 26 0\n2 3 9 11 13 16 17 18 20 22 23 29 30 31 32 0\n"
  "65 1 4 5 6 7 8 12 15 24 25 26 0 28 29 30 63 0\n66 2 3 9 11 13 16 17 18 20 22 29 30 31 32 0 30 64 0\n67 42 0 30 29 28 50 51 49 48 35 46 47 1 27 33 34 31 32 2 4 5 3 65 0\n68 -48 0 67 62 61 0\n69 -46 0 68 60 0\n70 -44 0 69 57 0\n71 43 0 30 53 54 40 41 42 37 38 39 26 24 10 13 14 22 11 16 12 17 7 9 66 0\n72 45 0 71 56 0\n73 -47 0 72 68 59 0\n74 -38 0 73 58 0\n75 -30 0 74 43 0\n76 -31 0 74 44 0\n77 -32 0 74 45 0\n78 -3 0 75 76 77 15 0\n79 -18 0 75 18 0\n80 -22 0 75 76 77 19 0\n81 -16 0 76 12 0\n82 -17 0 76 17 0\n83 -11 0 77 11 0\n84 -13 0 77 16 0\n85 37 0 71 77 76 75 40 41 42 52 25 23 20 36 0\n86 -36 0 85 70 55 0\n87 -9 0 86 37 0\n88 -29 0 87 75 21 0\n89 -2 0 87 78 84 82 80 30 6 0\n90 20 0 87 89 78 84 81 82 79 83 80 88 75 76 77 66 0\n91 0 90 87 78 84 82 80 8 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record013
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "338ad2ac3b23cf0ba2ccab2d2acacaaaac695a8e93aa9a9655a364d8b6a38ce8b8ae8785e0fba178731ac729aa5693a719566394e565395554d4b5334ad1b45de0dc3c8ea368f13a4d538cd332cf0ba2d4b32e2b4acab86d1b16c3b51d2729d1725c570dc8f0bf308e03cc4a1a3184e079310e4c5294351342d0754330d1312c1b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9b69b4db6d34db6db69b49369b6db6934d249269b69a69b6936d2493492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 33), (facetIndex 35), (facetIndex 41), (facetIndex 42), (facetIndex 48), (facetIndex 54)]))
 (.leaf ([(facetIndex 25), (facetIndex 26), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59)])))
 (.branch 3
 (.leaf ([(facetIndex 78), (facetIndex 82)]))
 (.leaf ([(facetIndex 34), (facetIndex 77), (facetIndex 79), (facetIndex 91), (facetIndex 102)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 61), (facetIndex 65), (facetIndex 66), (facetIndex 74)]))
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 50), (facetIndex 93)])))
 (.branch 7
 (.leaf ([(facetIndex 29), (facetIndex 31), (facetIndex 60), (facetIndex 63)]))
 (.branch 8
 (.leaf ([(facetIndex 99), (facetIndex 106)]))
 (.leaf ([(facetIndex 27), (facetIndex 30), (facetIndex 46)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "7000300700000503000000002003230040000000440604611110000050008000000005503006860811z19;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 62), (facetIndex 64)]))
 (.branch 2
 (.leaf ([(facetIndex 85), (facetIndex 87)]))
 (.leaf ([(facetIndex 51), (facetIndex 55), (facetIndex 75), (facetIndex 101)]))))
 (.branch 4
 (.leaf ([(facetIndex 81), (facetIndex 83), (facetIndex 88)]))
 (.branch 5
 (.leaf ([(facetIndex 86), (facetIndex 104), (facetIndex 105)]))
 (.leaf ([(facetIndex 38), (facetIndex 43), (facetIndex 69), (facetIndex 96)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 70), (facetIndex 103)]))
 (.branch 8
 (.leaf ([(facetIndex 39), (facetIndex 44), (facetIndex 67), (facetIndex 97)]))
 (.leaf ([(facetIndex 68), (facetIndex 90), (facetIndex 92)]))))
 (.branch 11
 (.branch 10
 (.leaf ([(facetIndex 40), (facetIndex 49), (facetIndex 71), (facetIndex 72), (facetIndex 76)]))
 (.leaf ([(facetIndex 45), (facetIndex 47), (facetIndex 80), (facetIndex 89), (facetIndex 95), (facetIndex 100)])))
 (.branch 12
 (.leaf ([(facetIndex 52), (facetIndex 73), (facetIndex 84)]))
 (.leaf ([(facetIndex 53), (facetIndex 94), (facetIndex 98)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "44602a0c75ac0808a3141b303a000920b9965870000000000020cb2090a0a7500975z26;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 13
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7, 8]
def grouped2_0008 : List Nat := [7]
def grouped2_0009 : List Nat := [7, 8]
def grouped2_0010 : List Nat := [8]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1, 2]
def grouped3_0013 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [1, 2]
def grouped3_0017 : List Nat := [2]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [3, 4, 5]
def grouped3_0020 : List Nat := [4]
def grouped3_0021 : List Nat := [4, 5]
def grouped3_0022 : List Nat := [5]
def grouped3_0023 : List Nat := [6, 7, 8]
def grouped3_0024 : List Nat := [6, 7, 8, 9, 10, 11, 12]
def grouped3_0025 : List Nat := [9]
def grouped3_0026 : List Nat := [9, 10]
def grouped3_0027 : List Nat := [9, 10, 11, 12]
def grouped3_0028 : List Nat := [10]
def grouped3_0029 : List Nat := [11]
def grouped3_0030 : List Nat := [11, 12]
def grouped3_0031 : List Nat := [12]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record013" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group\",\"kind\":3,\"index\":12},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record013" 74

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record013" "{\"ridges\":[[8,322],[33,322],[42,321],[43,649],[48,321],[49,642],[52,672],[54,322],[55,642],[64,356],[67,344],[70,360],[71,672],[73,657],[73,672],[75,480],[76,672],[83,652],[88,660],[89,672],[94,672],[96,712],[97,840],[98,178],[99,770],[100,642],[101,960],[104,652],[105,660]],\"owners\":[[42,321,[62,64,75],[8,33,48,54,67,70]],[48,321,[64,70,75],[8,33,42,54,62,67]],[8,322,[87,92,97,101],[33,42,48,54]],[33,322,[92,97,101],[8,42,48,54,87]],[54,322,[87,92,97],[8,33,42,48,101]],[99,770,[44,55,97,101],[21,50,53,93,95,100]],[49,642,[83,89,94,96,100,101],[43,52,55,88,98]],[55,642,[83,88,89,94,96,98],[43,49,52,100,101]],[100,642,[43,49,83,88,96],[52,55,89,94,98,101]],[43,649,[71],[]],[98,178,[45,84],[]],[73,657,[49],[]],[52,672,[104,105],[71,73,76,89,94,98,100]],[71,672,[89,98,100,105],[52,73,76,94,104]],[73,672,[89,94,100,104],[52,71,76,98,105]],[76,672,[89,94,98,104,105],[52,71,73,100]],[89,672,[71,73,76],[52,94,98,100,104,105]],[94,672,[73,76,105],[52,71,89,98,100,104]],[64,356,[],[]],[67,344,[92],[]],[70,360,[],[]],[75,480,[],[]],[83,652,[104],[]],[104,652,[83],[]],[88,660,[105],[]],[105,660,[88],[]],[96,712,[],[]],[97,840,[],[]],[101,960,[],[]]],\"edges\":[[40,[8,33,42,48,54,62,64,67,70,75,87,92,97,101]],[43,[43,49,52,55,71,73,76,83,88,89,94,96,98,100,101,104,105]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record013" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record013\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-3],[-31,-5],[-31,-6],[-31,-9],[-31,-14],[-32,-31],[-36,-2],[-36,-11],[-37,-36],[-42,-31],[-42,-36],[-7,18,19,24],[-12,19,21,24],[-1,28,31,35,39],[-4,31,35,39],[-16,28,31,35],[-37,9,17,35,39],[-13,26,30,33,34,38,39],[-17,26,29,30,33,34,36],[-38,8,13,26,29,34],[-8,22],[-36,10,27],[-23,13],[-15,40,41],[-22,30,36,38,41],[-23,30,33,38,40],[-25,30,33,36,40,41],[-30,22,23,25],[-33,23,25,41],[-19],[-20,31],[-21],[-24],[-26,40],[-40,26],[-29,41],[-41,29],[-34],[-35],[-39],[-43,5,6,14,32],[-44,37,42],[-45,2,3,11],[-46,43],[-47,44,45],[-48,44],[-49,47],[-50,48],[-51,46,50],[-51,49],[-52,51],[52],[-18,53],[-28,54],[-17,55],[-26,56],[-29,56],[-40,57],[-41,57],[-13,58],[-22,58],[-25,58],[-30,59],[-38,59],[-23,60],[-27,60],[-33,61],[-36,61],[-55,62],[-54,62],[-62,63],[-53,63],[-57,64],[-56,-64,65],[-63,66],[-63,-65,67],[-58,68],[-58,-59,69],[-61,70],[-60,-61,71],[-71,72],[-68,-70,72],[-69,72],[-72,73],[-66,-73,74],[-67,74],[-74],[1,4,7,12,16,18,19,20,21,24,28,31,35,39],[8,13,15,17,22,23,25,26,29,30,33,34,36,38,39,40,41]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group\",\"index\":12,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":45,\"b\":30},{\"tag\":\"incompatible\",\"a\":92,\"b\":36},{\"tag\":\"incompatible\",\"a\":92,\"b\":37},{\"tag\":\"incompatible\",\"a\":92,\"b\":44},{\"tag\":\"incompatible\",\"a\":92,\"b\":50},{\"tag\":\"incompatible\",\"a\":93,\"b\":92},{\"tag\":\"incompatible\",\"a\":98,\"b\":27},{\"tag\":\"incompatible\",\"a\":98,\"b\":46},{\"tag\":\"incompatible\",\"a\":99,\"b\":98},{\"tag\":\"incompatible\",\"a\":106,\"b\":92},{\"tag\":\"incompatible\",\"a\":106,\"b\":98},{\"tag\":\"mate\",\"ridge\":321,\"a\":42,\"owners\":[62,64,75]},{\"tag\":\"mate\",\"ridge\":321,\"a\":48,\"owners\":[64,70,75]},{\"tag\":\"mate\",\"ridge\":322,\"a\":8,\"owners\":[87,92,97,101]},{\"tag\":\"mate\",\"ridge\":322,\"a\":33,\"owners\":[92,97,101]},{\"tag\":\"mate\",\"ridge\":322,\"a\":54,\"owners\":[87,92,97]},{\"tag\":\"mate\",\"ridge\":770,\"a\":99,\"owners\":[44,55,97,101]},{\"tag\":\"mate\",\"ridge\":642,\"a\":49,\"owners\":[83,89,94,96,100,101]},{\"tag\":\"mate\",\"ridge\":642,\"a\":55,\"owners\":[83,88,89,94,96,98]},{\"tag\":\"mate\",\"ridge\":642,\"a\":100,\"owners\":[43,49,83,88,96]},{\"tag\":\"mate\",\"ridge\":649,\"a\":43,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":178,\"a\":98,\"owners\":[45,84]},{\"tag\":\"mate\",\"ridge\":657,\"a\":73,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":672,\"a\":52,\"owners\":[104,105]},{\"tag\":\"mate\",\"ridge\":672,\"a\":71,\"owners\":[89,98,100,105]},{\"tag\":\"mate\",\"ridge\":672,\"a\":73,\"owners\":[89,94,100,104]},{\"tag\":\"mate\",\"ridge\":672,\"a\":76,\"owners\":[89,94,98,104,105]},{\"tag\":\"mate\",\"ridge\":672,\"a\":89,\"owners\":[71,73,76]},{\"tag\":\"mate\",\"ridge\":672,\"a\":94,\"owners\":[73,76,105]},{\"tag\":\"mate\",\"ridge\":356,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":344,\"a\":67,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":360,\"a\":70,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":480,\"a\":75,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":652,\"a\":83,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":652,\"a\":104,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":660,\"a\":88,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":660,\"a\":105,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":712,\"a\":96,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":840,\"a\":97,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":960,\"a\":101,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[36,37,50,93],\"full_literals\":[-43,5,6,14,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[99,106],\"full_literals\":[-44,37,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[27,30,46],\"full_literals\":[-45,2,3,11]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,44,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-51,46,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-52,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":62,\"full_literals\":[-18,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-28,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":55,\"full_literals\":[-17,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-26,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":88,\"full_literals\":[-29,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":104,\"full_literals\":[-40,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":105,\"full_literals\":[-41,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":49,\"full_literals\":[-13,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":71,\"full_literals\":[-22,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":76,\"full_literals\":[-25,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":89,\"full_literals\":[-30,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":100,\"full_literals\":[-38,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":73,\"full_literals\":[-23,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":84,\"full_literals\":[-27,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":12,\"member\":94,\"full_literals\":[-33,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":12,\"member\":98,\"full_literals\":[-36,61]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-63,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-59,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[11],\"right\":[12],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[11],\"right\":[12],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-61,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-66,-73,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[8,33,42,48,54,62,64,67,70,75,87,92,97,101]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[43,49,52,55,71,73,76,83,88,89,94,96,98,100,101,104,105]}]}"
  "p cnf 74 89\n-10 -3 0\n-31 -5 0\n-31 -6 0\n-31 -9 0\n-31 -14 0\n-32 -31 0\n-36 -2 0\n-36 -11 0\n-37 -36 0\n-42 -31 0\n-42 -36 0\n-7 18 19 24 0\n-12 19 21 24 0\n-1 28 31 35 39 0\n-4 31 35 39 0\n-16 28 31 35 0\n-37 9 17 35 39 0\n-13 26 30 33 34 38 39 0\n-17 26 29 30 33 34 36 0\n-38 8 13 26 29 34 0\n-8 22 0\n-36 10 27 0\n-23 13 0\n-15 40 41 0\n-22 30 36 38 41 0\n-23 30 33 38 40 0\n-25 30 33 36 40 41 0\n-30 22 23 25 0\n-33 23 25 41 0\n-19 0\n-20 31 0\n-21 0\n-24 0\n-26 40 0\n-40 26 0\n-29 41 0\n-41 29 0\n-34 0\n-35 0\n-39 0\n-43 5 6 14 32 0\n-44 37 42 0\n-45 2 3 11 0\n-46 43 0\n-47 44 45 0\n-48 44 0\n-49 47 0\n-50 48 0\n-51 46 50 0\n-51 49 0\n-52 51 0\n52 0\n-18 53 0\n-28 54 0\n-17 55 0\n-26 56 0\n-29 56 0\n-40 57 0\n-41 57 0\n-13 58 0\n-22 58 0\n-25 58 0\n-30 59 0\n-38 59 0\n-23 60 0\n-27 60 0\n-33 61 0\n-36 61 0\n-55 62 0\n-54 62 0\n-62 63 0\n-53 63 0\n-57 64 0\n-56 -64 65 0\n-63 66 0\n-63 -65 67 0\n-58 68 0\n-58 -59 69 0\n-61 70 0\n-60 -61 71 0\n-71 72 0\n-68 -70 72 0\n-69 72 0\n-72 73 0\n-66 -73 74 0\n-67 74 0\n-74 0\n1 4 7 12 16 18 19 20 21 24 28 31 35 39 0\n8 13 15 17 22 23 25 26 29 30 33 34 36 38 39 40 41 0\n"
  "90 -12 0 33 30 32 13 0\n91 51 0 52 51 0\n92 49 0 91 50 0\n93 47 0 92 47 0\n94 -67 0 87 86 0\n95 1 4 7 16 18 20 28 31 0 90 30 32 33 39 40 88 0\n96 8 13 15 17 22 23 25 26 29 30 33 36 38 40 41 0 38 40 89 0\n97 31 63 0 30 33 40 39 72 53 12 71 70 54 15 31 16 14 95 0\n98 63 0 40 39 91 71 69 55 97 2 3 4 5 6 10 17 41 42 44 46 49 48 0\n99 66 0 98 75 0\n100 -65 0 98 94 76 0\n101 -73 0 99 87 85 0\n102 -72 0 101 84 0\n103 -71 0 102 81 0\n104 -69 0 102 83 0\n105 13 41 23 15 22 17 25 26 29 30 33 36 38 40 0 96 21 0\n106 30 33 36 38 40 41 0 40 38 34 24 36 25 18 19 26 27 105 0\n107 -30 0 104 63 78 60 61 62 23 28 0\n108 -33 41 0 103 102 67 79 80 82 65 77 29 62 0\n109 -36 0 103 93 7 8 9 11 68 42 80 45 66 43 22 1 0\n110 40 41 0 109 107 104 38 108 36 34 106 64 78 60 61 20 21 0\n111 -40 0 100 35 58 56 73 74 0\n112 41 0 111 110 0\n113 29 0 112 37 0\n114 57 0 112 59 0\n115 56 0 113 57 0\n116 64 0 114 73 0\n117 0 115 116 100 74 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026.record013_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00026.record013
