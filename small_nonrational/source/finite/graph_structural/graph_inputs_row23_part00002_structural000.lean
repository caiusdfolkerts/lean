module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00002Frames
public import GraphInputsRow23Part00002Leaves
public import GraphInputsRow23Part00002Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00002.record042
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "d295aa98b6538ae1b91e2785e0fb49566a52d54d2b46d4749d1743de0ec3c8e63c4e9364d532cf0b92e2b4acab1ac9b16c3ba1e4751cc789c6745c570dd0f23f42a894a468a62584e0b81ed06a152519294951342d07703a0e4350e2328d1324d0b12c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12492492492492492492492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.leaf ([(facetIndex 1)])))
 (.branch 3
 (.leaf ([(facetIndex 2)]))
 (.leaf ([(facetIndex 3)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 4)]))
 (.leaf ([(facetIndex 5)])))
 (.branch 7
 (.leaf ([(facetIndex 6)]))
 (.leaf ([(facetIndex 7)])))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ([(facetIndex 8)]))
 (.leaf ([(facetIndex 9)])))
 (.branch 11
 (.leaf ([(facetIndex 10)]))
 (.leaf ([(facetIndex 11)]))))
 (.branch 14
 (.branch 13
 (.leaf ([(facetIndex 12)]))
 (.leaf ([(facetIndex 13)])))
 (.branch 15
 (.leaf ([(facetIndex 14)]))
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.leaf ([(facetIndex 16)])))))))
 (.branch 26
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ([(facetIndex 17)]))
 (.leaf ([(facetIndex 18)])))
 (.branch 20
 (.leaf ([(facetIndex 19)]))
 (.leaf ([(facetIndex 20)]))))
 (.branch 23
 (.branch 22
 (.leaf ([(facetIndex 21)]))
 (.leaf ([(facetIndex 22)])))
 (.branch 24
 (.leaf ([(facetIndex 23)]))
 (.branch 25
 (.leaf ([(facetIndex 24)]))
 (.leaf ([(facetIndex 25)]))))))
 (.branch 30
 (.branch 28
 (.branch 27
 (.leaf ([(facetIndex 26)]))
 (.leaf ([(facetIndex 27)])))
 (.branch 29
 (.leaf ([(facetIndex 28)]))
 (.leaf ([(facetIndex 29)]))))
 (.branch 32
 (.branch 31
 (.leaf ([(facetIndex 30)]))
 (.leaf ([(facetIndex 31)])))
 (.branch 33
 (.leaf ([(facetIndex 32)]))
 (.branch 34
 (.leaf ([(facetIndex 33)]))
 (.leaf ([(facetIndex 34)]))))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨6, sparse_nat% "228607de75c6da6585d65544d24503ce34c2ca2481c61440c2040"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 35
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 69), (facetIndex 71), (facetIndex 72)]))
 (.branch 2
 (.leaf ([(facetIndex 70), (facetIndex 73), (facetIndex 74)]))
 (.leaf ([(facetIndex 40), (facetIndex 49), (facetIndex 60), (facetIndex 68), (facetIndex 79)]))))
 (.branch 4
 (.leaf ([(facetIndex 80), (facetIndex 82), (facetIndex 83)]))
 (.branch 5
 (.leaf ([(facetIndex 81), (facetIndex 84), (facetIndex 85)]))
 (.leaf ([(facetIndex 54), (facetIndex 56), (facetIndex 57), (facetIndex 59), (facetIndex 63)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 45), (facetIndex 58), (facetIndex 61), (facetIndex 62)]))
 (.branch 8
 (.leaf ([(facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 78)]))))
 (.branch 11
 (.branch 10
 (.leaf ([(facetIndex 35), (facetIndex 37), (facetIndex 41), (facetIndex 42), (facetIndex 55)]))
 (.leaf ([(facetIndex 36), (facetIndex 46), (facetIndex 47), (facetIndex 50), (facetIndex 51), (facetIndex 52)])))
 (.branch 12
 (.leaf ([(facetIndex 38), (facetIndex 43), (facetIndex 44), (facetIndex 53)]))
 (.leaf ([(facetIndex 39), (facetIndex 48)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "44334328888110010277775662565595baaa2caa6bb992cb9a9z23;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 13
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped1_0000 : List Nat := [0, 1]
def grouped1_0001 : List Nat := [0, 1, 2, 3]
def grouped1_0002 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def grouped1_0003 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
def grouped1_0005 : List Nat := [2]
def grouped1_0006 : List Nat := [2, 3]
def grouped1_0007 : List Nat := [3]
def grouped1_0008 : List Nat := [4, 5, 6, 7]
def grouped1_0009 : List Nat := [8, 9, 10, 11]
def grouped1_0010 : List Nat := [8, 9, 10, 11, 12, 13, 14, 15, 16]
def grouped1_0011 : List Nat := [12, 13]
def grouped1_0012 : List Nat := [12, 13, 14, 15, 16]
def grouped1_0013 : List Nat := [14]
def grouped1_0014 : List Nat := [14, 15, 16]
def grouped1_0015 : List Nat := [15, 16]
def grouped1_0016 : List Nat := [17, 18]
def grouped1_0017 : List Nat := [17, 18, 19, 20]
def grouped1_0018 : List Nat := [17, 18, 19, 20, 21, 22, 23, 24, 25]
def grouped1_0019 : List Nat := [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]
def grouped1_0020 : List Nat := [19]
def grouped1_0021 : List Nat := [19, 20]
def grouped1_0022 : List Nat := [20]
def grouped1_0023 : List Nat := [21, 22]
def grouped1_0024 : List Nat := [21, 22, 23, 24, 25]
def grouped1_0025 : List Nat := [23]
def grouped1_0026 : List Nat := [23, 24, 25]
def grouped1_0027 : List Nat := [24]
def grouped1_0028 : List Nat := [24, 25]
def grouped1_0029 : List Nat := [25]
def grouped1_0030 : List Nat := [26, 27, 28, 29]
def grouped1_0031 : List Nat := [26, 27, 28, 29, 30, 31, 32, 33, 34]
def grouped1_0032 : List Nat := [30, 31]
def grouped1_0033 : List Nat := [30, 31, 32, 33, 34]
def grouped1_0034 : List Nat := [32]
def grouped1_0035 : List Nat := [32, 33, 34]
def grouped1_0036 : List Nat := [33]
def grouped1_0037 : List Nat := [33, 34]
def grouped1_0038 : List Nat := [34]
def grouped2_0039 : List Nat := [0]
def grouped2_0040 : List Nat := [0, 1, 2]
def grouped2_0041 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped2_0043 : List Nat := [1]
def grouped2_0044 : List Nat := [1, 2]
def grouped2_0045 : List Nat := [2]
def grouped2_0046 : List Nat := [3]
def grouped2_0047 : List Nat := [3, 4, 5]
def grouped2_0048 : List Nat := [4]
def grouped2_0049 : List Nat := [4, 5]
def grouped2_0050 : List Nat := [5]
def grouped2_0051 : List Nat := [6]
def grouped2_0052 : List Nat := [6, 7, 8]
def grouped2_0053 : List Nat := [6, 7, 8, 9, 10, 11, 12]
def grouped2_0054 : List Nat := [7]
def grouped2_0055 : List Nat := [7, 8]
def grouped2_0056 : List Nat := [8]
def grouped2_0057 : List Nat := [9]
def grouped2_0058 : List Nat := [9, 10]
def grouped2_0059 : List Nat := [9, 10, 11, 12]
def grouped2_0060 : List Nat := [10]
def grouped2_0061 : List Nat := [11]
def grouped2_0062 : List Nat := [11, 12]
def grouped2_0063 : List Nat := [12]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00002.record042" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"kind\":1,\"index\":3},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group\",\"kind\":1,\"index\":19},{\"tag\":\"group\",\"kind\":1,\"index\":24},{\"tag\":\"group\",\"kind\":1,\"index\":25},{\"tag\":\"group\",\"kind\":1,\"index\":33},{\"tag\":\"group\",\"kind\":1,\"index\":34},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0006\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0017\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0024\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0033\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0031\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group\",\"kind\":2,\"index\":10},{\"tag\":\"group\",\"kind\":2,\"index\":11},{\"tag\":\"group\",\"kind\":2,\"index\":12},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0044\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0040\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0049\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0041\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0055\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0058\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0062\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0062\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0059\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0059\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0059\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00002.record042" 129

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00002.record042" "{\"ridges\":[[3,67],[12,515],[14,67],[14,515],[14,577],[14,578],[16,515],[17,28],[18,41],[19,69],[20,21],[22,273],[24,545],[24,672],[25,577],[25,769],[26,28],[27,42],[28,70],[29,22],[31,274],[33,546],[34,578],[34,770],[38,67],[40,35],[40,67],[41,38],[41,545],[42,67],[44,515],[45,515],[45,641],[47,67],[48,25],[49,67],[51,35],[52,515],[53,515],[54,515],[55,35],[56,67],[58,515],[58,641],[58,642],[59,515],[61,769],[64,28],[64,41],[65,28],[65,69],[66,28],[67,28],[68,41],[68,69],[72,545],[73,273],[74,577],[74,769],[75,28],[75,42],[76,28],[76,70],[77,28],[78,28],[79,38],[79,70],[79,76],[82,38],[83,546],[83,672],[84,274],[85,770],[85,832]],\"owners\":[[20,21,[1,17,37,38,39,64,65,67],[71]],[29,22,[1,26,37,38,39,75,76,78],[82]],[19,69,[3,38,40,42,43,44],[65,68,70]],[65,69,[3,40,42,43,44],[19,38,68,70]],[68,69,[3,38,42,43,44],[19,40,65,70]],[28,70,[3,38,40,42,43,44],[76,79,81]],[76,70,[3,40,42,43,44],[28,38,79,81]],[79,70,[3,38,42,43,44],[28,40,76,81]],[48,25,[17,22,64,65,73],[5,46,47,66]],[18,41,[6,46,49,50,51,52],[64,68,69]],[64,41,[6,49,50,51,52],[18,46,68,69]],[68,41,[6,46,50,51,52],[18,49,64,69]],[27,42,[6,46,49,50,51,52],[75,79,80]],[75,42,[6,49,50,51,52],[27,46,79,80]],[22,273,[10,39,56,57,59],[67,73]],[73,273,[10,39,57,59],[22,56,67]],[31,274,[10,39,56,57,59],[78,84]],[84,274,[10,39,57,59],[31,56,78]],[24,545,[12,41,52,60,61],[72]],[41,545,[24],[12,52,60,61,72]],[72,545,[12,52,60,61],[24,41]],[33,546,[12,41,52,60,61],[83]],[83,546,[12,52,60,61],[33,41]],[14,577,[25,74],[44,53,60,62]],[25,577,[14,44,53,60,62],[74]],[74,577,[14,44,60,62],[25,53]],[14,578,[34,85],[44,53,60,62]],[34,578,[14,44,53,60,62],[85]],[45,641,[24],[15,58,62,63,72]],[58,641,[24,72],[15,45,62,63]],[58,642,[33,83],[15,45,62,63]],[25,769,[16,54,59,61,63],[74]],[61,769,[25,74],[16,54,59,63]],[74,769,[16,59,61,63],[25,54]],[34,770,[16,54,59,61,63],[85]],[85,770,[16,59,61,63],[34,54]],[17,28,[26,75,76,77,78],[64,65,66,67]],[26,28,[17,64,65,66,67],[75,76,77,78]],[64,28,[26,76,77,78],[17,65,66,67,75]],[65,28,[26,75,77,78],[17,64,66,67,76]],[66,28,[26,75,76,78],[17,64,65,67,77]],[67,28,[26,75,76,77],[17,64,65,66,78]],[75,28,[17,65,66,67],[26,64,76,77,78]],[76,28,[17,64,66,67],[26,65,75,77,78]],[77,28,[17,64,65,67],[26,66,75,76,78]],[78,28,[17,64,65,66],[26,67,75,76,77]],[79,76,[19,65,70],[28,68,76,81]],[24,672,[33,83],[72]],[83,672,[24],[33,72]],[85,832,[25],[34,74]]],\"edges\":[[18,[1,17,20,26,29,37,38,39,64,65,66,67,71,75,76,77,78,82]],[20,[3,19,28,38,40,42,43,44,65,68,70,76,79,81]],[25,[6,18,27,46,49,50,51,52,64,68,69,75,79,80]],[33,[10,22,31,39,56,57,59,67,73,78,84]],[38,[12,24,33,41,52,60,61,72,83]],[41,[14,25,34,44,53,60,62,74,85]],[44,[16,25,34,54,59,61,63,74,85]]],\"groupings\":[1,2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00002.record042" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00002.record042\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-25,-24],[-26,-25],[-27,-22],[-27,-23],[-27,-24],[-27,-25],[-27,-26],[-28,-3],[-28,-25],[-28,-27],[-29,-1],[-29,-24],[-29,-25],[-29,-26],[-29,-27],[-30,-6],[-30,-27],[-31,-22],[-31,-24],[-31,-27],[-31,-28],[-31,-29],[-32,-25],[-32,-27],[-32,-29],[-32,-31],[-33,-28],[-35,-4],[-35,-25],[-36,-30],[-36,-31],[-37,-5],[-37,-27],[-37,-28],[-38,-28],[-39,-24],[-39,-27],[-39,-28],[-40,-2],[-40,-23],[-40,-25],[-40,-27],[-40,-29],[-40,-30],[-40,-31],[-40,-33],[-40,-34],[-40,-36],[-40,-38],[-40,-39],[-41,-39],[-41,-40],[-42,-33],[-42,-39],[-44,-35],[-45,-29],[-45,-42],[-46,-35],[-47,-7],[-47,-41],[-47,-46],[-48,-6],[-48,-31],[-48,-40],[-48,-47],[-49,-7],[-49,-41],[-49,-46],[-49,-48],[-50,-5],[-50,-39],[-50,-47],[-50,-49],[-54,-35],[-55,-8],[-55,-22],[-55,-51],[-55,-52],[-55,-53],[-55,-54],[-56,-28],[-56,-55],[-57,-26],[-57,-36],[-58,-29],[-58,-42],[-59,-31],[-60,-57],[-61,-14],[-61,-39],[-65,-35],[-66,-15],[-66,-22],[-66,-62],[-66,-63],[-66,-64],[-66,-65],[-67,-28],[-67,-66],[-68,-36],[-68,-66],[-69,-29],[-69,-42],[-70,-31],[-71,-60],[-72,-39],[-11,1,8,24,25,26,51,52,54],[-18,1,15,24,25,26,62,63,65],[-27,-38,-42],[-28,-66,-69],[-2,-6,-36],[-2,-6,-43],[-6,-25,-36],[-6,-27,-34],[-6,-27,-43],[-6,-29,-36],[-10,2,25,27,29,30,31],[-52,2,27,29,30,31],[-55,2,25,29,30,31],[-17,2,25,27,29,30,31],[-63,2,27,29,30,31],[-66,2,25,29,30,31],[-35,8,12,51,52,60],[-9,3,33,36,37,38,39],[-51,3,36,37,38,39],[-55,3,33,37,38,39],[-16,3,33,36,37,38,39],[-62,3,36,37,38,39],[-12,4,26,43,44,46],[-60,4,26,44,46],[-19,4,26,43,44,46],[-71,4,26,44,46],[-5,-6,-7],[-5,-6,-32],[-5,-6,-41],[-5,-6,-45],[-5,-6,-46],[-5,-7,-31],[-5,-7,-40],[-5,-31,-41],[-5,-31,-45],[-5,-31,-46],[-5,-40,-46],[-6,-7,-39],[-6,-39,-46],[-7,-31,-39],[-31,-39,-45],[-31,-39,-46],[-13,5,28,39,47,48],[-28,13],[-59,5,39,47,48],[-20,5,28,39,47,48],[-70,5,39,47,48],[-6,14,61],[-14,6,31,40,47,49],[-61,6,31,47,49],[-6,21,72],[-21,6,31,40,47,49],[-32,13],[-45,13,59],[-45,20,70],[-14,7,41,46,48,50],[-48,14,61],[-61,7,46,48,50],[-21,7,41,46,48,50],[-72,7,46,48,50],[-8,15,62,63,64,65],[-15,8,51,52,53,54],[-51,15,63,64,65],[-52,15,62,64,65],[-53,15,62,63,65],[-54,15,62,63,64],[-62,8,52,53,54],[-63,8,51,53,54],[-64,8,51,52,54],[-65,8,51,52,53],[-66,10,52,57],[-13,20,70],[-70,13],[-72,14],[-2,73],[-6,74],[-10,75],[-13,76],[-14,77],[-20,78],[-21,79],[-73,80],[-80,81],[-81,82],[-74,83],[-83,84],[-84,85],[-82,-85,86],[-75,87],[-87,88],[-76,-77,89],[-89,90],[-90,91],[-88,92],[-88,-91,93],[-78,-79,94],[-94,95],[-95,96],[-96,97],[-92,-97,98],[-93,98],[-86,-98,99],[-99],[-100,56,58,59],[-101,57,60,61],[-102,27,36,47,55,66],[-36,102],[-55,102],[-103,67,69,70],[-104,68,71,72],[-105,32,45,48,49],[-106,51,52,53,54],[-107,62,63,64,65],[-108,22,24,28,29,42],[-109,23,33,34,37,38,39],[-110,25,30,31,40],[-111,26,35],[-112,101],[-113,100],[-113,112],[-114,104],[-115,103],[-115,114],[-116,113],[-116,115],[-117,106,107],[-118,105,117],[-120,105],[-119,117],[-121,108],[-121,109],[-122,110,111],[-123,110],[-123,111],[-124,121,122],[-125,121,123],[-126,121],[-125,122],[-126,123],[-127,118,126],[-128,118],[-127,119,125],[-128,119,126],[-127,120,124],[-129,116,128],[-129,127],[129],[1,8,11,15,18,24,25,26,51,52,53,54,58,62,63,64,65,69],[2,10,17,25,27,29,30,31,52,55,57,63,66,68],[3,9,16,33,36,37,38,39,51,55,56,62,66,67],[4,12,19,26,43,44,46,54,60,65,71],[5,13,20,28,39,47,48,59,70],[6,14,21,31,40,47,49,61,72],[7,14,21,41,46,48,50,61,72]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"index\":3,\"kind\":1},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group\",\"index\":19,\"kind\":1},{\"tag\":\"group\",\"index\":24,\"kind\":1},{\"tag\":\"group\",\"index\":25,\"kind\":1},{\"tag\":\"group\",\"index\":33,\"kind\":1},{\"tag\":\"group\",\"index\":34,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":2},{\"tag\":\"group\",\"index\":11,\"kind\":2},{\"tag\":\"group\",\"index\":12,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":36},{\"tag\":\"incompatible\",\"a\":40,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":41,\"b\":6},{\"tag\":\"incompatible\",\"a\":41,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":40},{\"tag\":\"incompatible\",\"a\":42,\"b\":1},{\"tag\":\"incompatible\",\"a\":42,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":38},{\"tag\":\"incompatible\",\"a\":42,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":40},{\"tag\":\"incompatible\",\"a\":43,\"b\":14},{\"tag\":\"incompatible\",\"a\":43,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":35},{\"tag\":\"incompatible\",\"a\":44,\"b\":37},{\"tag\":\"incompatible\",\"a\":44,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":42},{\"tag\":\"incompatible\",\"a\":45,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":40},{\"tag\":\"incompatible\",\"a\":45,\"b\":42},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":41},{\"tag\":\"incompatible\",\"a\":48,\"b\":10},{\"tag\":\"incompatible\",\"a\":48,\"b\":38},{\"tag\":\"incompatible\",\"a\":49,\"b\":43},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":12},{\"tag\":\"incompatible\",\"a\":50,\"b\":40},{\"tag\":\"incompatible\",\"a\":50,\"b\":41},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":52,\"b\":37},{\"tag\":\"incompatible\",\"a\":52,\"b\":40},{\"tag\":\"incompatible\",\"a\":52,\"b\":41},{\"tag\":\"incompatible\",\"a\":53,\"b\":3},{\"tag\":\"incompatible\",\"a\":53,\"b\":36},{\"tag\":\"incompatible\",\"a\":53,\"b\":38},{\"tag\":\"incompatible\",\"a\":53,\"b\":40},{\"tag\":\"incompatible\",\"a\":53,\"b\":42},{\"tag\":\"incompatible\",\"a\":53,\"b\":43},{\"tag\":\"incompatible\",\"a\":53,\"b\":44},{\"tag\":\"incompatible\",\"a\":53,\"b\":46},{\"tag\":\"incompatible\",\"a\":53,\"b\":47},{\"tag\":\"incompatible\",\"a\":53,\"b\":49},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":55,\"b\":46},{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":57,\"b\":48},{\"tag\":\"incompatible\",\"a\":58,\"b\":42},{\"tag\":\"incompatible\",\"a\":58,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":48},{\"tag\":\"incompatible\",\"a\":60,\"b\":16},{\"tag\":\"incompatible\",\"a\":60,\"b\":54},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":14},{\"tag\":\"incompatible\",\"a\":61,\"b\":44},{\"tag\":\"incompatible\",\"a\":61,\"b\":53},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":16},{\"tag\":\"incompatible\",\"a\":62,\"b\":54},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":12},{\"tag\":\"incompatible\",\"a\":63,\"b\":52},{\"tag\":\"incompatible\",\"a\":63,\"b\":60},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":67,\"b\":48},{\"tag\":\"incompatible\",\"a\":68,\"b\":17},{\"tag\":\"incompatible\",\"a\":68,\"b\":35},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":41},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":39},{\"tag\":\"incompatible\",\"a\":70,\"b\":49},{\"tag\":\"incompatible\",\"a\":71,\"b\":42},{\"tag\":\"incompatible\",\"a\":71,\"b\":55},{\"tag\":\"incompatible\",\"a\":72,\"b\":44},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":25},{\"tag\":\"incompatible\",\"a\":74,\"b\":52},{\"tag\":\"incompatible\",\"a\":78,\"b\":48},{\"tag\":\"incompatible\",\"a\":79,\"b\":26},{\"tag\":\"incompatible\",\"a\":79,\"b\":35},{\"tag\":\"incompatible\",\"a\":79,\"b\":75},{\"tag\":\"incompatible\",\"a\":79,\"b\":76},{\"tag\":\"incompatible\",\"a\":79,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":41},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"incompatible\",\"a\":81,\"b\":49},{\"tag\":\"incompatible\",\"a\":81,\"b\":79},{\"tag\":\"incompatible\",\"a\":82,\"b\":42},{\"tag\":\"incompatible\",\"a\":82,\"b\":55},{\"tag\":\"incompatible\",\"a\":83,\"b\":44},{\"tag\":\"incompatible\",\"a\":84,\"b\":73},{\"tag\":\"incompatible\",\"a\":85,\"b\":52},{\"tag\":\"mate\",\"ridge\":21,\"a\":20,\"owners\":[1,17,37,38,39,64,65,67]},{\"tag\":\"mate\",\"ridge\":22,\"a\":29,\"owners\":[1,26,37,38,39,75,76,78]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[40,51,55]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[41,79,82]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[3,14,49]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[3,14,56]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[14,38,49]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[14,40,47]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[14,40,56]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[14,42,49]},{\"tag\":\"mate\",\"ridge\":69,\"a\":19,\"owners\":[3,38,40,42,43,44]},{\"tag\":\"mate\",\"ridge\":69,\"a\":65,\"owners\":[3,40,42,43,44]},{\"tag\":\"mate\",\"ridge\":69,\"a\":68,\"owners\":[3,38,42,43,44]},{\"tag\":\"mate\",\"ridge\":70,\"a\":28,\"owners\":[3,38,40,42,43,44]},{\"tag\":\"mate\",\"ridge\":70,\"a\":76,\"owners\":[3,40,42,43,44]},{\"tag\":\"mate\",\"ridge\":70,\"a\":79,\"owners\":[3,38,42,43,44]},{\"tag\":\"mate\",\"ridge\":25,\"a\":48,\"owners\":[17,22,64,65,73]},{\"tag\":\"mate\",\"ridge\":41,\"a\":18,\"owners\":[6,46,49,50,51,52]},{\"tag\":\"mate\",\"ridge\":41,\"a\":64,\"owners\":[6,49,50,51,52]},{\"tag\":\"mate\",\"ridge\":41,\"a\":68,\"owners\":[6,46,50,51,52]},{\"tag\":\"mate\",\"ridge\":42,\"a\":27,\"owners\":[6,46,49,50,51,52]},{\"tag\":\"mate\",\"ridge\":42,\"a\":75,\"owners\":[6,49,50,51,52]},{\"tag\":\"mate\",\"ridge\":273,\"a\":22,\"owners\":[10,39,56,57,59]},{\"tag\":\"mate\",\"ridge\":273,\"a\":73,\"owners\":[10,39,57,59]},{\"tag\":\"mate\",\"ridge\":274,\"a\":31,\"owners\":[10,39,56,57,59]},{\"tag\":\"mate\",\"ridge\":274,\"a\":84,\"owners\":[10,39,57,59]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[12,14,16]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[12,14,45]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[12,14,54]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[12,14,58]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[12,14,59]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[12,16,44]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[12,16,53]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[12,44,54]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[12,44,58]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[12,44,59]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[12,53,59]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[14,16,52]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[14,52,59]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[16,44,52]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[44,52,58]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[44,52,59]},{\"tag\":\"mate\",\"ridge\":545,\"a\":24,\"owners\":[12,41,52,60,61]},{\"tag\":\"mate\",\"ridge\":545,\"a\":41,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":545,\"a\":72,\"owners\":[12,52,60,61]},{\"tag\":\"mate\",\"ridge\":546,\"a\":33,\"owners\":[12,41,52,60,61]},{\"tag\":\"mate\",\"ridge\":546,\"a\":83,\"owners\":[12,52,60,61]},{\"tag\":\"mate\",\"ridge\":577,\"a\":14,\"owners\":[25,74]},{\"tag\":\"mate\",\"ridge\":577,\"a\":25,\"owners\":[14,44,53,60,62]},{\"tag\":\"mate\",\"ridge\":577,\"a\":74,\"owners\":[14,44,60,62]},{\"tag\":\"mate\",\"ridge\":578,\"a\":14,\"owners\":[34,85]},{\"tag\":\"mate\",\"ridge\":578,\"a\":34,\"owners\":[14,44,53,60,62]},{\"tag\":\"mate\",\"ridge\":641,\"a\":45,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":641,\"a\":58,\"owners\":[24,72]},{\"tag\":\"mate\",\"ridge\":642,\"a\":58,\"owners\":[33,83]},{\"tag\":\"mate\",\"ridge\":769,\"a\":25,\"owners\":[16,54,59,61,63]},{\"tag\":\"mate\",\"ridge\":769,\"a\":61,\"owners\":[25,74]},{\"tag\":\"mate\",\"ridge\":769,\"a\":74,\"owners\":[16,59,61,63]},{\"tag\":\"mate\",\"ridge\":770,\"a\":34,\"owners\":[16,54,59,61,63]},{\"tag\":\"mate\",\"ridge\":770,\"a\":85,\"owners\":[16,59,61,63]},{\"tag\":\"mate\",\"ridge\":28,\"a\":17,\"owners\":[26,75,76,77,78]},{\"tag\":\"mate\",\"ridge\":28,\"a\":26,\"owners\":[17,64,65,66,67]},{\"tag\":\"mate\",\"ridge\":28,\"a\":64,\"owners\":[26,76,77,78]},{\"tag\":\"mate\",\"ridge\":28,\"a\":65,\"owners\":[26,75,77,78]},{\"tag\":\"mate\",\"ridge\":28,\"a\":66,\"owners\":[26,75,76,78]},{\"tag\":\"mate\",\"ridge\":28,\"a\":67,\"owners\":[26,75,76,77]},{\"tag\":\"mate\",\"ridge\":28,\"a\":75,\"owners\":[17,65,66,67]},{\"tag\":\"mate\",\"ridge\":28,\"a\":76,\"owners\":[17,64,66,67]},{\"tag\":\"mate\",\"ridge\":28,\"a\":77,\"owners\":[17,64,65,67]},{\"tag\":\"mate\",\"ridge\":28,\"a\":78,\"owners\":[17,64,65,66]},{\"tag\":\"mate\",\"ridge\":76,\"a\":79,\"owners\":[19,65,70]},{\"tag\":\"mate\",\"ridge\":672,\"a\":24,\"owners\":[33,83]},{\"tag\":\"mate\",\"ridge\":672,\"a\":83,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":832,\"a\":85,\"owners\":[25]},{\"tag\":\"group_take\",\"kind\":1,\"index\":3,\"member\":3,\"full_literals\":[-2,73]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-6,74]},{\"tag\":\"group_take\",\"kind\":1,\"index\":19,\"member\":19,\"full_literals\":[-10,75]},{\"tag\":\"group_take\",\"kind\":1,\"index\":24,\"member\":24,\"full_literals\":[-13,76]},{\"tag\":\"group_take\",\"kind\":1,\"index\":25,\"member\":25,\"full_literals\":[-14,77]},{\"tag\":\"group_take\",\"kind\":1,\"index\":33,\"member\":33,\"full_literals\":[-20,78]},{\"tag\":\"group_take\",\"kind\":1,\"index\":34,\"member\":34,\"full_literals\":[-21,79]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped1_0005\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-73,80],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-80,81],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,82],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15,16],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"grouped1_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,83],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13],\"right\":[14,15,16],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,84],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15,16],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0012\",\"joined_name\":\"grouped1_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-84,85],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15,16],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-82,-85,86],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[19],\"right\":[20],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,87],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18],\"right\":[19,20],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,88],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24],\"right\":[25],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-77,89],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[23],\"right\":[24,25],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-89,90],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22],\"right\":[23,24,25],\"left_name\":\"grouped1_0023\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0024\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-90,91],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19,20],\"right\":[21,22,23,24,25],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-88,false,92],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19,20],\"right\":[21,22,23,24,25],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-88,-91,93],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[33],\"right\":[34],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0038\",\"joined_name\":\"grouped1_0037\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-78,-79,94],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[32],\"right\":[33,34],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0037\",\"joined_name\":\"grouped1_0035\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-94,95],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[30,31],\"right\":[32,33,34],\"left_name\":\"grouped1_0032\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0033\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-95,96],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[26,27,28,29],\"right\":[30,31,32,33,34],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0031\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-96,97],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19,20,21,22,23,24,25],\"right\":[26,27,28,29,30,31,32,33,34],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0031\",\"joined_name\":\"grouped1_0019\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-92,-97,98],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19,20,21,22,23,24,25],\"right\":[26,27,28,29,30,31,32,33,34],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0031\",\"joined_name\":\"grouped1_0019\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-93,false,98],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],\"right\":[17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-86,-98,99],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[69,71,72],\"full_literals\":[-100,56,58,59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[70,73,74],\"full_literals\":[-101,57,60,61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[40,49,60,68,79],\"full_literals\":[-102,27,36,47,55,66]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":49,\"full_literals\":[-36,102]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":68,\"full_literals\":[-55,102]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[80,82,83],\"full_literals\":[-103,67,69,70]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[81,84,85],\"full_literals\":[-104,68,71,72]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[45,58,61,62],\"full_literals\":[-105,32,45,48,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[64,65,66,67],\"full_literals\":[-106,51,52,53,54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[75,76,77,78],\"full_literals\":[-107,62,63,64,65]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[35,37,41,42,55],\"full_literals\":[-108,22,24,28,29,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":10,\"members\":[36,46,47,50,51,52],\"full_literals\":[-109,23,33,34,37,38,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":11,\"members\":[38,43,44,53],\"full_literals\":[-110,25,30,31,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":12,\"members\":[39,48],\"full_literals\":[-111,26,35]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0045\",\"joined_name\":\"grouped2_0044\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-112,101,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0044\",\"joined_name\":\"grouped2_0040\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-113,100,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0044\",\"joined_name\":\"grouped2_0040\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-113,false,112],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0048\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0049\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-114,104,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-115,103,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-115,false,114],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0041\",\"a\":2,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-116,113,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0041\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-116,false,115],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0054\",\"right_name\":\"grouped2_0056\",\"joined_name\":\"grouped2_0055\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-117,106,107],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-118,105,117],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-120,105,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0052\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-119,false,117],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-121,108,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0057\",\"right_name\":\"grouped2_0060\",\"joined_name\":\"grouped2_0058\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-121,false,109],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[11],\"right\":[12],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"grouped2_0062\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-122,110,111],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[11],\"right\":[12],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"grouped2_0062\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-123,110,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[11],\"right\":[12],\"left_name\":\"grouped2_0061\",\"right_name\":\"grouped2_0063\",\"joined_name\":\"grouped2_0062\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-123,false,111],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-124,121,122],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-125,121,123],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-126,121,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-125,false,122],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped2_0058\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0059\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-126,false,123],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0053\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-127,118,126],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0053\",\"a\":0,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-128,118,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-127,119,125],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-128,119,126],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0059\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-127,120,124],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-129,116,128],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"groupKind2\",\"a\":6,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-129,false,127],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":18,\"owners\":[1,17,20,26,29,37,38,39,64,65,66,67,71,75,76,77,78,82]},{\"tag\":\"edge\",\"edge\":20,\"owners\":[3,19,28,38,40,42,43,44,65,68,70,76,79,81]},{\"tag\":\"edge\",\"edge\":25,\"owners\":[6,18,27,46,49,50,51,52,64,68,69,75,79,80]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[10,22,31,39,56,57,59,67,73,78,84]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[12,24,33,41,52,60,61,72,83]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[14,25,34,44,53,60,62,74,85]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[16,25,34,54,59,61,63,74,85]}]}"
  "p cnf 129 260\n-25 -24 0\n-26 -25 0\n-27 -22 0\n-27 -23 0\n-27 -24 0\n-27 -25 0\n-27 -26 0\n-28 -3 0\n-28 -25 0\n-28 -27 0\n-29 -1 0\n-29 -24 0\n-29 -25 0\n-29 -26 0\n-29 -27 0\n-30 -6 0\n-30 -27 0\n-31 -22 0\n-31 -24 0\n-31 -27 0\n-31 -28 0\n-31 -29 0\n-32 -25 0\n-32 -27 0\n-32 -29 0\n-32 -31 0\n-33 -28 0\n-35 -4 0\n-35 -25 0\n-36 -30 0\n-36 -31 0\n-37 -5 0\n-37 -27 0\n-37 -28 0\n-38 -28 0\n-39 -24 0\n-39 -27 0\n-39 -28 0\n-40 -2 0\n-40 -23 0\n-40 -25 0\n-40 -27 0\n-40 -29 0\n-40 -30 0\n-40 -31 0\n-40 -33 0\n-40 -34 0\n-40 -36 0\n-40 -38 0\n-40 -39 0\n-41 -39 0\n-41 -40 0\n-42 -33 0\n-42 -39 0\n-44 -35 0\n-45 -29 0\n-45 -42 0\n-46 -35 0\n-47 -7 0\n-47 -41 0\n-47 -46 0\n-48 -6 0\n-48 -31 0\n-48 -40 0\n-48 -47 0\n-49 -7 0\n-49 -41 0\n-49 -46 0\n-49 -48 0\n-50 -5 0\n-50 -39 0\n-50 -47 0\n-50 -49 0\n-54 -35 0\n-55 -8 0\n-55 -22 0\n-55 -51 0\n-55 -52 0\n-55 -53 0\n-55 -54 0\n-56 -28 0\n-56 -55 0\n-57 -26 0\n-57 -36 0\n-58 -29 0\n-58 -42 0\n-59 -31 0\n-60 -57 0\n-61 -14 0\n-61 -39 0\n-65 -35 0\n-66 -15 0\n-66 -22 0\n-66 -62 0\n-66 -63 0\n-66 -64 0\n-66 -65 0\n-67 -28 0\n-67 -66 0\n-68 -36 0\n-68 -66 0\n-69 -29 0\n-69 -42 0\n-70 -31 0\n-71 -60 0\n-72 -39 0\n-11 1 8 24 25 26 51 52 54 0\n-18 1 15 24 25 26 62 63 65 0\n-27 -38 -42 0\n-28 -66 -69 0\n-2 -6 -36 0\n-2 -6 -43 0\n-6 -25 -36 0\n-6 -27 -34 0\n-6 -27 -43 0\n-6 -29 -36 0\n-10 2 25 27 29 30 31 0\n-52 2 27 29 30 31 0\n-55 2 25 29 30 31 0\n-17 2 25 27 29 30 31 0\n-63 2 27 29 30 31 0\n-66 2 25 29 30 31 0\n-35 8 12 51 52 60 0\n-9 3 33 36 37 38 39 0\n-51 3 36 37 38 39 0\n-55 3 33 37 38 39 0\n-16 3 33 36 37 38 39 0\n-62 3 36 37 38 39 0\n-12 4 26 43 44 46 0\n-60 4 26 44 46 0\n-19 4 26 43 44 46 0\n-71 4 26 44 46 0\n-5 -6 -7 0\n-5 -6 -32 0\n-5 -6 -41 0\n-5 -6 -45 0\n-5 -6 -46 0\n-5 -7 -31 0\n-5 -7 -40 0\n-5 -31 -41 0\n-5 -31 -45 0\n-5 -31 -46 0\n-5 -40 -46 0\n-6 -7 -39 0\n-6 -39 -46 0\n-7 -31 -39 0\n-31 -39 -45 0\n-31 -39 -46 0\n-13 5 28 39 47 48 0\n-28 13 0\n-59 5 39 47 48 0\n-20 5 28 39 47 48 0\n-70 5 39 47 48 0\n-6 14 61 0\n-14 6 31 40 47 49 0\n-61 6 31 47 49 0\n-6 21 72 0\n-21 6 31 40 47 49 0\n-32 13 0\n-45 13 59 0\n-45 20 70 0\n-14 7 41 46 48 50 0\n-48 14 61 0\n-61 7 46 48 50 0\n-21 7 41 46 48 50 0\n-72 7 46 48 50 0\n-8 15 62 63 64 65 0\n-15 8 51 52 53 54 0\n-51 15 63 64 65 0\n-52 15 62 64 65 0\n-53 15 62 63 65 0\n-54 15 62 63 64 0\n-62 8 52 53 54 0\n-63 8 51 53 54 0\n-64 8 51 52 54 0\n-65 8 51 52 53 0\n-66 10 52 57 0\n-13 20 70 0\n-70 13 0\n-72 14 0\n-2 73 0\n-6 74 0\n-10 75 0\n-13 76 0\n-14 77 0\n-20 78 0\n-21 79 0\n-73 80 0\n-80 81 0\n-81 82 0\n-74 83 0\n-83 84 0\n-84 85 0\n-82 -85 86 0\n-75 87 0\n-87 88 0\n-76 -77 89 0\n-89 90 0\n-90 91 0\n-88 92 0\n-88 -91 93 0\n-78 -79 94 0\n-94 95 0\n-95 96 0\n-96 97 0\n-92 -97 98 0\n-93 98 0\n-86 -98 99 0\n-99 0\n-100 56 58 59 0\n-101 57 60 61 0\n-102 27 36 47 55 66 0\n-36 102 0\n-55 102 0\n-103 67 69 70 0\n-104 68 71 72 0\n-105 32 45 48 49 0\n-106 51 52 53 54 0\n-107 62 63 64 65 0\n-108 22 24 28 29 42 0\n-109 23 33 34 37 38 39 0\n-110 25 30 31 40 0\n-111 26 35 0\n-112 101 0\n-113 100 0\n-113 112 0\n-114 104 0\n-115 103 0\n-115 114 0\n-116 113 0\n-116 115 0\n-117 106 107 0\n-118 105 117 0\n-120 105 0\n-119 117 0\n-121 108 0\n-121 109 0\n-122 110 111 0\n-123 110 0\n-123 111 0\n-124 121 122 0\n-125 121 123 0\n-126 121 0\n-125 122 0\n-126 123 0\n-127 118 126 0\n-128 118 0\n-127 119 125 0\n-128 119 126 0\n-127 120 124 0\n-129 116 128 0\n-129 127 0\n129 0\n1 8 11 15 18 24 25 26 51 52 53 54 58 62 63 64 65 69 0\n2 10 17 25 27 29 30 31 52 55 57 63 66 68 0\n3 9 16 33 36 37 38 39 51 55 56 62 66 67 0\n4 12 19 26 43 44 46 54 60 65 71 0\n5 13 20 28 39 47 48 59 70 0\n6 14 21 31 40 47 49 61 72 0\n7 14 21 41 46 48 50 61 72 0\n"
  "261 127 0 253 252 0\n262 -40 37 39 -109 0 40 46 47 49 221 0\n263 -6 -5 48 49 -105 0 134 136 217 0\n264 -48 47 0 62 63 64 69 156 155 163 0\n265 6 14 40 31 49 47 0 180 156 158 259 0\n266 -25 -111 0 2 29 223 0\n267 6 40 49 31 47 0 155 265 0\n268 40 31 49 47 -123 0 240 266 239 222 16 267 0\n269 -40 -66 0 39 41 43 44 45 122 0\n270 -14 89 57 -104 -101 5 -105 68 47 49 0 264 89 185 211 197 105 184 216 150 159 179 106 152 217 161 0\n271 57 98 31 -66 47 49 0 261 253 207 95 94 96 97 219 92 170 169 171 172 218 232 235 269 268 245 249 251 231 229 227 230 226 224 228 267 264 246 233 263 101 99 177 183 195 196 200 201 206 199 205 198 204 203 270 180 154 157 90 187 153 151 202 215 186 110 178 258 0\n272 -2 -111 31 -66 47 49 0 209 269 267 182 191 192 193 97 96 95 92 169 94 170 167 112 181 188 189 190 194 208 271 83 88 223 28 55 58 123 129 0\n273 -29 -105 48 49 0 25 56 217 0\n274 25 31 -66 47 49 0 261 264 95 94 96 97 219 92 170 169 171 172 218 232 269 268 245 246 233 273 267 16 235 248 244 222 122 238 272 0\n275 31 -66 47 49 0 261 269 95 94 96 97 219 92 170 169 171 172 218 232 235 248 93 264 268 245 242 246 236 233 273 274 1 9 23 220 217 57 0\n276 -45 -31 47 0 87 21 264 160 147 141 149 0\n277 -66 47 49 0 261 253 264 92 93 94 95 96 97 99 170 172 169 219 171 218 232 275 19 21 22 26 104 276 217 233 246 247 243 251 236 231 220 228 103 215 0\n278 -31 -102 47 49 0 261 253 277 264 18 19 20 21 22 26 31 87 276 212 217 75 77 78 79 80 82 174 175 176 173 218 219 232 233 246 247 243 251 236 230 220 225 86 210 0\n279 -123 29 -102 47 49 0 278 277 240 268 266 39 42 44 48 119 212 0\n280 27 55 29 -102 47 49 0 278 277 212 30 48 84 100 267 111 113 118 121 117 120 255 0\n281 -35 43 26 0 28 55 58 74 91 130 129 132 131 257 0\n282 -27 29 28 -124 31 47 49 0 3 4 5 6 7 17 33 37 42 222 267 114 115 281 223 238 241 236 237 220 53 109 221 0\n283 29 28 105 -102 47 49 0 261 234 250 278 279 245 246 233 282 280 75 77 78 79 80 174 175 176 173 218 219 232 0\n284 -29 -102 47 49 0 278 277 11 12 13 14 15 43 85 102 267 116 212 75 77 78 79 80 168 174 175 176 173 107 108 254 0\n285 -28 -102 47 49 0 284 8 10 27 34 35 38 280 126 0\n286 5 39 28 47 0 264 153 151 152 149 258 0\n287 39 -109 -102 47 49 0 284 285 283 278 264 286 32 263 262 267 0\n288 -55 -102 47 49 0 261 285 284 279 75 76 77 78 79 80 174 175 176 173 218 219 232 235 248 242 236 237 287 36 54 220 0\n289 -102 47 49 0 264 278 284 285 283 288 280 24 37 42 217 286 267 136 0\n290 7 41 50 46 48 0 162 166 164 165 260 0\n291 -6 -5 48 0 70 133 137 135 290 0\n292 -41 -5 47 49 0 264 291 52 140 267 0\n293 -7 -5 47 49 0 264 291 138 139 267 0\n294 -5 47 49 0 264 70 291 292 293 290 143 142 267 0\n295 -46 -39 47 49 0 50 148 145 267 0\n296 -39 47 49 0 264 50 51 71 295 290 144 146 267 0\n297 47 49 0 277 289 213 214 294 296 286 8 27 34 35 81 98 125 128 124 127 256 0\n298 -47 0 59 60 61 65 72 290 0\n299 -48 0 298 264 0\n300 49 0 298 297 0\n301 -7 0 300 66 0\n302 -41 0 300 67 0\n303 -46 0 300 68 0\n304 -50 0 300 73 0\n305 0 301 303 304 302 299 290 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00002.record042

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00002.record097
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "538ce1b83ee4731ac719566394e695356352d54d3346d4749d17783d0ec370f23a8f13a4e33c2ccb8ad2b1ad1b0ee8751e2729c6725c3743c8f07c3c528c61382ec46918c54946439314950d44d0b41dc0e8350cc388d0b12c2b21c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "492492492492492492492492492492492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 75)]))
 (.leaf ([(facetIndex 34), (facetIndex 37), (facetIndex 41), (facetIndex 44), (facetIndex 51)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 33), (facetIndex 35), (facetIndex 38), (facetIndex 63)]))
 (.branch 4
 (.leaf ([(facetIndex 29), (facetIndex 32), (facetIndex 39), (facetIndex 40), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 72)]))
 (.leaf ([(facetIndex 66), (facetIndex 68), (facetIndex 69), (facetIndex 70), (facetIndex 71)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 55), (facetIndex 58), (facetIndex 59), (facetIndex 60)]))
 (.branch 7
 (.leaf ([(facetIndex 36), (facetIndex 62), (facetIndex 64)]))
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 52), (facetIndex 53), (facetIndex 54)]))))
 (.branch 9
 (.leaf ([(facetIndex 42), (facetIndex 65), (facetIndex 67)]))
 (.branch 10
 (.leaf ([(facetIndex 56), (facetIndex 57), (facetIndex 61)]))
 (.leaf ([(facetIndex 31), (facetIndex 43), (facetIndex 45)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "344448486269555995777177333a1a81332162123a23z1d;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [4]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6, 7]
def grouped2_0010 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0011 : List Nat := [6]
def grouped2_0012 : List Nat := [6, 7]
def grouped2_0013 : List Nat := [7]
def grouped2_0014 : List Nat := [8, 9, 10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00002.record097" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00002.record097" 29

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00002.record097" "{\"ridges\":[[7,546],[10,642],[11,515],[36,546],[38,642],[43,546],[46,546],[47,642],[49,546],[50,546],[52,642],[53,515],[54,642],[62,545],[64,641],[66,545],[68,769],[69,545],[70,545],[71,641]],\"owners\":[[11,515,[7,10,36,38,43,46,47,52],[45,48,53]],[53,515,[7,10,36,38,43,46,47],[11,45,48,52]],[62,545,[7,43,49,50],[21,36,66,69,70]],[66,545,[7,36,49,50],[21,43,62,69,70]],[69,545,[7,36,43,50],[21,49,62,66,70]],[70,545,[7,36,43,49],[21,50,62,66,69]],[7,546,[],[36,43,46,49,50]],[36,546,[],[7,43,46,49,50]],[43,546,[],[7,36,46,49,50]],[46,546,[],[7,36,43,49,50]],[49,546,[],[7,36,43,46,50]],[50,546,[],[7,36,43,46,49]],[64,641,[10,49,52,54],[22,38,69,71]],[71,641,[10,38,49,52],[22,54,64,69]],[10,642,[],[38,47,49,52,54]],[38,642,[],[10,47,49,52,54]],[47,642,[],[10,38,49,52,54]],[52,642,[],[10,38,47,49,54]],[54,642,[],[10,38,47,49,52]],[68,769,[11,50,53,54],[23,45,70,71]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00002.record097" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00002.record097\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-3,1,2,4,5,6,7,8,11],[-12,1,2,4,5,6,7,8],[-14,1,6,9,10],[-16,1,4,9,10],[-18,1,4,6,10],[-19,1,4,6,9],[-1],[-4],[-6],[-7],[-9],[-10],[-15,2,9,11,13],[-20,2,5,9,11],[-2],[-5],[-8],[-11],[-13],[-17,3,10,12,13],[-21,16,17,18,19,20],[-22,4,14,15],[-23,21],[-24,23],[-25,24],[-26,22],[-27,26],[-28,27],[-29,25,28],[29]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"mate\",\"ridge\":515,\"a\":11,\"owners\":[7,10,36,38,43,46,47,52]},{\"tag\":\"mate\",\"ridge\":515,\"a\":53,\"owners\":[7,10,36,38,43,46,47]},{\"tag\":\"mate\",\"ridge\":545,\"a\":62,\"owners\":[7,43,49,50]},{\"tag\":\"mate\",\"ridge\":545,\"a\":66,\"owners\":[7,36,49,50]},{\"tag\":\"mate\",\"ridge\":545,\"a\":69,\"owners\":[7,36,43,50]},{\"tag\":\"mate\",\"ridge\":545,\"a\":70,\"owners\":[7,36,43,49]},{\"tag\":\"mate\",\"ridge\":546,\"a\":7,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":546,\"a\":36,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":546,\"a\":43,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":546,\"a\":46,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":546,\"a\":49,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":546,\"a\":50,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":641,\"a\":64,\"owners\":[10,49,52,54]},{\"tag\":\"mate\",\"ridge\":641,\"a\":71,\"owners\":[10,38,49,52]},{\"tag\":\"mate\",\"ridge\":642,\"a\":10,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":642,\"a\":38,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":642,\"a\":47,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":642,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":642,\"a\":54,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":769,\"a\":68,\"owners\":[11,50,53,54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[66,68,69,70,71],\"full_literals\":[-21,16,17,18,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[36,62,64],\"full_literals\":[-22,4,14,15]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-23,false,21],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-24,false,23],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-25,false,24],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0012\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-26,22,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-27,false,26],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-28,27,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-29,25,28],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true}]}"
  "p cnf 29 30\n-3 1 2 4 5 6 7 8 11 0\n-12 1 2 4 5 6 7 8 0\n-14 1 6 9 10 0\n-16 1 4 9 10 0\n-18 1 4 6 10 0\n-19 1 4 6 9 0\n-1 0\n-4 0\n-6 0\n-7 0\n-9 0\n-10 0\n-15 2 9 11 13 0\n-20 2 5 9 11 0\n-2 0\n-5 0\n-8 0\n-11 0\n-13 0\n-17 3 10 12 13 0\n-21 16 17 18 19 20 0\n-22 4 14 15 0\n-23 21 0\n-24 23 0\n-25 24 0\n-26 22 0\n-27 26 0\n-28 27 0\n-29 25 28 0\n29 0\n"
  "31 -19 0 11 7 8 9 6 0\n32 -18 0 12 7 8 9 5 0\n33 -16 0 12 7 8 11 4 0\n34 -14 0 12 7 9 11 3 0\n35 -15 2 11 13 0 11 13 0\n36 -20 2 5 11 0 11 14 0\n37 -12 0 17 7 8 15 9 10 16 2 0\n38 -20 0 18 15 16 36 0\n39 -3 0 18 7 8 15 9 10 16 17 1 0\n40 -15 0 19 15 18 35 0\n41 -17 0 39 12 37 19 20 0\n42 -21 0 33 41 32 31 38 21 0\n43 -22 0 8 34 40 22 0\n44 -23 0 42 23 0\n45 -24 0 44 24 0\n46 -25 0 45 25 0\n47 -26 0 43 26 0\n48 -27 0 47 27 0\n49 -28 0 48 28 0\n50 -29 0 46 49 29 0\n51 0 50 30 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00002.record097
