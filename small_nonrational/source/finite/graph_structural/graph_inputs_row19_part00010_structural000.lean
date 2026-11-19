module
prelude
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00010Frames
public import GraphInputsRow19Part00010Leaves
public import GraphInputsRow19Part00010Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00010.record010
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ce334ab0ec970dc8f332ca8eac68da8e93a398d6338ae1b89e1783ecc4e93672539715356354d4cd2b46d2745d0f5a338d5334d3332cab1ac9b16c3b31ca719c9715c3723c4f0bc1f3322c2b21c170ca2a85a314a5154c348ca344c53"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b4924da69b6d26d36db4d369369a49249b4d26d36db249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
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
 (.leaf ([(facetIndex 15)]))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨4, 18364758544493064720⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 16
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 34)]))
 (.leaf ([(facetIndex 38), (facetIndex 53), (facetIndex 68), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 67), (facetIndex 71)]))
 (.leaf ([(facetIndex 21), (facetIndex 25), (facetIndex 33), (facetIndex 45)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 56), (facetIndex 57), (facetIndex 64), (facetIndex 70)]))
 (.leaf ([(facetIndex 24), (facetIndex 30), (facetIndex 35), (facetIndex 36)])))
 (.branch 7
 (.leaf ([(facetIndex 27), (facetIndex 31), (facetIndex 62)]))
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 47)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "509404180024008000e181f8045a18d40c1d018000000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped1_0000 : List Nat := [0, 1, 2, 3]
def grouped1_0001 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def grouped1_0003 : List Nat := [4]
def grouped1_0004 : List Nat := [4, 5]
def grouped1_0005 : List Nat := [4, 5, 6, 7]
def grouped1_0006 : List Nat := [5]
def grouped1_0007 : List Nat := [6]
def grouped1_0008 : List Nat := [6, 7]
def grouped1_0009 : List Nat := [7]
def grouped1_0010 : List Nat := [8]
def grouped1_0011 : List Nat := [8, 9]
def grouped1_0012 : List Nat := [8, 9, 10, 11]
def grouped1_0013 : List Nat := [8, 9, 10, 11, 12, 13, 14, 15]
def grouped1_0014 : List Nat := [9]
def grouped1_0015 : List Nat := [10, 11]
def grouped1_0016 : List Nat := [12, 13, 14, 15]
def grouped2_0017 : List Nat := [0]
def grouped2_0018 : List Nat := [0, 1]
def grouped2_0019 : List Nat := [0, 1, 2, 3]
def grouped2_0021 : List Nat := [1]
def grouped2_0022 : List Nat := [2]
def grouped2_0023 : List Nat := [2, 3]
def grouped2_0024 : List Nat := [3]
def grouped2_0025 : List Nat := [4]
def grouped2_0026 : List Nat := [4, 5]
def grouped2_0027 : List Nat := [4, 5, 6, 7]
def grouped2_0028 : List Nat := [5]
def grouped2_0029 : List Nat := [6]
def grouped2_0030 : List Nat := [6, 7]
def grouped2_0031 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010_matrix_checked

def leafCount : Nat := 12
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 5), (facetIndex 8), (facetIndex 24), (facetIndex 32), (facetIndex 33), (facetIndex 42), (facetIndex 46), (facetIndex 48), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 69), (facetIndex 71)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 4), (facetIndex 15), (facetIndex 21), (facetIndex 30), (facetIndex 32), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 62), (facetIndex 63), (facetIndex 65), (facetIndex 69), (facetIndex 71)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 5), (facetIndex 8), (facetIndex 30), (facetIndex 32), (facetIndex 33), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 57), (facetIndex 63), (facetIndex 65), (facetIndex 69), (facetIndex 71)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 5), (facetIndex 8), (facetIndex 25), (facetIndex 34), (facetIndex 36), (facetIndex 41), (facetIndex 46), (facetIndex 48), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 67), (facetIndex 68)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 5), (facetIndex 8), (facetIndex 31), (facetIndex 34), (facetIndex 36), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 56), (facetIndex 63), (facetIndex 65), (facetIndex 67), (facetIndex 68)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 6), (facetIndex 9), (facetIndex 21), (facetIndex 32), (facetIndex 35), (facetIndex 42), (facetIndex 46), (facetIndex 48), (facetIndex 62), (facetIndex 63), (facetIndex 65), (facetIndex 69), (facetIndex 71)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 6), (facetIndex 9), (facetIndex 27), (facetIndex 32), (facetIndex 35), (facetIndex 45), (facetIndex 46), (facetIndex 48), (facetIndex 57), (facetIndex 63), (facetIndex 65), (facetIndex 69), (facetIndex 71)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 6), (facetIndex 9), (facetIndex 31), (facetIndex 34), (facetIndex 36), (facetIndex 45), (facetIndex 46), (facetIndex 48), (facetIndex 53), (facetIndex 63), (facetIndex 65), (facetIndex 67), (facetIndex 70)]
theorem leaf0007_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0007 = true := by
  decide +kernel
theorem leaf0007_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0007 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0007_counts_checked
def leaf0008 : List (Fin data.count) := [(facetIndex 4), (facetIndex 15), (facetIndex 24), (facetIndex 27), (facetIndex 32), (facetIndex 45), (facetIndex 46), (facetIndex 48), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 69), (facetIndex 71)]
theorem leaf0008_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0008 = true := by
  decide +kernel
theorem leaf0008_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0008 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0008_counts_checked
def leaf0009 : List (Fin data.count) := [(facetIndex 4), (facetIndex 15), (facetIndex 34), (facetIndex 36), (facetIndex 38), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 56), (facetIndex 62), (facetIndex 63), (facetIndex 65), (facetIndex 67)]
theorem leaf0009_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0009 = true := by
  decide +kernel
theorem leaf0009_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0009 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0009_counts_checked
def leaf0010 : List (Fin data.count) := [(facetIndex 4), (facetIndex 15), (facetIndex 34), (facetIndex 36), (facetIndex 41), (facetIndex 45), (facetIndex 46), (facetIndex 48), (facetIndex 53), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 67)]
theorem leaf0010_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0010 = true := by
  decide +kernel
theorem leaf0010_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0010 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0010_counts_checked
def leaf0011 : List (Fin data.count) := [(facetIndex 6), (facetIndex 9), (facetIndex 25), (facetIndex 34), (facetIndex 36), (facetIndex 38), (facetIndex 46), (facetIndex 48), (facetIndex 62), (facetIndex 63), (facetIndex 65), (facetIndex 67), (facetIndex 70)]
theorem leaf0011_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0011 = true := by
  decide +kernel
theorem leaf0011_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0011 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0011_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf (leaf0000))
 (.branch 2
 (.leaf (leaf0001))
 (.leaf (leaf0002))))
 (.branch 4
 (.leaf (leaf0003))
 (.branch 5
 (.leaf (leaf0004))
 (.leaf (leaf0005)))))
 (.branch 9
 (.branch 7
 (.leaf (leaf0006))
 (.branch 8
 (.leaf (leaf0007))
 (.leaf (leaf0008))))
 (.branch 10
 (.leaf (leaf0009))
 (.branch 11
 (.leaf (leaf0010))
 (.leaf (leaf0011))))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00010.record010" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"kind\":1,\"index\":4},{\"tag\":\"group\",\"kind\":1,\"index\":5},{\"tag\":\"group\",\"kind\":1,\"index\":6},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":8},{\"tag\":\"group\",\"kind\":1,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0008\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0005\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0018\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0018\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0023\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0023\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0019\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0019\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0026\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0026\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0030\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0030\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0027\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0027\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00010.record010" 91

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00010.record010" "{\"ridges\":[[19,15],[24,131],[25,69],[31,74],[31,138],[32,273],[32,274],[32,289],[32,290],[33,81],[33,82],[35,161],[42,69],[42,133],[45,133],[47,69],[47,193],[47,196],[50,105],[52,54],[53,76],[57,74],[63,26],[64,74],[64,194],[65,42],[67,532],[67,536],[67,548],[67,552],[70,164],[71,140],[71,164],[71,168]],\"owners\":[[33,81,[5,38],[0,27,34,45,49]],[33,82,[8,53],[0,21,34,58,62]],[32,273,[46],[1,34,43,51]],[32,274,[63],[1,34,60,66]],[24,131,[4,28,31,33],[2,19,22,25,30,36]],[35,161,[6,41],[2,30,36,47,50]],[32,289,[48],[3,36,43,51]],[32,290,[65],[3,36,60,66]],[47,193,[4,31,33,49],[7,35,42,45,50]],[64,194,[4,25,33,58],[10,35,57,59,62]],[25,69,[5,38,40],[7,18,21,23,42,47]],[42,69,[5,21,23],[7,18,25,38,40,47]],[47,69,[5,18,21,38],[7,23,25,40,42]],[42,133,[6,22,24],[7,19,25,39,41,45]],[45,133,[6,19,24,41],[7,22,25,39,42]],[70,164,[6,24],[13,47,56,59,71]],[71,164,[6,24,47,59],[13,56,70]],[47,196,[15,57,58,68],[7,25,45,59,70]],[63,26,[8,16,26,27,28,52,53,54,62],[60,61]],[31,74,[8,53,55],[10,18,27,29,57,64]],[57,74,[8,27,29],[10,18,31,53,55,64]],[64,74,[8,18,27,53],[10,29,31,55,57]],[65,42,[9,17,26,29,30,52,55,56,64],[60,61]],[31,138,[9,54,56],[10,19,28,30,57,62]],[71,168,[9,30,50,64],[13,41,70]],[53,76,[15,40,42,70],[11,18,38,55,57,69]],[67,532,[46],[12,44,69,72]],[67,536,[63],[12,61,69,73]],[71,140,[15,19,39,42,54,57,68],[13,41,56]],[67,548,[48],[14,44,71,72]],[67,552,[65],[14,61,71,73]],[19,15,[16,17,18],[]],[52,54,[20],[]],[50,105,[29,40],[]]],\"edges\":[],\"groupings\":[1,2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00010.record010" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00010.record010\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-13,-11],[-16,-3],[-16,-11],[-16,-13],[-17,-9],[-17,-10],[-17,-16],[-19,-13],[-22,-19],[-23,-1],[-23,-10],[-23,-11],[-23,-17],[-23,-22],[-25,-13],[-25,-15],[-25,-19],[-25,-21],[-25,-23],[-26,-8],[-26,-13],[-26,-19],[-26,-25],[-27,-1],[-27,-17],[-27,-23],[-27,-25],[-28,-9],[-28,-12],[-28,-18],[-28,-24],[-29,-13],[-29,-22],[-29,-23],[-32,-3],[-32,-16],[-32,-19],[-32,-22],[-32,-23],[-32,-29],[-32,-31],[-33,-17],[-33,-19],[-33,-22],[-33,-23],[-33,-29],[-34,-2],[-34,-4],[-34,-10],[-34,-17],[-34,-20],[-34,-25],[-34,-29],[-34,-30],[-34,-31],[-34,-33],[-36,-16],[-36,-17],[-36,-27],[-36,-34],[-39,-27],[-40,-17],[-41,-16],[-41,-17],[-41,-19],[-42,-34],[-43,-36],[-44,-13],[-44,-16],[-44,-17],[-44,-32],[-44,-41],[-45,-13],[-45,-16],[-45,-17],[-45,-23],[-45,-41],[-46,-13],[-46,-17],[-46,-19],[-46,-23],[-46,-25],[-46,-34],[-47,-45],[-48,-14],[-48,-21],[-48,-23],[-48,-25],[-48,-30],[-48,-34],[-48,-38],[-48,-41],[-48,-42],[-48,-43],[-48,-45],[-48,-46],[-50,-22],[-50,-23],[-50,-27],[-50,-48],[-52,-18],[-52,-24],[-53,-25],[-53,-34],[-53,-48],[-54,-52],[-55,-27],[-55,-32],[-55,-33],[-55,-36],[-56,-31],[-56,-32],[-56,-44],[-56,-55],[-25,2,29],[-25,5,41],[-24,35],[-24,49],[-16,1,20,23,25],[-27,3,32],[-24,37],[-24,51],[-36,1,23,25,38],[-50,1,17,25,46],[-17,2,29,31],[-33,2,13,15],[-36,2,10,13,29],[-33,3,14,16],[-34,3,11,16,32],[-55,3,16],[-56,3,16,36,47],[-36,7,45,46,53],[-49,5,8,18,19,20,40,41,42,48],[-23,5,41,43],[-45,5,19,21],[-50,5,10,19,41],[-51,6,9,18,21,22,40,43,44,50],[-23,6,42,44],[-56,6,22,39,50],[-41,7,31,33,55],[-52,35],[-52,49],[-56,7,11,30,33,42,45,53],[-52,37],[-52,51],[-11,8,9,10],[-40,12],[-39,21,31],[-57,1],[-1,57],[-58,2],[-59,3],[-3,59],[-60,4],[-5,61],[-6,62],[-63,57,58],[-57,63],[-64,59,60],[-59,64],[-65,63,64],[-64,65],[-63,65],[-65,66],[-61,-62,67],[-67,68],[-68,69],[-66,-69,70],[-70],[-71,24,26],[-72,29,41,53,54],[-73,52,56],[-74,13,17,25,34],[-75,44,45,50,55],[-76,16,22,27,28],[-77,19,23,48],[-19,77],[-78,32,33,36],[-32,78],[-79,71,72],[-80,71],[-80,72],[-81,73,74],[-82,73],[-82,74],[-83,79],[-83,80,82],[-84,80],[-83,81],[-84,82],[-85,75,76],[-86,75],[-86,76],[-87,77,78],[-88,77],[-88,78],[-77,-78,88],[-89,85],[-89,86,88],[-90,86],[-89,87],[-90,88],[-91,83],[-91,84,90],[-91,89],[91],[-2,-5,-16,-24,-25,-33,-35,-37,-49,-50,-51,-54,-56],[-1,-7,-13,-22,-24,-35,-36,-37,-48,-49,-51,-54,-56],[-2,-5,-22,-24,-25,-35,-36,-37,-45,-49,-51,-54,-56],[-2,-5,-17,-26,-28,-32,-35,-37,-49,-50,-51,-52,-53],[-2,-5,-23,-26,-28,-35,-36,-37,-44,-49,-51,-52,-53],[-3,-6,-13,-24,-27,-33,-35,-37,-48,-49,-51,-54,-56],[-3,-6,-19,-24,-27,-34,-35,-37,-45,-49,-51,-54,-56],[-3,-6,-23,-26,-28,-34,-35,-37,-41,-49,-51,-52,-55],[-1,-7,-16,-19,-24,-34,-35,-37,-49,-50,-51,-54,-56],[-1,-7,-26,-28,-29,-35,-36,-37,-44,-48,-49,-51,-52],[-1,-7,-26,-28,-32,-34,-35,-37,-41,-49,-50,-51,-52],[-3,-6,-17,-26,-28,-29,-35,-37,-48,-49,-51,-52,-55]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"index\":4,\"kind\":1},{\"tag\":\"group\",\"index\":5,\"kind\":1},{\"tag\":\"group\",\"index\":6,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":8,\"kind\":1},{\"tag\":\"group\",\"index\":9,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":21,\"b\":19},{\"tag\":\"incompatible\",\"a\":24,\"b\":6},{\"tag\":\"incompatible\",\"a\":24,\"b\":19},{\"tag\":\"incompatible\",\"a\":24,\"b\":21},{\"tag\":\"incompatible\",\"a\":25,\"b\":17},{\"tag\":\"incompatible\",\"a\":25,\"b\":18},{\"tag\":\"incompatible\",\"a\":25,\"b\":24},{\"tag\":\"incompatible\",\"a\":27,\"b\":21},{\"tag\":\"incompatible\",\"a\":30,\"b\":27},{\"tag\":\"incompatible\",\"a\":31,\"b\":4},{\"tag\":\"incompatible\",\"a\":31,\"b\":18},{\"tag\":\"incompatible\",\"a\":31,\"b\":19},{\"tag\":\"incompatible\",\"a\":31,\"b\":25},{\"tag\":\"incompatible\",\"a\":31,\"b\":30},{\"tag\":\"incompatible\",\"a\":33,\"b\":21},{\"tag\":\"incompatible\",\"a\":33,\"b\":23},{\"tag\":\"incompatible\",\"a\":33,\"b\":27},{\"tag\":\"incompatible\",\"a\":33,\"b\":29},{\"tag\":\"incompatible\",\"a\":33,\"b\":31},{\"tag\":\"incompatible\",\"a\":34,\"b\":16},{\"tag\":\"incompatible\",\"a\":34,\"b\":21},{\"tag\":\"incompatible\",\"a\":34,\"b\":27},{\"tag\":\"incompatible\",\"a\":34,\"b\":33},{\"tag\":\"incompatible\",\"a\":35,\"b\":4},{\"tag\":\"incompatible\",\"a\":35,\"b\":25},{\"tag\":\"incompatible\",\"a\":35,\"b\":31},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":36,\"b\":17},{\"tag\":\"incompatible\",\"a\":36,\"b\":20},{\"tag\":\"incompatible\",\"a\":36,\"b\":26},{\"tag\":\"incompatible\",\"a\":36,\"b\":32},{\"tag\":\"incompatible\",\"a\":38,\"b\":21},{\"tag\":\"incompatible\",\"a\":38,\"b\":30},{\"tag\":\"incompatible\",\"a\":38,\"b\":31},{\"tag\":\"incompatible\",\"a\":41,\"b\":6},{\"tag\":\"incompatible\",\"a\":41,\"b\":24},{\"tag\":\"incompatible\",\"a\":41,\"b\":27},{\"tag\":\"incompatible\",\"a\":41,\"b\":30},{\"tag\":\"incompatible\",\"a\":41,\"b\":31},{\"tag\":\"incompatible\",\"a\":41,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":40},{\"tag\":\"incompatible\",\"a\":42,\"b\":25},{\"tag\":\"incompatible\",\"a\":42,\"b\":27},{\"tag\":\"incompatible\",\"a\":42,\"b\":30},{\"tag\":\"incompatible\",\"a\":42,\"b\":31},{\"tag\":\"incompatible\",\"a\":42,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":5},{\"tag\":\"incompatible\",\"a\":45,\"b\":7},{\"tag\":\"incompatible\",\"a\":45,\"b\":18},{\"tag\":\"incompatible\",\"a\":45,\"b\":25},{\"tag\":\"incompatible\",\"a\":45,\"b\":28},{\"tag\":\"incompatible\",\"a\":45,\"b\":33},{\"tag\":\"incompatible\",\"a\":45,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":40},{\"tag\":\"incompatible\",\"a\":45,\"b\":42},{\"tag\":\"incompatible\",\"a\":47,\"b\":24},{\"tag\":\"incompatible\",\"a\":47,\"b\":25},{\"tag\":\"incompatible\",\"a\":47,\"b\":35},{\"tag\":\"incompatible\",\"a\":47,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":35},{\"tag\":\"incompatible\",\"a\":52,\"b\":25},{\"tag\":\"incompatible\",\"a\":53,\"b\":24},{\"tag\":\"incompatible\",\"a\":53,\"b\":25},{\"tag\":\"incompatible\",\"a\":53,\"b\":27},{\"tag\":\"incompatible\",\"a\":54,\"b\":45},{\"tag\":\"incompatible\",\"a\":55,\"b\":47},{\"tag\":\"incompatible\",\"a\":56,\"b\":21},{\"tag\":\"incompatible\",\"a\":56,\"b\":24},{\"tag\":\"incompatible\",\"a\":56,\"b\":25},{\"tag\":\"incompatible\",\"a\":56,\"b\":41},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":21},{\"tag\":\"incompatible\",\"a\":57,\"b\":24},{\"tag\":\"incompatible\",\"a\":57,\"b\":25},{\"tag\":\"incompatible\",\"a\":57,\"b\":31},{\"tag\":\"incompatible\",\"a\":57,\"b\":53},{\"tag\":\"incompatible\",\"a\":58,\"b\":21},{\"tag\":\"incompatible\",\"a\":58,\"b\":25},{\"tag\":\"incompatible\",\"a\":58,\"b\":27},{\"tag\":\"incompatible\",\"a\":58,\"b\":31},{\"tag\":\"incompatible\",\"a\":58,\"b\":33},{\"tag\":\"incompatible\",\"a\":58,\"b\":45},{\"tag\":\"incompatible\",\"a\":59,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":22},{\"tag\":\"incompatible\",\"a\":62,\"b\":29},{\"tag\":\"incompatible\",\"a\":62,\"b\":31},{\"tag\":\"incompatible\",\"a\":62,\"b\":33},{\"tag\":\"incompatible\",\"a\":62,\"b\":39},{\"tag\":\"incompatible\",\"a\":62,\"b\":45},{\"tag\":\"incompatible\",\"a\":62,\"b\":49},{\"tag\":\"incompatible\",\"a\":62,\"b\":53},{\"tag\":\"incompatible\",\"a\":62,\"b\":54},{\"tag\":\"incompatible\",\"a\":62,\"b\":55},{\"tag\":\"incompatible\",\"a\":62,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":30},{\"tag\":\"incompatible\",\"a\":64,\"b\":31},{\"tag\":\"incompatible\",\"a\":64,\"b\":35},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":67,\"b\":26},{\"tag\":\"incompatible\",\"a\":67,\"b\":32},{\"tag\":\"incompatible\",\"a\":68,\"b\":33},{\"tag\":\"incompatible\",\"a\":68,\"b\":45},{\"tag\":\"incompatible\",\"a\":68,\"b\":62},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":35},{\"tag\":\"incompatible\",\"a\":70,\"b\":41},{\"tag\":\"incompatible\",\"a\":70,\"b\":42},{\"tag\":\"incompatible\",\"a\":70,\"b\":47},{\"tag\":\"incompatible\",\"a\":71,\"b\":40},{\"tag\":\"incompatible\",\"a\":71,\"b\":41},{\"tag\":\"incompatible\",\"a\":71,\"b\":56},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"mate\",\"ridge\":81,\"a\":33,\"owners\":[5,38]},{\"tag\":\"mate\",\"ridge\":82,\"a\":33,\"owners\":[8,53]},{\"tag\":\"mate\",\"ridge\":273,\"a\":32,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":274,\"a\":32,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":131,\"a\":24,\"owners\":[4,28,31,33]},{\"tag\":\"mate\",\"ridge\":161,\"a\":35,\"owners\":[6,41]},{\"tag\":\"mate\",\"ridge\":289,\"a\":32,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":290,\"a\":32,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":193,\"a\":47,\"owners\":[4,31,33,49]},{\"tag\":\"mate\",\"ridge\":194,\"a\":64,\"owners\":[4,25,33,58]},{\"tag\":\"mate\",\"ridge\":69,\"a\":25,\"owners\":[5,38,40]},{\"tag\":\"mate\",\"ridge\":69,\"a\":42,\"owners\":[5,21,23]},{\"tag\":\"mate\",\"ridge\":69,\"a\":47,\"owners\":[5,18,21,38]},{\"tag\":\"mate\",\"ridge\":133,\"a\":42,\"owners\":[6,22,24]},{\"tag\":\"mate\",\"ridge\":133,\"a\":45,\"owners\":[6,19,24,41]},{\"tag\":\"mate\",\"ridge\":164,\"a\":70,\"owners\":[6,24]},{\"tag\":\"mate\",\"ridge\":164,\"a\":71,\"owners\":[6,24,47,59]},{\"tag\":\"mate\",\"ridge\":196,\"a\":47,\"owners\":[15,57,58,68]},{\"tag\":\"mate\",\"ridge\":26,\"a\":63,\"owners\":[8,16,26,27,28,52,53,54,62]},{\"tag\":\"mate\",\"ridge\":74,\"a\":31,\"owners\":[8,53,55]},{\"tag\":\"mate\",\"ridge\":74,\"a\":57,\"owners\":[8,27,29]},{\"tag\":\"mate\",\"ridge\":74,\"a\":64,\"owners\":[8,18,27,53]},{\"tag\":\"mate\",\"ridge\":42,\"a\":65,\"owners\":[9,17,26,29,30,52,55,56,64]},{\"tag\":\"mate\",\"ridge\":138,\"a\":31,\"owners\":[9,54,56]},{\"tag\":\"mate\",\"ridge\":168,\"a\":71,\"owners\":[9,30,50,64]},{\"tag\":\"mate\",\"ridge\":76,\"a\":53,\"owners\":[15,40,42,70]},{\"tag\":\"mate\",\"ridge\":532,\"a\":67,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":536,\"a\":67,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":140,\"a\":71,\"owners\":[15,19,39,42,54,57,68]},{\"tag\":\"mate\",\"ridge\":548,\"a\":67,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":552,\"a\":67,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":15,\"a\":19,\"owners\":[16,17,18]},{\"tag\":\"mate\",\"ridge\":54,\"a\":52,\"owners\":[20]},{\"tag\":\"mate\",\"ridge\":105,\"a\":50,\"owners\":[29,40]},{\"tag\":\"group_or\",\"kind\":1,\"index\":4,\"members\":[4],\"full_literals\":[-57,1]},{\"tag\":\"group_take\",\"kind\":1,\"index\":4,\"member\":4,\"full_literals\":[-1,57]},{\"tag\":\"group_or\",\"kind\":1,\"index\":5,\"members\":[5],\"full_literals\":[-58,2]},{\"tag\":\"group_or\",\"kind\":1,\"index\":6,\"members\":[6],\"full_literals\":[-59,3]},{\"tag\":\"group_take\",\"kind\":1,\"index\":6,\"member\":6,\"full_literals\":[-3,59]},{\"tag\":\"group_or\",\"kind\":1,\"index\":7,\"members\":[7],\"full_literals\":[-60,4]},{\"tag\":\"group_take\",\"kind\":1,\"index\":8,\"member\":8,\"full_literals\":[-5,61]},{\"tag\":\"group_take\",\"kind\":1,\"index\":9,\"member\":9,\"full_literals\":[-6,62]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0004\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,57,58],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,63],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0007\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0008\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,59,60],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0007\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,64],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0005\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,63,64],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,65],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,65],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-62,67],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9],\"right\":[10,11],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"grouped1_0012\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,68],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,69],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-66,-69,70],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":2,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[32,34],\"full_literals\":[-71,24,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[38,53,68,69],\"full_literals\":[-72,29,41,53,54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[67,71],\"full_literals\":[-73,52,56]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[21,25,33,45],\"full_literals\":[-74,13,17,25,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[56,57,64,70],\"full_literals\":[-75,44,45,50,55]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[24,30,35,36],\"full_literals\":[-76,16,22,27,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[27,31,62],\"full_literals\":[-77,19,23,48]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":27,\"full_literals\":[-19,77]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[41,42,47],\"full_literals\":[-78,32,33,36]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":41,\"full_literals\":[-32,78]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0017\",\"right_name\":\"grouped2_0021\",\"joined_name\":\"grouped2_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,71,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0017\",\"right_name\":\"grouped2_0021\",\"joined_name\":\"grouped2_0018\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-80,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0017\",\"right_name\":\"grouped2_0021\",\"joined_name\":\"grouped2_0018\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0022\",\"right_name\":\"grouped2_0024\",\"joined_name\":\"grouped2_0023\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-81,73,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0022\",\"right_name\":\"grouped2_0024\",\"joined_name\":\"grouped2_0023\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-82,73,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0022\",\"right_name\":\"grouped2_0024\",\"joined_name\":\"grouped2_0023\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-82,false,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0018\",\"right_name\":\"grouped2_0023\",\"joined_name\":\"grouped2_0019\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-83,79,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0018\",\"right_name\":\"grouped2_0023\",\"joined_name\":\"grouped2_0019\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-83,80,82],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0018\",\"right_name\":\"grouped2_0023\",\"joined_name\":\"grouped2_0019\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-84,80,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0018\",\"right_name\":\"grouped2_0023\",\"joined_name\":\"grouped2_0019\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-83,false,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0018\",\"right_name\":\"grouped2_0023\",\"joined_name\":\"grouped2_0019\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-84,false,82],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0025\",\"right_name\":\"grouped2_0028\",\"joined_name\":\"grouped2_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,75,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0025\",\"right_name\":\"grouped2_0028\",\"joined_name\":\"grouped2_0026\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,75,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0025\",\"right_name\":\"grouped2_0028\",\"joined_name\":\"grouped2_0026\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-86,false,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0029\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"grouped2_0030\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-87,77,78],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0029\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"grouped2_0030\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-88,77,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0029\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"grouped2_0030\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-88,false,78],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0029\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"grouped2_0030\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-77,-78,88],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0026\",\"right_name\":\"grouped2_0030\",\"joined_name\":\"grouped2_0027\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-89,85,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0026\",\"right_name\":\"grouped2_0030\",\"joined_name\":\"grouped2_0027\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-89,86,88],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0026\",\"right_name\":\"grouped2_0030\",\"joined_name\":\"grouped2_0027\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-90,86,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0026\",\"right_name\":\"grouped2_0030\",\"joined_name\":\"grouped2_0027\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-89,false,87],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0026\",\"right_name\":\"grouped2_0030\",\"joined_name\":\"grouped2_0027\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-90,false,88],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0019\",\"right_name\":\"grouped2_0027\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-91,83,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0019\",\"right_name\":\"grouped2_0027\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-91,84,90],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0019\",\"right_name\":\"grouped2_0027\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-91,false,89],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[5,8,24,32,33,42,46,48,63,64,65,69,71]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[4,15,21,30,32,46,47,48,62,63,65,69,71]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[5,8,30,32,33,46,47,48,57,63,65,69,71]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[5,8,25,34,36,41,46,48,63,64,65,67,68]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[5,8,31,34,36,46,47,48,56,63,65,67,68]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[6,9,21,32,35,42,46,48,62,63,65,69,71]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[6,9,27,32,35,45,46,48,57,63,65,69,71]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[6,9,31,34,36,45,46,48,53,63,65,67,70]},{\"tag\":\"block\",\"leaf\":8,\"vertices\":[4,15,24,27,32,45,46,48,63,64,65,69,71]},{\"tag\":\"block\",\"leaf\":9,\"vertices\":[4,15,34,36,38,46,47,48,56,62,63,65,67]},{\"tag\":\"block\",\"leaf\":10,\"vertices\":[4,15,34,36,41,45,46,48,53,63,64,65,67]},{\"tag\":\"block\",\"leaf\":11,\"vertices\":[6,9,25,34,36,38,46,48,62,63,65,67,70]}]}"
  "p cnf 91 218\n-13 -11 0\n-16 -3 0\n-16 -11 0\n-16 -13 0\n-17 -9 0\n-17 -10 0\n-17 -16 0\n-19 -13 0\n-22 -19 0\n-23 -1 0\n-23 -10 0\n-23 -11 0\n-23 -17 0\n-23 -22 0\n-25 -13 0\n-25 -15 0\n-25 -19 0\n-25 -21 0\n-25 -23 0\n-26 -8 0\n-26 -13 0\n-26 -19 0\n-26 -25 0\n-27 -1 0\n-27 -17 0\n-27 -23 0\n-27 -25 0\n-28 -9 0\n-28 -12 0\n-28 -18 0\n-28 -24 0\n-29 -13 0\n-29 -22 0\n-29 -23 0\n-32 -3 0\n-32 -16 0\n-32 -19 0\n-32 -22 0\n-32 -23 0\n-32 -29 0\n-32 -31 0\n-33 -17 0\n-33 -19 0\n-33 -22 0\n-33 -23 0\n-33 -29 0\n-34 -2 0\n-34 -4 0\n-34 -10 0\n-34 -17 0\n-34 -20 0\n-34 -25 0\n-34 -29 0\n-34 -30 0\n-34 -31 0\n-34 -33 0\n-36 -16 0\n-36 -17 0\n-36 -27 0\n-36 -34 0\n-39 -27 0\n-40 -17 0\n-41 -16 0\n-41 -17 0\n-41 -19 0\n-42 -34 0\n-43 -36 0\n-44 -13 0\n-44 -16 0\n-44 -17 0\n-44 -32 0\n-44 -41 0\n-45 -13 0\n-45 -16 0\n-45 -17 0\n-45 -23 0\n-45 -41 0\n-46 -13 0\n-46 -17 0\n-46 -19 0\n-46 -23 0\n-46 -25 0\n-46 -34 0\n-47 -45 0\n-48 -14 0\n-48 -21 0\n-48 -23 0\n-48 -25 0\n-48 -30 0\n-48 -34 0\n-48 -38 0\n-48 -41 0\n-48 -42 0\n-48 -43 0\n-48 -45 0\n-48 -46 0\n-50 -22 0\n-50 -23 0\n-50 -27 0\n-50 -48 0\n-52 -18 0\n-52 -24 0\n-53 -25 0\n-53 -34 0\n-53 -48 0\n-54 -52 0\n-55 -27 0\n-55 -32 0\n-55 -33 0\n-55 -36 0\n-56 -31 0\n-56 -32 0\n-56 -44 0\n-56 -55 0\n-25 2 29 0\n-25 5 41 0\n-24 35 0\n-24 49 0\n-16 1 20 23 25 0\n-27 3 32 0\n-24 37 0\n-24 51 0\n-36 1 23 25 38 0\n-50 1 17 25 46 0\n-17 2 29 31 0\n-33 2 13 15 0\n-36 2 10 13 29 0\n-33 3 14 16 0\n-34 3 11 16 32 0\n-55 3 16 0\n-56 3 16 36 47 0\n-36 7 45 46 53 0\n-49 5 8 18 19 20 40 41 42 48 0\n-23 5 41 43 0\n-45 5 19 21 0\n-50 5 10 19 41 0\n-51 6 9 18 21 22 40 43 44 50 0\n-23 6 42 44 0\n-56 6 22 39 50 0\n-41 7 31 33 55 0\n-52 35 0\n-52 49 0\n-56 7 11 30 33 42 45 53 0\n-52 37 0\n-52 51 0\n-11 8 9 10 0\n-40 12 0\n-39 21 31 0\n-57 1 0\n-1 57 0\n-58 2 0\n-59 3 0\n-3 59 0\n-60 4 0\n-5 61 0\n-6 62 0\n-63 57 58 0\n-57 63 0\n-64 59 60 0\n-59 64 0\n-65 63 64 0\n-64 65 0\n-63 65 0\n-65 66 0\n-61 -62 67 0\n-67 68 0\n-68 69 0\n-66 -69 70 0\n-70 0\n-71 24 26 0\n-72 29 41 53 54 0\n-73 52 56 0\n-74 13 17 25 34 0\n-75 44 45 50 55 0\n-76 16 22 27 28 0\n-77 19 23 48 0\n-19 77 0\n-78 32 33 36 0\n-32 78 0\n-79 71 72 0\n-80 71 0\n-80 72 0\n-81 73 74 0\n-82 73 0\n-82 74 0\n-83 79 0\n-83 80 82 0\n-84 80 0\n-83 81 0\n-84 82 0\n-85 75 76 0\n-86 75 0\n-86 76 0\n-87 77 78 0\n-88 77 0\n-88 78 0\n-77 -78 88 0\n-89 85 0\n-89 86 88 0\n-90 86 0\n-89 87 0\n-90 88 0\n-91 83 0\n-91 84 90 0\n-91 89 0\n91 0\n-2 -5 -16 -24 -25 -33 -35 -37 -49 -50 -51 -54 -56 0\n-1 -7 -13 -22 -24 -35 -36 -37 -48 -49 -51 -54 -56 0\n-2 -5 -22 -24 -25 -35 -36 -37 -45 -49 -51 -54 -56 0\n-2 -5 -17 -26 -28 -32 -35 -37 -49 -50 -51 -52 -53 0\n-2 -5 -23 -26 -28 -35 -36 -37 -44 -49 -51 -52 -53 0\n-3 -6 -13 -24 -27 -33 -35 -37 -48 -49 -51 -54 -56 0\n-3 -6 -19 -24 -27 -34 -35 -37 -45 -49 -51 -54 -56 0\n-3 -6 -23 -26 -28 -34 -35 -37 -41 -49 -51 -52 -55 0\n-1 -7 -16 -19 -24 -34 -35 -37 -49 -50 -51 -54 -56 0\n-1 -7 -26 -28 -29 -35 -36 -37 -44 -48 -49 -51 -52 0\n-1 -7 -26 -28 -32 -34 -35 -37 -41 -49 -50 -51 -52 0\n-3 -6 -17 -26 -28 -29 -35 -37 -48 -49 -51 -52 -55 0\n"
  "219 83 0 206 203 0\n220 89 0 206 205 0\n221 79 0 219 186 0\n222 81 0 219 189 0\n223 85 0 220 198 0\n224 87 0 220 201 0\n225 -46 0 206 78 79 80 81 82 83 96 173 176 185 195 190 202 204 0\n226 -88 23 -34 48 0 60 56 195 196 176 178 37 0\n227 23 -34 44 48 65 0 225 220 206 50 163 158 150 52 124 104 60 53 51 162 160 153 119 130 226 202 199 204 192 188 190 174 182 184 77 84 171 131 106 172 0\n228 -34 44 48 65 0 225 220 206 163 158 150 162 160 153 50 52 53 56 60 104 124 227 12 39 76 178 129 196 63 202 199 204 192 188 190 174 182 184 114 171 172 106 0\n229 88 -23 34 0 220 206 26 19 14 13 202 199 204 193 188 190 181 185 173 4 21 175 170 31 0\n230 -86 -23 34 0 222 219 45 39 229 196 178 110 67 57 98 76 34 26 19 14 13 11 192 193 174 175 68 72 113 31 173 127 134 185 183 187 172 181 182 106 141 142 144 145 170 171 211 0\n231 -23 34 0 206 223 13 14 19 26 39 45 76 98 229 196 178 57 110 230 200 204 188 190 181 185 173 21 68 170 174 31 191 175 0\n232 86 34 48 0 220 206 231 199 200 195 196 204 176 190 8 17 37 43 185 178 173 58 0\n233 -88 -17 23 48 0 58 42 195 196 176 178 37 0\n234 -78 88 -17 -73 -86 0 206 202 204 188 182 181 75 70 64 58 42 25 7 6 193 192 197 178 177 38 40 41 108 112 175 125 174 172 31 136 106 141 142 144 145 170 171 210 0\n235 -17 -73 34 48 0 206 224 232 193 231 7 25 233 202 204 188 181 234 194 176 9 22 175 170 31 0\n236 -82 25 34 48 0 206 232 193 192 231 184 185 235 173 4 8 21 68 73 176 195 202 204 188 181 170 31 102 172 114 174 97 99 175 0\n237 82 34 48 0 219 206 232 193 231 190 187 204 181 202 195 196 176 9 22 37 43 170 178 31 57 59 175 0\n238 -22 -56 -24 -72 -78 -25 -75 0 114 113 112 122 121 118 117 103 18 17 33 44 97 115 178 174 77 135 171 209 0\n239 34 48 0 224 206 231 232 192 193 237 184 236 15 16 17 23 27 103 176 194 195 202 204 188 181 182 170 31 102 117 118 121 122 172 112 113 114 238 175 57 63 74 178 116 174 46 126 171 207 0\n240 77 48 0 224 220 206 239 48 154 47 151 104 60 56 55 53 194 195 178 202 199 35 36 38 71 108 112 204 192 193 152 228 188 190 159 161 181 182 184 157 172 149 102 106 141 142 144 145 24 170 171 175 77 140 174 217 0\n241 44 -3 -26 -28 -73 48 0 220 169 153 160 162 164 168 167 166 239 56 60 240 22 176 39 178 196 199 192 98 76 20 29 147 30 66 51 138 174 156 114 165 172 155 141 142 144 145 133 214 0\n242 -26 -28 16 -73 48 0 206 28 240 239 104 60 56 53 49 20 22 146 176 39 129 178 196 202 204 188 182 241 72 113 171 172 106 0\n243 -88 48 0 239 60 56 196 226 178 39 0\n244 -28 16 -73 48 0 206 243 202 204 188 181 31 242 170 0\n245 -22 48 0 240 9 14 176 0\n246 -27 -73 48 0 220 206 245 243 202 204 188 182 181 240 197 179 199 192 239 104 53 26 61 99 107 120 176 22 65 170 171 102 117 118 121 122 172 113 139 174 213 0\n247 16 -73 48 0 220 246 245 243 199 193 244 175 0\n248 -73 48 0 220 206 243 202 204 188 182 181 199 192 240 239 48 154 47 151 104 66 56 54 53 247 2 3 63 69 74 152 171 228 159 106 161 172 157 114 143 149 174 10 176 22 170 117 118 121 122 215 0\n249 48 0 206 243 202 204 248 190 184 0\n250 -14 0 249 85 0\n251 -21 0 249 86 0\n252 -23 0 249 87 0\n253 -25 0 249 88 0\n254 -30 0 249 89 0\n255 -34 0 249 90 0\n256 -38 0 249 91 0\n257 -41 0 249 92 0\n258 -42 0 249 93 0\n259 -43 0 249 94 0\n260 -45 0 249 95 0\n261 -50 0 249 100 0\n262 -53 0 249 105 0\n263 -16 0 255 253 206 260 261 4 7 36 57 69 173 185 190 204 200 202 192 196 174 178 109 0\n264 -56 -75 0 260 261 113 114 174 0\n265 -52 82 0 219 206 257 256 253 252 262 225 263 260 261 249 190 204 202 196 200 193 192 187 182 181 102 106 141 142 144 145 170 171 33 40 46 178 59 110 123 132 175 174 216 0\n266 -44 -74 0 255 253 68 70 173 0\n267 82 0 206 222 260 261 190 204 200 202 192 196 264 265 172 183 266 174 108 109 110 178 0\n268 73 0 267 184 0\n269 74 0 267 185 0\n270 -44 0 269 266 0\n271 -55 -52 -17 0 220 206 257 262 259 270 251 261 263 249 145 144 142 141 106 102 101 62 58 42 25 5 108 130 178 196 202 199 204 193 188 181 182 170 171 33 137 175 218 0\n272 -52 -17 0 260 270 261 220 206 257 262 58 42 106 271 174 192 199 200 196 204 178 188 40 182 171 0\n273 -17 0 268 220 42 58 272 172 112 264 178 192 196 199 0\n274 13 0 273 253 255 269 173 0\n275 -11 0 274 1 0\n276 -26 0 274 21 0\n277 -29 0 274 32 0\n278 33 -56 0 223 220 277 257 206 276 262 258 275 254 260 256 253 252 263 249 274 264 192 200 204 188 181 170 122 121 118 117 31 182 171 199 196 191 112 143 178 59 123 175 208 0\n279 -56 0 251 223 206 276 257 262 277 250 261 263 249 274 111 264 148 191 192 200 204 188 181 182 170 171 31 117 118 121 122 278 44 128 139 175 212 0\n280 52 0 279 268 172 0\n281 -24 0 280 102 0\n282 -54 0 280 106 0\n283 -71 0 281 276 170 0\n284 -72 0 282 277 262 257 171 0\n285 0 283 284 221 180 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010.l) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf (⟨0, by decide⟩))
 (.branch 2
 (.leaf (⟨1, by decide⟩))
 (.leaf (⟨0, by decide⟩))))
 (.branch 4
 (.leaf (⟨0, by decide⟩))
 (.branch 5
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨0, by decide⟩)))))
 (.branch 9
 (.branch 7
 (.leaf (⟨0, by decide⟩))
 (.branch 8
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩))))
 (.branch 10
 (.leaf (⟨1, by decide⟩))
 (.branch 11
 (.leaf (⟨1, by decide⟩))
 (.leaf (⟨0, by decide⟩))))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010.g)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([]))
 (.branch 2
 (.leaf ([]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 4
 (.leaf ([⟨2, by decide⟩]))
 (.branch 5
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨4, by decide⟩])))))
 (.branch 9
 (.branch 7
 (.leaf ([⟨5, by decide⟩]))
 (.branch 8
 (.leaf ([⟨6, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 10
 (.leaf ([⟨2, by decide⟩]))
 (.branch 11
 (.leaf ([⟨3, by decide⟩]))
 (.leaf ([⟨6, by decide⟩, ⟨1, by decide⟩]))))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00010.record010_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00010.record010
