module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00018Data
public import GraphInputsRow16Part00018Frames
public import GraphInputsRow16Part00018Leaves
public import GraphInputsRow16Part00018Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00018.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record023
def vertexColumn : Fields := ⟨10, hexnat% "b896a969a6a58766392e1b85eb8569965a5a54756352d1b45de0ec3a8e6358ce3a4c7362e4b52d2b1ae1b46e8761d2719e1725c570dd0f23c4f0bda29485a2981e68651164a50768360e4348ca318e1314d0b12c1b21c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6d26db69b49b6da492492492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100c100fecfe000000", hexnat% "204000000000000000", 1161157293375488, 1055539752599552, 2251799813685248, 17592186044416]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10040a605ffe000000", 4616189755493711872, 152832116260864, hexnat% "200800140000000000", 1407924639367168]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100402400c90000000", hexnat% "200800144040000000", 4616189755560820736, 3412952812093440, 4999610368, 152832116260864, 282033322459136]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00018.record023

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00018.record026
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record026
def vertexColumn : Fields := ⟨10, hexnat% "2d41f1b21e876a398e1b85e0fad16c7899a5691e6c5a565535475a358d1b45d0f5a364d332cc73a2d8b1ac5b0ee8761c6715c3783d0f23c4f0bc1f9312a25871925291a685914951560d1358348c930cd0b0ac8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6db4924924d269249a4d24d2492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [63085613515014144, 6667936727040, 6896141224378368, 1933003718656, 1987917559889920, 264241152]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record026_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record026_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record026_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record026_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record026_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record026_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record026_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record026_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record026_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00018.record026

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00018.record065
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "b92e2748bab1aa6998e6558d62d94e4783eb85d12e6c5a966539695554d52d54d8b51d0f6c370ea398ce364d5334cb352d2b2ac9b0ee8791d4731e2729c6745c9715c3743c4f4682e07ac1a8519916250b41d50cc328d1324d0b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6d24da49b6db49249a4924924d2492492489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 23), (facetIndex 27), (facetIndex 32), (facetIndex 50), (facetIndex 65)]))
 (.leaf ([(facetIndex 30), (facetIndex 51), (facetIndex 58), (facetIndex 59)])))
 (.branch 3
 (.leaf ([(facetIndex 48), (facetIndex 60), (facetIndex 63)]))
 (.leaf ([(facetIndex 24), (facetIndex 35), (facetIndex 40), (facetIndex 49), (facetIndex 64)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 38)]))
 (.leaf ([(facetIndex 33), (facetIndex 46)])))
 (.branch 7
 (.leaf ([(facetIndex 39), (facetIndex 42), (facetIndex 43), (facetIndex 47)]))
 (.branch 8
 (.leaf ([(facetIndex 26), (facetIndex 29), (facetIndex 31), (facetIndex 41), (facetIndex 44)]))
 (.leaf ([(facetIndex 22), (facetIndex 25), (facetIndex 28)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3200211000000103265076673644430507178078308z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 52), (facetIndex 55)]))
 (.leaf ([(facetIndex 53), (facetIndex 61)])))
 (.branch 3
 (.leaf ([(facetIndex 66), (facetIndex 69)]))
 (.branch 4
 (.leaf ([(facetIndex 67), (facetIndex 74)]))
 (.leaf ([(facetIndex 54), (facetIndex 62)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 68), (facetIndex 75)]))
 (.leaf ([(facetIndex 34), (facetIndex 45), (facetIndex 57)])))
 (.branch 8
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 72)]))
 (.branch 9
 (.leaf ([(facetIndex 73), (facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 56)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "88538777253200041000690410000000600000000006z22;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6, 7, 8]
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
def grouped3_0027 : List Nat := [8]
def grouped3_0028 : List Nat := [8, 9]
def grouped3_0029 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00018.record065" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00018.record065" 72

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00018.record065" "{\"ridges\":[[7,145],[11,321],[11,322],[15,580],[18,704],[26,145],[32,321],[32,322],[33,580],[36,145],[39,321],[40,145],[42,322],[43,145],[46,162],[47,322],[52,332],[55,340],[56,660],[58,548],[60,580],[62,464],[63,672],[66,332],[67,180],[69,340],[74,184],[75,464]],\"owners\":[[7,145,[53,54,56,61,62],[26,36,40,41,43]],[26,145,[61,62],[7,36,40,41,43,53,54,56]],[36,145,[53,54,56,62],[7,26,40,41,43,61]],[40,145,[54,56,62],[7,26,36,41,43,53,61]],[43,145,[53,54,56,61],[7,26,36,40,41,62]],[46,162,[67,70,74],[9,29,37,40,44,72,76]],[11,321,[52,55,62],[32,39,42,47]],[32,321,[62],[11,39,42,47,52,55]],[39,321,[55,62],[11,32,42,47,52]],[11,322,[66,69,75],[32,39,42,47]],[32,322,[75],[11,39,42,47,66,69]],[42,322,[66],[11,32,39,47,69,75]],[47,322,[66,69],[11,32,39,42,75]],[58,548,[72],[14,30,51,59,71,77]],[15,580,[71,73,77],[33,58,60]],[33,580,[77],[15,58,60,71,73]],[60,580,[71],[15,33,58,73,77]],[63,672,[72],[17,46,59,76,77]],[18,704,[73,76,77],[48,60,63]],[52,332,[66],[]],[66,332,[52],[]],[67,180,[53],[]],[55,340,[69],[]],[69,340,[55],[]],[56,660,[],[]],[74,184,[61],[]],[62,464,[75],[]],[75,464,[62],[]]],\"edges\":[[32,[7,26,36,40,41,43,53,54,56,61,62,67,68,74,75]],[40,[11,32,39,42,47,52,55,62,66,69,75]],[41,[15,18,33,45,48,58,60,63,71,73,76,77]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00018.record065" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00018.record065\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-21,-9],[-29,-19],[-32,-5],[-32,-7],[-32,-20],[-32,-31],[-35,-13],[-35,-23],[-35,-34],[-1,22,23,25,28,29],[-6,28,29],[-10,22,23,25,29],[-12,23,25,29],[-15,22,23,25,28],[-17,33,36,40],[-2,21,24,29],[-8,29],[-11,24,29],[-2,32,35,41],[-8,41],[-14,32],[-18,32,35],[-26,38],[-3,37,39,43],[-9,43],[-27,37],[-30,38],[-4,39,42,43],[-21,32],[-32,21],[-33,22],[-24,35],[-35,24],[-25],[-40,28],[-29,41],[-41,29],[-44,5,7,8,20,31],[-45,9,17],[-46,44],[-47,46],[-48,45],[-49,48],[-50,47,49],[50],[-21,51],[-24,51],[-22,52],[-28,52],[-32,53],[-35,53],[-29,54],[-41,55],[-16,56],[-36,57],[-37,57],[-38,57],[-39,58],[-42,58],[-43,58],[-51,59],[-51,-52,60],[-54,61],[-61,62],[-53,62],[-62,63],[-59,63],[-59,-62,64],[-60,-62,65],[-55,66],[-55,-56,67],[-58,68],[-68,69],[-57,69],[-69,70],[-66,-69,71],[-67,71],[-63,-71,72],[-64,-70,72],[-65,72],[-72],[1,6,10,12,13,15,22,23,25,28,29,33,34,40,41],[2,8,11,14,18,21,24,29,32,35,41],[3,4,9,16,19,26,27,30,37,39,42,43]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":52,\"b\":33},{\"tag\":\"incompatible\",\"a\":62,\"b\":48},{\"tag\":\"incompatible\",\"a\":66,\"b\":23},{\"tag\":\"incompatible\",\"a\":66,\"b\":27},{\"tag\":\"incompatible\",\"a\":66,\"b\":50},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":69,\"b\":41},{\"tag\":\"incompatible\",\"a\":69,\"b\":54},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"mate\",\"ridge\":145,\"a\":7,\"owners\":[53,54,56,61,62]},{\"tag\":\"mate\",\"ridge\":145,\"a\":26,\"owners\":[61,62]},{\"tag\":\"mate\",\"ridge\":145,\"a\":36,\"owners\":[53,54,56,62]},{\"tag\":\"mate\",\"ridge\":145,\"a\":40,\"owners\":[54,56,62]},{\"tag\":\"mate\",\"ridge\":145,\"a\":43,\"owners\":[53,54,56,61]},{\"tag\":\"mate\",\"ridge\":162,\"a\":46,\"owners\":[67,70,74]},{\"tag\":\"mate\",\"ridge\":321,\"a\":11,\"owners\":[52,55,62]},{\"tag\":\"mate\",\"ridge\":321,\"a\":32,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":321,\"a\":39,\"owners\":[55,62]},{\"tag\":\"mate\",\"ridge\":322,\"a\":11,\"owners\":[66,69,75]},{\"tag\":\"mate\",\"ridge\":322,\"a\":32,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":322,\"a\":42,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":322,\"a\":47,\"owners\":[66,69]},{\"tag\":\"mate\",\"ridge\":548,\"a\":58,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":580,\"a\":15,\"owners\":[71,73,77]},{\"tag\":\"mate\",\"ridge\":580,\"a\":33,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":580,\"a\":60,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":672,\"a\":63,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":704,\"a\":18,\"owners\":[73,76,77]},{\"tag\":\"mate\",\"ridge\":332,\"a\":52,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":332,\"a\":66,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":180,\"a\":67,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":340,\"a\":55,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":340,\"a\":69,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":660,\"a\":56,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":184,\"a\":74,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":464,\"a\":62,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":464,\"a\":75,\"owners\":[62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[23,27,32,50,65],\"full_literals\":[-44,5,7,8,20,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[33,46],\"full_literals\":[-45,9,17]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-47,46,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-49,48,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-50,47,49],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":52,\"full_literals\":[-21,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":55,\"full_literals\":[-24,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":53,\"full_literals\":[-22,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":61,\"full_literals\":[-28,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-32,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-35,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":62,\"full_literals\":[-29,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":75,\"full_literals\":[-41,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":45,\"full_literals\":[-16,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":70,\"full_literals\":[-36,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":71,\"full_literals\":[-37,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":72,\"full_literals\":[-38,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":73,\"full_literals\":[-39,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":76,\"full_literals\":[-42,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":77,\"full_literals\":[-43,58]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-52,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-62,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-56,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-63,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":32,\"owners\":[7,26,36,40,41,43,53,54,56,61,62,67,68,74,75]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[11,32,39,42,47,52,55,62,66,69,75]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[15,18,33,45,48,58,60,63,71,73,76,77]}]}"
  "p cnf 72 84\n-21 -9 0\n-29 -19 0\n-32 -5 0\n-32 -7 0\n-32 -20 0\n-32 -31 0\n-35 -13 0\n-35 -23 0\n-35 -34 0\n-1 22 23 25 28 29 0\n-6 28 29 0\n-10 22 23 25 29 0\n-12 23 25 29 0\n-15 22 23 25 28 0\n-17 33 36 40 0\n-2 21 24 29 0\n-8 29 0\n-11 24 29 0\n-2 32 35 41 0\n-8 41 0\n-14 32 0\n-18 32 35 0\n-26 38 0\n-3 37 39 43 0\n-9 43 0\n-27 37 0\n-30 38 0\n-4 39 42 43 0\n-21 32 0\n-32 21 0\n-33 22 0\n-24 35 0\n-35 24 0\n-25 0\n-40 28 0\n-29 41 0\n-41 29 0\n-44 5 7 8 20 31 0\n-45 9 17 0\n-46 44 0\n-47 46 0\n-48 45 0\n-49 48 0\n-50 47 49 0\n50 0\n-21 51 0\n-24 51 0\n-22 52 0\n-28 52 0\n-32 53 0\n-35 53 0\n-29 54 0\n-41 55 0\n-16 56 0\n-36 57 0\n-37 57 0\n-38 57 0\n-39 58 0\n-42 58 0\n-43 58 0\n-51 59 0\n-51 -52 60 0\n-54 61 0\n-61 62 0\n-53 62 0\n-62 63 0\n-59 63 0\n-59 -62 64 0\n-60 -62 65 0\n-55 66 0\n-55 -56 67 0\n-58 68 0\n-68 69 0\n-57 69 0\n-69 70 0\n-66 -69 71 0\n-67 71 0\n-63 -71 72 0\n-64 -70 72 0\n-65 72 0\n-72 0\n1 6 10 12 13 15 22 23 25 28 29 33 34 40 41 0\n2 8 11 14 18 21 24 29 32 35 41 0\n3 4 9 16 19 26 27 30 37 39 42 43 0\n"
  "85 -65 0 81 80 0\n86 1 6 10 12 13 15 22 23 28 29 33 34 40 41 0 34 82 0\n87 29 41 2 14 18 21 24 8 32 35 0 83 18 0\n88 63 0 66 67 64 65 61 63 50 51 46 47 52 21 22 16 17 37 87 0\n89 -71 0 88 81 78 0\n90 -67 0 89 77 0\n91 32 35 41 0 32 36 20 21 29 19 22 87 0\n92 -32 8 0 85 45 81 3 4 5 6 30 50 38 1 46 65 40 61 69 41 68 62 44 79 48 49 43 75 31 35 42 74 39 55 15 0\n93 41 0 85 34 20 36 92 91 7 8 9 33 51 13 47 65 69 62 48 49 31 10 12 14 35 11 86 0\n94 29 0 93 37 0\n95 55 0 93 53 0\n96 -19 0 94 2 0\n97 66 0 95 70 0\n98 -56 0 95 90 71 0\n99 -69 0 97 89 76 0\n100 -16 0 98 54 0\n101 -68 0 99 73 0\n102 -57 0 99 74 0\n103 -58 0 101 72 0\n104 -37 0 102 56 0\n105 -38 0 102 57 0\n106 -39 0 103 58 0\n107 -42 0 103 59 0\n108 -43 0 103 60 0\n109 -3 0 104 106 108 24 0\n110 -27 0 104 26 0\n111 -26 0 105 23 0\n112 -30 0 105 27 0\n113 -4 0 106 107 108 28 0\n114 -9 0 108 25 0\n115 0 110 114 109 113 100 111 96 112 104 106 107 108 84 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00018.record065
