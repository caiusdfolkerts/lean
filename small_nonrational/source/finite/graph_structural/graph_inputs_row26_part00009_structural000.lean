module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00009Data
public import GraphInputsRow26Part00009Frames
public import GraphInputsRow26Part00009Leaves
public import GraphInputsRow26Part00009Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011
def vertexColumn : Fields := ⟨10, hexnat% "f4398ce2b8cd32cc723c4f2b2aaa9a8e8ba558d61d94e3391e2783ef0791d46d174731ac78972729aa725c5555356354d475c354d3362d4b6a3a4d5334e332cc73a2d4b32e2b2ad4731c6745c9715c3743c8f13d54348560d82ec26898a5454342d30c8b0ac4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6d24db69b6db69a4da6db49a4db4db4d24926d2491249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨62, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1840000080bb1e0000", 281509338546176, 4398113619968, 24779693555187712, hexnat% "200000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8400004802f3e0000", 281509336449024, hexnat% "300000000000000000", 24769800366456832, 9895604649984]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [24780246398926848, 285873090330624, hexnat% "84000000001100000", hexnat% "300000000000200000", 34393292800]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2840000d800d1e0000", 34930163712, 281474978807808, 24769800366456832, hexnat% "100000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2840010508053e0000", hexnat% "100000000002000000", 2818572288, 4512945476206592, 20266198591602688]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840010100011e0000", 2818572288, 13743895347200, hexnat% "200000000004200000", hexnat% "100000000802000000", 24769798218973184]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨19, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨17, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012
def vertexColumn : Fields := ⟨10, hexnat% "f41d8cd32c5713cac95a368ba1ea9655a365391e2785e0fbc1e4751b45d1cc6b1e25c9ca6a9c9715a55558d535c368d5362d4b6a3a4d5334e332cc7352cab1ae8751e2785d1725c570dd0f23c4fc5234348ca0d82e524c9c16254342d30c8b12c2b09c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6d36db4db69b6d36db6da6d26d34d24db4db49369b6d2489249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨61, by decide⟩, ⟨66, by decide⟩, ⟨71, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200400132b80e43c0000", hexnat% "800000000800000000", 2305843009213693952]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000122b80e43c0000", 281509336449024, hexnat% "42000000000000000", hexnat% "800000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20840013298864300000", 2305843009213693952, 2148270080, 2199023255552]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000013298864300000", hexnat% "42000000000000000", 2148270080, 2199023255552, hexnat% "800000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c6 c2
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800000010800000000", 4503602311987200, hexnat% "42000000004200000", 1075314688, 11544872091648, hexnat% "20000003200000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c9 c8
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record013
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ce39475334ad15c4f2b2a695a36a3a558d62d94e1b91e1783ef0791cc6b1d26c9ca719a66394e78571725a9715a55958d5352d54d4b46d4743da8e938ccb3a2d4b32e2b1ae1b46c9b0ed4729c6745c970dd0f13c2f07f188e03a318960db0952629514c530c4b0ac8711c27"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "136db6db69a4db69b6d349a6d36db6da6db6db6924db492693499249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 22), (facetIndex 25), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 19), (facetIndex 26), (facetIndex 44), (facetIndex 53)])))
 (.branch 3
 (.leaf ([(facetIndex 58), (facetIndex 59), (facetIndex 61)]))
 (.leaf ([(facetIndex 56), (facetIndex 74), (facetIndex 85)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 31), (facetIndex 33), (facetIndex 34)]))
 (.leaf ([(facetIndex 18), (facetIndex 27), (facetIndex 32)])))
 (.branch 7
 (.leaf ([(facetIndex 21), (facetIndex 66)]))
 (.leaf ([(facetIndex 24)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "180000000c0000180010483008000001000000125800a47030340000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 60), (facetIndex 65)]))
 (.branch 2
 (.leaf ([(facetIndex 67), (facetIndex 73), (facetIndex 75), (facetIndex 83)]))
 (.leaf ([(facetIndex 20), (facetIndex 76), (facetIndex 80)]))))
 (.branch 4
 (.leaf ([(facetIndex 30), (facetIndex 35), (facetIndex 39)]))
 (.branch 5
 (.leaf ([(facetIndex 17), (facetIndex 42), (facetIndex 43), (facetIndex 68)]))
 (.leaf ([(facetIndex 40), (facetIndex 69), (facetIndex 70), (facetIndex 79)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 37), (facetIndex 77), (facetIndex 78)]))
 (.branch 8
 (.leaf ([(facetIndex 47), (facetIndex 51), (facetIndex 52), (facetIndex 54)]))
 (.leaf ([(facetIndex 49), (facetIndex 81), (facetIndex 82), (facetIndex 84)]))))
 (.branch 10
 (.leaf ([(facetIndex 23), (facetIndex 28), (facetIndex 36), (facetIndex 38), (facetIndex 41), (facetIndex 46), (facetIndex 48), (facetIndex 50)]))
 (.branch 11
 (.leaf ([(facetIndex 29), (facetIndex 45), (facetIndex 55), (facetIndex 57), (facetIndex 64)]))
 (.leaf ([(facetIndex 62), (facetIndex 63)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "81882566210100554100abb0000a0a707798979a044953969300003a900009002004z11;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
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
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record013" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":5}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record013" 73

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record013" "{\"ridges\":[[4,74],[5,193],[9,328],[12,22],[13,70],[19,74],[21,22],[22,22],[26,70],[26,324],[28,26],[30,26],[31,74],[33,74],[34,328],[35,650],[38,531],[39,674],[42,108],[44,324],[44,328],[49,656],[51,641],[53,196],[53,324],[54,641],[54,900],[57,153],[60,712],[61,328],[62,656],[64,641],[65,960],[66,22],[66,26],[67,70],[67,92],[68,22],[70,270],[72,22],[73,22],[73,338],[75,216],[76,26],[76,338],[77,26],[78,656],[80,92],[81,656],[83,464],[84,148]],\"owners\":[[4,74,[67,69,70,75,76],[19,31,33,34]],[19,74,[75,76],[4,31,33,34,67,69,70]],[31,74,[67,70,75,76],[4,19,33,34,69]],[33,74,[67,69,70,76],[4,19,31,34,75]],[5,193,[6,53,60,65],[33]],[53,196,[13,72],[6,83]],[26,324,[80,83],[7,44,53,70,73]],[44,324,[73,83],[7,26,53,70,80]],[53,324,[70,73,80],[7,26,44,83]],[9,328,[70,76,80],[34,44,61]],[34,328,[80],[9,44,61,70,76]],[44,328,[76],[9,34,61,70,80]],[61,328,[70,76,80],[9,34,44]],[84,148,[12,22,45,71,72],[48,49,81,83]],[70,270,[20,68],[]],[57,153,[28],[]],[38,531,[30,37],[]],[51,641,[35,38,57,60,64,65],[39,49,54,62]],[54,641,[35,38,39,57,60,62],[49,51,64,65]],[64,641,[35,39,51,60],[38,49,54,57,62,65]],[35,650,[77],[]],[49,656,[77,78],[38,57,62,64,81,84]],[62,656,[77,84],[38,49,57,64,78,81]],[78,656,[49,57,64,84],[38,62,77,81]],[81,656,[38,57,64,77],[49,62,78,84]],[39,674,[78],[]],[42,108,[69],[]],[54,900,[84],[]],[60,712,[],[]],[65,960,[],[]],[67,92,[80],[]],[80,92,[67],[]],[73,338,[76],[]],[76,338,[73],[]],[75,216,[],[]],[83,464,[],[]]],\"edges\":[[26,[4,9,19,31,33,34,42,44,60,61,67,69,70,75,76,80]],[39,[5,6,13,33,53,60,65,72,75,83]],[43,[35,38,39,49,51,54,57,60,62,64,65,77,78,81,84]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record013" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record013\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-6],[-11,-10],[-12,-8],[-12,-10],[-12,-11],[-13,-10],[-13,-12],[-14,-3],[-18,-15],[-19,-18],[-20,-14],[-24,-10],[-29,-13],[-30,-10],[-31,-13],[-32,-12],[-34,-20],[-36,-9],[-36,-28],[-37,-13],[-38,-32],[-40,-8],[-40,-23],[-40,-26],[-40,-28],[-43,-40],[-44,-7],[-44,-40],[-45,-40],[-45,-41],[-45,-42],[-47,-45],[-47,-46],[-49,-46],[-50,-20],[-51,-40],[-52,-40],[-53,-8],[-53,-28],[-53,-40],[-53,-46],[-54,-13],[-56,-32],[-6,-14,-41],[-1,41,43,44,48,49],[-8,48,49],[-18,41,44,48,49],[-20,41,43,44,49],[-2,3,32,35,39],[-32,6,46],[-14,53,55],[-28,47,55],[-32,44,47,53],[-4,44,49,53],[-21,53],[-28,49],[-36,44,49,53],[-5,-40,-47],[-10,-42,-46],[-11,-40,-47],[-56,5,11,29,45,46],[-16,-40,-49],[-17,-40,-49],[-40,-49,-50],[-44,9,42],[-34,16],[-24,17,23],[-31,22,24,34,35,38,39],[-33,22,24,25,34,35,37],[-38,22,25,31,35],[-22,50],[-30,50,51],[-37,50,56],[-51,30,34,38,56],[-54,24,34,38,50],[-25,51],[-27,43],[-33,56],[-35],[-39],[-41,53],[-53,41],[-47,49],[-49,47],[-48],[-55],[-57,11,13,45,46],[-58,8,14,28,32],[-59,18,20,21],[-60,7,15,19],[-61,10,40],[-62,12],[-63,57,58],[-64,57],[-64,58],[-65,63],[-66,64],[-67,59],[-67,60],[-68,61,62],[-69,61],[-69,62],[-70,67,69],[-70,68],[-71,69],[-72,65],[-72,66,71],[-72,70],[72],[-73,26,43,44,52],[-43,73],[-44,73],[1,4,8,18,20,21,27,28,35,36,41,43,44,48,49,53],[2,3,6,20,32,35,39,46,48,55],[22,24,25,30,31,33,34,35,37,38,39,50,51,54,56]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":22,\"b\":13},{\"tag\":\"incompatible\",\"a\":22,\"b\":21},{\"tag\":\"incompatible\",\"a\":24,\"b\":19},{\"tag\":\"incompatible\",\"a\":24,\"b\":21},{\"tag\":\"incompatible\",\"a\":24,\"b\":22},{\"tag\":\"incompatible\",\"a\":25,\"b\":21},{\"tag\":\"incompatible\",\"a\":25,\"b\":24},{\"tag\":\"incompatible\",\"a\":26,\"b\":6},{\"tag\":\"incompatible\",\"a\":31,\"b\":27},{\"tag\":\"incompatible\",\"a\":32,\"b\":31},{\"tag\":\"incompatible\",\"a\":33,\"b\":26},{\"tag\":\"incompatible\",\"a\":38,\"b\":21},{\"tag\":\"incompatible\",\"a\":45,\"b\":25},{\"tag\":\"incompatible\",\"a\":49,\"b\":21},{\"tag\":\"incompatible\",\"a\":51,\"b\":25},{\"tag\":\"incompatible\",\"a\":53,\"b\":24},{\"tag\":\"incompatible\",\"a\":57,\"b\":33},{\"tag\":\"incompatible\",\"a\":61,\"b\":20},{\"tag\":\"incompatible\",\"a\":61,\"b\":44},{\"tag\":\"incompatible\",\"a\":62,\"b\":25},{\"tag\":\"incompatible\",\"a\":64,\"b\":53},{\"tag\":\"incompatible\",\"a\":66,\"b\":19},{\"tag\":\"incompatible\",\"a\":66,\"b\":37},{\"tag\":\"incompatible\",\"a\":66,\"b\":40},{\"tag\":\"incompatible\",\"a\":66,\"b\":44},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":18},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":67},{\"tag\":\"incompatible\",\"a\":71,\"b\":68},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":76,\"b\":72},{\"tag\":\"incompatible\",\"a\":77,\"b\":33},{\"tag\":\"incompatible\",\"a\":78,\"b\":66},{\"tag\":\"incompatible\",\"a\":79,\"b\":66},{\"tag\":\"incompatible\",\"a\":80,\"b\":19},{\"tag\":\"incompatible\",\"a\":80,\"b\":44},{\"tag\":\"incompatible\",\"a\":80,\"b\":66},{\"tag\":\"incompatible\",\"a\":80,\"b\":72},{\"tag\":\"incompatible\",\"a\":81,\"b\":25},{\"tag\":\"incompatible\",\"a\":84,\"b\":53},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[13,26,67]},{\"tag\":\"mate\",\"ridge\":74,\"a\":4,\"owners\":[67,69,70,75,76]},{\"tag\":\"mate\",\"ridge\":74,\"a\":19,\"owners\":[75,76]},{\"tag\":\"mate\",\"ridge\":74,\"a\":31,\"owners\":[67,70,75,76]},{\"tag\":\"mate\",\"ridge\":74,\"a\":33,\"owners\":[67,69,70,76]},{\"tag\":\"mate\",\"ridge\":193,\"a\":5,\"owners\":[6,53,60,65]},{\"tag\":\"mate\",\"ridge\":196,\"a\":53,\"owners\":[13,72]},{\"tag\":\"mate\",\"ridge\":324,\"a\":26,\"owners\":[80,83]},{\"tag\":\"mate\",\"ridge\":324,\"a\":44,\"owners\":[73,83]},{\"tag\":\"mate\",\"ridge\":324,\"a\":53,\"owners\":[70,73,80]},{\"tag\":\"mate\",\"ridge\":328,\"a\":9,\"owners\":[70,76,80]},{\"tag\":\"mate\",\"ridge\":328,\"a\":34,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":328,\"a\":44,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":328,\"a\":61,\"owners\":[70,76,80]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[12,66,73]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[21,68,72]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[22,66,73]},{\"tag\":\"mate\",\"ridge\":148,\"a\":84,\"owners\":[12,22,45,71,72]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[28,66,76]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[30,66,76]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[66,76,77]},{\"tag\":\"mate\",\"ridge\":270,\"a\":70,\"owners\":[20,68]},{\"tag\":\"mate\",\"ridge\":153,\"a\":57,\"owners\":[28]},{\"tag\":\"mate\",\"ridge\":531,\"a\":38,\"owners\":[30,37]},{\"tag\":\"mate\",\"ridge\":641,\"a\":51,\"owners\":[35,38,57,60,64,65]},{\"tag\":\"mate\",\"ridge\":641,\"a\":54,\"owners\":[35,38,39,57,60,62]},{\"tag\":\"mate\",\"ridge\":641,\"a\":64,\"owners\":[35,39,51,60]},{\"tag\":\"mate\",\"ridge\":650,\"a\":35,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":656,\"a\":49,\"owners\":[77,78]},{\"tag\":\"mate\",\"ridge\":656,\"a\":62,\"owners\":[77,84]},{\"tag\":\"mate\",\"ridge\":656,\"a\":78,\"owners\":[49,57,64,84]},{\"tag\":\"mate\",\"ridge\":656,\"a\":81,\"owners\":[38,57,64,77]},{\"tag\":\"mate\",\"ridge\":674,\"a\":39,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":108,\"a\":42,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":900,\"a\":54,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":712,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":960,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":92,\"a\":67,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":92,\"a\":80,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":338,\"a\":73,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":338,\"a\":76,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":216,\"a\":75,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":464,\"a\":83,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[22,25,71,72],\"full_literals\":[-57,11,13,45,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[19,26,44,53],\"full_literals\":[-58,8,14,28,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[31,33,34],\"full_literals\":[-59,18,20,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[18,27,32],\"full_literals\":[-60,7,15,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[21,66],\"full_literals\":[-61,10,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[24],\"full_literals\":[-62,12]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,57,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,61,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-69,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-70,67,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-70,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-72,65,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-72,66,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-72,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[40,69,70,79],\"full_literals\":[-73,26,43,44,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":69,\"full_literals\":[-43,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":70,\"full_literals\":[-44,73]},{\"tag\":\"edge\",\"edge\":26,\"owners\":[4,9,19,31,33,34,42,44,60,61,67,69,70,75,76,80]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[5,6,13,33,53,60,65,72,75,83]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[35,38,39,49,51,54,57,60,62,64,65,77,78,81,84]}]}"
  "p cnf 73 115\n-11 -6 0\n-11 -10 0\n-12 -8 0\n-12 -10 0\n-12 -11 0\n-13 -10 0\n-13 -12 0\n-14 -3 0\n-18 -15 0\n-19 -18 0\n-20 -14 0\n-24 -10 0\n-29 -13 0\n-30 -10 0\n-31 -13 0\n-32 -12 0\n-34 -20 0\n-36 -9 0\n-36 -28 0\n-37 -13 0\n-38 -32 0\n-40 -8 0\n-40 -23 0\n-40 -26 0\n-40 -28 0\n-43 -40 0\n-44 -7 0\n-44 -40 0\n-45 -40 0\n-45 -41 0\n-45 -42 0\n-47 -45 0\n-47 -46 0\n-49 -46 0\n-50 -20 0\n-51 -40 0\n-52 -40 0\n-53 -8 0\n-53 -28 0\n-53 -40 0\n-53 -46 0\n-54 -13 0\n-56 -32 0\n-6 -14 -41 0\n-1 41 43 44 48 49 0\n-8 48 49 0\n-18 41 44 48 49 0\n-20 41 43 44 49 0\n-2 3 32 35 39 0\n-32 6 46 0\n-14 53 55 0\n-28 47 55 0\n-32 44 47 53 0\n-4 44 49 53 0\n-21 53 0\n-28 49 0\n-36 44 49 53 0\n-5 -40 -47 0\n-10 -42 -46 0\n-11 -40 -47 0\n-56 5 11 29 45 46 0\n-16 -40 -49 0\n-17 -40 -49 0\n-40 -49 -50 0\n-44 9 42 0\n-34 16 0\n-24 17 23 0\n-31 22 24 34 35 38 39 0\n-33 22 24 25 34 35 37 0\n-38 22 25 31 35 0\n-22 50 0\n-30 50 51 0\n-37 50 56 0\n-51 30 34 38 56 0\n-54 24 34 38 50 0\n-25 51 0\n-27 43 0\n-33 56 0\n-35 0\n-39 0\n-41 53 0\n-53 41 0\n-47 49 0\n-49 47 0\n-48 0\n-55 0\n-57 11 13 45 46 0\n-58 8 14 28 32 0\n-59 18 20 21 0\n-60 7 15 19 0\n-61 10 40 0\n-62 12 0\n-63 57 58 0\n-64 57 0\n-64 58 0\n-65 63 0\n-66 64 0\n-67 59 0\n-67 60 0\n-68 61 62 0\n-69 61 0\n-69 62 0\n-70 67 69 0\n-70 68 0\n-71 69 0\n-72 65 0\n-72 66 71 0\n-72 70 0\n72 0\n-73 26 43 44 52 0\n-43 73 0\n-44 73 0\n1 4 8 18 20 21 27 28 35 36 41 43 44 48 49 53 0\n2 3 6 20 32 35 39 46 48 55 0\n22 24 25 30 31 33 34 35 37 38 39 50 51 54 56 0\n"
  "116 65 0 109 106 0\n117 70 0 109 108 0\n118 63 0 116 96 0\n119 68 0 117 104 0\n120 1 4 8 18 20 21 27 28 36 41 43 44 49 53 0 79 85 113 0\n121 2 3 6 20 32 46 0 79 80 85 86 114 0\n122 22 24 25 30 31 33 34 37 38 50 51 54 56 0 79 80 115 0\n123 56 51 50 38 34 24 0 79 80 71 68 76 75 72 78 73 122 0\n124 73 49 53 36 0 85 46 56 81 55 111 112 77 45 48 54 47 120 0\n125 -69 40 0 101 102 91 92 4 0\n126 -18 -44 0 117 28 125 103 99 27 9 10 90 0\n127 49 53 -36 0 86 85 109 119 51 19 18 46 57 28 65 31 125 105 107 97 94 95 88 16 92 100 91 2 6 59 87 0\n128 -10 -57 -49 0 84 32 34 2 6 87 0\n129 -40 -58 -49 14 28 0 22 23 36 64 62 63 88 67 66 21 43 123 0\n130 -64 -49 14 28 0 119 94 95 128 129 91 100 92 3 16 88 0\n131 53 -36 0 86 109 118 19 51 127 34 84 32 130 97 107 105 102 125 92 60 129 7 93 87 0\n132 -32 -53 0 109 119 40 125 105 107 97 94 82 30 41 16 50 92 1 100 87 91 6 0\n133 -36 0 109 80 79 19 131 38 40 41 82 125 105 107 97 95 132 88 8 11 44 49 121 0\n134 -53 0 109 80 79 38 39 40 41 82 132 125 105 107 97 95 88 8 11 44 49 121 0\n135 -14 0 134 86 51 0\n136 -21 0 134 55 0\n137 28 40 0 117 109 85 135 134 119 136 125 105 107 97 95 103 98 130 83 46 88 16 21 43 53 92 126 100 89 91 17 35 12 14 123 74 0\n138 40 0 109 86 119 125 105 107 97 94 137 52 56 32 33 128 91 100 92 5 7 87 0\n139 -23 0 138 23 0\n140 -26 0 138 24 0\n141 -28 0 138 25 0\n142 -43 0 138 26 0\n143 -44 0 138 28 0\n144 -45 0 138 29 0\n145 -51 0 138 36 0\n146 -52 0 138 37 0\n147 -73 0 143 142 140 146 110 0\n148 -25 0 145 76 0\n149 49 0 147 134 133 124 0\n150 -46 0 149 34 0\n151 47 0 149 84 0\n152 -50 0 149 138 64 0\n153 -16 0 149 138 62 0\n154 -17 0 149 138 63 0\n155 -58 0 149 138 135 141 129 0\n156 -5 0 151 138 58 0\n157 -11 0 151 138 60 0\n158 -22 0 152 71 0\n159 -30 0 152 145 72 0\n160 -34 0 153 66 0\n161 -24 0 154 139 67 0\n162 57 0 155 118 93 0\n163 13 0 157 150 144 162 87 0\n164 -29 0 163 13 0\n165 -31 0 163 15 0\n166 -37 0 163 20 0\n167 -54 0 163 42 0\n168 -56 0 164 157 156 144 150 61 0\n169 -38 0 165 148 158 79 70 0\n170 -33 0 166 161 148 160 79 158 69 0\n171 0 167 169 148 159 158 166 160 161 165 152 145 170 168 122 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record013
