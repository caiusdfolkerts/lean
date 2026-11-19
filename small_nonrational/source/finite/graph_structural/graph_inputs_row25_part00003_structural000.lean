module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow25Part00003Data
public import GraphInputsRow25Part00003Frames
public import GraphInputsRow25Part00003Leaves
public import GraphInputsRow25Part00003Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020
def vertexColumn : Fields := ⟨10, hexnat% "358e52b4d331c4f0bcd4ab2d2b1a9695a2eb46b1aa6c5a968d8b6c3a4e538ae1ba1e4789e0fb91d45594e4b9e1745b1715a55954d4b54b4ad1b51d2743dd0ec3c4e9394d5352cab1ad1b26c5bc1e8791d4731c6785d1725c3743c8f07f44532922c83aa1a462984e0b8b1525190e5452950d1342d28c930cc4b0ac1b21c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db4db69b6d249a69a4936d369269b6da49269b69b49249a4926d2491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨94, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41d50200114449b360000000", hexnat% "20040100400000000000000", hexnat% "600800000000000000", hexnat% "8000080040000004000000000", 197914240483328, hexnat% "20000200000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "425462100404491340000000", 1242993497691127808, hexnat% "810000000000a000000000", hexnat% "8010080040000004000000000", 197914240483328, hexnat% "600800000000000000", 144115188075855872]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d16000060061f3e0000000", hexnat% "8010080040000000000000000", hexnat% "600900000000000000", 162727720910848, hexnat% "420000000004080000000000", hexnat% "101040000000000000", hexnat% "402000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e0600f40b452e0000000", hexnat% "8010000040000000000000000", hexnat% "810000000000a000000000", hexnat% "402001000400100000000", hexnat% "405000000000000000000000", hexnat% "20000100000080000000000", 1126999418470400]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3c160100e006df3e0000000", hexnat% "401400000004000000000000", hexnat% "8000080040000000000000000", hexnat% "600100100000000000", 140737488355328, hexnat% "2001040000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "425462001340601360000000", 864691130602618880, hexnat% "300000180000000000", hexnat% "40004018000000000", hexnat% "8010180000000004000000000", hexnat% "400000840000000000", hexnat% "8000000000002000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80100c2040200005240000000", hexnat% "120000000008000000000", hexnat% "405400000000000000000000", hexnat% "600900000000000000", hexnat% "8000000000012000000000", hexnat% "20000000004080000000000", 197914777354240, hexnat% "101440400100000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record038
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038
def vertexColumn : Fields := ⟨10, hexnat% "3b0da338b92b44f0bce8b62b8b92d2b2a9a96ac6a5ab1aa6998e6a5a564b8ae1b91e2785ee8761b8791cc6b16c5694e4b9395352d52d2b51d2745d0f783d0ec3c8ea368e6358ce3c4e9364e5352d2b2ac6b26c5b31d2729c6745c5743c8f0bc6cc4a92468961381e4a469464a5194951342d0751324d0b12c1b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db69b6d36db4db4926db6da4d34924936db6db49349a493492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩, ⟨85, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d00014002dcfe000000", hexnat% "42000000000080000000000", hexnat% "82000000040000000000", 2882303770107052032, hexnat% "18420000000000000", 180143985094819840]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2012ee0000efe000000", hexnat% "8000000005000000000", hexnat% "40080000000060000000000", 9223372586610589696, hexnat% "5000000000000000000", 72057594037927936, hexnat% "2000000000080000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40080000200060400000000", hexnat% "2004000000080020000000", 2882303772254535680, hexnat% "1800000c000000000", hexnat% "9000040000002000000", hexnat% "2000080000814000000", 69793218560, 369295169578598400]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record038

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record021
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "358570bce4ab2d2b1a4e8bab1a962d94e2b86e4789e0fb91d46b1d2719965594e4b9b169595555534ad1b51d2745de0ec3a8f13a4d938cd332cf0b92d2b2ac6b86d1b26c3ba1e4751cc719e1745c970dd0f23c1f2d03cd094a2984e0bb41c46912c54946439294950d44d0b41dc0e8390d4328d0b12c2b21c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da6d36db4926d249269269b4924924936d249269a4924da492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 38), (facetIndex 69), (facetIndex 71)]))
 (.branch 2
 (.leaf ([(facetIndex 88), (facetIndex 89)]))
 (.leaf ([(facetIndex 68), (facetIndex 75)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 97), (facetIndex 98)]))
 (.leaf ([(facetIndex 37), (facetIndex 45), (facetIndex 47), (facetIndex 54), (facetIndex 55), (facetIndex 56)])))
 (.branch 6
 (.leaf ([(facetIndex 82), (facetIndex 83), (facetIndex 91), (facetIndex 92), (facetIndex 94), (facetIndex 95)]))
 (.leaf ([(facetIndex 90)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "d8b45b89000b4000040000200000000490000082000002z1c;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [3, 4, 5, 6]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record021" "{\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record021" 67

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record021" "{\"ridges\":[[3,131],[10,131],[10,642],[16,145],[17,133],[19,280],[22,145],[22,529],[22,641],[22,656],[23,784],[27,134],[31,148],[33,131],[37,278],[40,131],[43,642],[46,280],[47,538],[54,306],[56,131],[56,145],[56,402],[57,656],[58,784],[59,642],[60,131],[60,642],[61,642],[63,145],[64,280],[66,133],[69,596],[70,529],[70,656],[71,708],[73,280],[74,280],[76,784],[78,656],[79,784],[80,656],[80,784],[85,134],[88,534],[89,708],[94,562],[95,402],[95,656],[96,148],[97,340],[98,600]],\"owners\":[[17,133,[3,16,33,40,43,63,70,71],[66]],[66,133,[3,16,40,43,70,71],[17,33,63]],[27,134,[3,33,36,40,43,82,88,89],[85,87]],[85,134,[3,36,40,43,88,89],[27,33,82,87]],[22,641,[10,43,59,60,61,71],[70,78,80]],[10,642,[88,89,94,95],[43,57,59,60,61]],[43,642,[94,95],[10,57,59,60,61,88,89]],[59,642,[88,89,95],[10,43,57,60,61,94]],[60,642,[88,94,95],[10,43,57,59,61,89]],[61,642,[88,89,94],[10,43,57,59,60,95]],[31,148,[16,36,63,70,82,88],[87,96]],[96,148,[16,36,70,88],[31,63,82,87]],[19,280,[83,91,92,97,98],[46,64,73,74,76]],[46,280,[97,98],[19,64,73,74,76,83,91,92]],[64,280,[91,92,98],[19,46,73,74,76,83,97]],[73,280,[83,92,97,98],[19,46,64,74,76,91]],[74,280,[83,91,92],[19,46,64,73,76,97,98]],[22,529,[23,38,47,55,58,69,75,76,79],[57,70,78]],[70,529,[23,47,55,58,75,76,79],[22,38,57,69,78]],[22,656,[88,94,95],[57,70,78,80]],[57,656,[],[22,70,78,80,88,94,95]],[70,656,[94,95],[22,57,78,80,88]],[78,656,[88,95],[22,57,70,80,94]],[80,656,[88,94],[22,57,70,78,95]],[95,656,[22,70,78],[57,80,88,94]],[23,784,[92,95,98],[58,76,79,80]],[58,784,[98],[23,76,79,80,92,95]],[76,784,[95],[23,58,79,80,92,98]],[79,784,[92,95],[23,58,76,80,98]],[80,784,[92,98],[23,58,76,79,95]],[37,278,[83],[]],[88,534,[38],[]],[47,538,[92],[]],[54,306,[91],[]],[94,562,[55],[]],[56,402,[95],[]],[95,402,[56],[]],[97,340,[68],[]],[69,596,[],[]],[71,708,[89],[]],[89,708,[71],[]],[98,600,[75],[]]],\"edges\":[[21,[3,16,17,27,31,33,36,40,43,63,66,70,71,82,85,87,88,89,96]],[33,[19,23,37,46,54,56,58,64,68,73,74,76,79,80,83,91,92,95,97,98]],[34,[22,23,38,47,55,57,58,69,70,75,76,78,79,80,88,92,94,95,98]],[43,[10,22,43,57,59,60,61,70,71,78,80,88,89,94,95]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record021" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record021\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-20,-15],[-23,-20],[-24,-14],[-24,-19],[-31,-20],[-37,-20],[-41,-19],[-44,-41],[-46,-19],[-46,-44],[-47,-44],[-48,-41],[-48,-46],[-48,-47],[-49,-11],[-49,-25],[-49,-40],[-49,-43],[-1,-2,-20],[-1,-20,-24],[-2,-10,-20],[-2,-14,-20],[-10,-20,-24],[-4,1,3,10,14,15,26,31,32],[-28,1,3,14,15,31,32],[-8,1,10,11,14,15,40,44,45],[-42,1,11,14,15,44,45],[-6,2,15,23,24,25,32],[-2,44,45,48,49],[-15,48,49],[-23,44,45,49],[-24,44,48,49],[-25,44,45,48],[-3,-6,-20],[-6,-20,-26],[-9,3,11,26,31,40,44],[-50,3,11,31,44],[-5,41,46,47,51,52],[-16,51,52],[-27,46,47,52],[-33,41,47,51,52],[-34,41,46,47],[-6,7,13,17,19,22,30,35,36,38],[-31,7,17,19,22,35,36,38],[-6,44,48,49],[-21],[-31,48,49],[-37,44,49],[-39,44,48],[-49,6,31,37],[-7,47,49,52],[-22,52],[-36,49],[-38,47,49],[-39,47,52],[-12,41],[-44,13],[-17,47],[-18,46],[-48,19],[-20,49],[-49,20],[-51,29],[-30],[-32,45],[-45,32],[-52,35],[-13,53],[-32,53],[-44,54],[-45,54],[-29,55],[-35,55],[-19,56],[-20,56],[-41,57],[-46,57],[-47,57],[-48,57],[-49,57],[-55,58],[-54,58],[-54,-55,59],[-58,60],[-53,60],[-53,-58,61],[-53,-59,62],[-56,63],[-57,64],[-64,65],[-63,-64,66],[-60,-66,67],[-61,-65,67],[-62,67],[-67],[1,3,4,8,9,10,11,14,15,26,28,31,32,40,42,43,44,45,50],[5,7,12,16,18,20,22,27,29,33,34,36,38,39,41,46,47,49,51,52],[6,7,13,17,19,21,22,30,31,35,36,37,38,39,44,47,48,49,52],[2,6,15,21,23,24,25,31,32,37,39,44,45,48,49]],\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":56,\"b\":43},{\"tag\":\"incompatible\",\"a\":59,\"b\":56},{\"tag\":\"incompatible\",\"a\":60,\"b\":40},{\"tag\":\"incompatible\",\"a\":60,\"b\":55},{\"tag\":\"incompatible\",\"a\":70,\"b\":56},{\"tag\":\"incompatible\",\"a\":78,\"b\":56},{\"tag\":\"incompatible\",\"a\":83,\"b\":55},{\"tag\":\"incompatible\",\"a\":88,\"b\":83},{\"tag\":\"incompatible\",\"a\":91,\"b\":55},{\"tag\":\"incompatible\",\"a\":91,\"b\":88},{\"tag\":\"incompatible\",\"a\":92,\"b\":88},{\"tag\":\"incompatible\",\"a\":94,\"b\":83},{\"tag\":\"incompatible\",\"a\":94,\"b\":91},{\"tag\":\"incompatible\",\"a\":94,\"b\":92},{\"tag\":\"incompatible\",\"a\":95,\"b\":36},{\"tag\":\"incompatible\",\"a\":95,\"b\":61},{\"tag\":\"incompatible\",\"a\":95,\"b\":82},{\"tag\":\"incompatible\",\"a\":95,\"b\":87},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[3,10,56]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[3,56,60]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[10,33,56]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[10,40,56]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[33,56,60]},{\"tag\":\"mate\",\"ridge\":133,\"a\":17,\"owners\":[3,16,33,40,43,63,70,71]},{\"tag\":\"mate\",\"ridge\":133,\"a\":66,\"owners\":[3,16,40,43,70,71]},{\"tag\":\"mate\",\"ridge\":134,\"a\":27,\"owners\":[3,33,36,40,43,82,88,89]},{\"tag\":\"mate\",\"ridge\":134,\"a\":85,\"owners\":[3,36,40,43,88,89]},{\"tag\":\"mate\",\"ridge\":641,\"a\":22,\"owners\":[10,43,59,60,61,71]},{\"tag\":\"mate\",\"ridge\":642,\"a\":10,\"owners\":[88,89,94,95]},{\"tag\":\"mate\",\"ridge\":642,\"a\":43,\"owners\":[94,95]},{\"tag\":\"mate\",\"ridge\":642,\"a\":59,\"owners\":[88,89,95]},{\"tag\":\"mate\",\"ridge\":642,\"a\":60,\"owners\":[88,94,95]},{\"tag\":\"mate\",\"ridge\":642,\"a\":61,\"owners\":[88,89,94]},{\"tag\":\"three\",\"ridge\":145,\"vertices\":[16,22,56]},{\"tag\":\"three\",\"ridge\":145,\"vertices\":[22,56,63]},{\"tag\":\"mate\",\"ridge\":148,\"a\":31,\"owners\":[16,36,63,70,82,88]},{\"tag\":\"mate\",\"ridge\":148,\"a\":96,\"owners\":[16,36,70,88]},{\"tag\":\"mate\",\"ridge\":280,\"a\":19,\"owners\":[83,91,92,97,98]},{\"tag\":\"mate\",\"ridge\":280,\"a\":46,\"owners\":[97,98]},{\"tag\":\"mate\",\"ridge\":280,\"a\":64,\"owners\":[91,92,98]},{\"tag\":\"mate\",\"ridge\":280,\"a\":73,\"owners\":[83,92,97,98]},{\"tag\":\"mate\",\"ridge\":280,\"a\":74,\"owners\":[83,91,92]},{\"tag\":\"mate\",\"ridge\":529,\"a\":22,\"owners\":[23,38,47,55,58,69,75,76,79]},{\"tag\":\"mate\",\"ridge\":529,\"a\":70,\"owners\":[23,47,55,58,75,76,79]},{\"tag\":\"mate\",\"ridge\":656,\"a\":22,\"owners\":[88,94,95]},{\"tag\":\"mate\",\"ridge\":656,\"a\":57,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":656,\"a\":70,\"owners\":[94,95]},{\"tag\":\"mate\",\"ridge\":656,\"a\":78,\"owners\":[88,95]},{\"tag\":\"mate\",\"ridge\":656,\"a\":80,\"owners\":[88,94]},{\"tag\":\"mate\",\"ridge\":656,\"a\":95,\"owners\":[22,70,78]},{\"tag\":\"mate\",\"ridge\":784,\"a\":23,\"owners\":[92,95,98]},{\"tag\":\"mate\",\"ridge\":784,\"a\":58,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":784,\"a\":76,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":784,\"a\":79,\"owners\":[92,95]},{\"tag\":\"mate\",\"ridge\":784,\"a\":80,\"owners\":[92,98]},{\"tag\":\"mate\",\"ridge\":278,\"a\":37,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":534,\"a\":88,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":538,\"a\":47,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":306,\"a\":54,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":562,\"a\":94,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":402,\"a\":56,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":402,\"a\":95,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":340,\"a\":97,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":596,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":708,\"a\":71,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":708,\"a\":89,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":600,\"a\":98,\"owners\":[75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":38,\"full_literals\":[-13,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":71,\"full_literals\":[-32,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":88,\"full_literals\":[-44,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":89,\"full_literals\":[-45,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":68,\"full_literals\":[-29,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-35,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":55,\"full_literals\":[-19,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":56,\"full_literals\":[-20,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-41,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":91,\"full_literals\":[-46,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":92,\"full_literals\":[-47,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":94,\"full_literals\":[-48,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":95,\"full_literals\":[-49,57]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-55,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-58,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-53,-59,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-60,-66,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":21,\"owners\":[3,16,17,27,31,33,36,40,43,63,66,70,71,82,85,87,88,89,96]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[19,23,37,46,54,56,58,64,68,73,74,76,79,80,83,91,92,95,97,98]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[22,23,38,47,55,57,58,69,70,75,76,78,79,80,88,92,94,95,98]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[10,22,43,57,59,60,61,70,71,78,80,88,89,94,95]}]}"
  "p cnf 67 99\n-20 -15 0\n-23 -20 0\n-24 -14 0\n-24 -19 0\n-31 -20 0\n-37 -20 0\n-41 -19 0\n-44 -41 0\n-46 -19 0\n-46 -44 0\n-47 -44 0\n-48 -41 0\n-48 -46 0\n-48 -47 0\n-49 -11 0\n-49 -25 0\n-49 -40 0\n-49 -43 0\n-1 -2 -20 0\n-1 -20 -24 0\n-2 -10 -20 0\n-2 -14 -20 0\n-10 -20 -24 0\n-4 1 3 10 14 15 26 31 32 0\n-28 1 3 14 15 31 32 0\n-8 1 10 11 14 15 40 44 45 0\n-42 1 11 14 15 44 45 0\n-6 2 15 23 24 25 32 0\n-2 44 45 48 49 0\n-15 48 49 0\n-23 44 45 49 0\n-24 44 48 49 0\n-25 44 45 48 0\n-3 -6 -20 0\n-6 -20 -26 0\n-9 3 11 26 31 40 44 0\n-50 3 11 31 44 0\n-5 41 46 47 51 52 0\n-16 51 52 0\n-27 46 47 52 0\n-33 41 47 51 52 0\n-34 41 46 47 0\n-6 7 13 17 19 22 30 35 36 38 0\n-31 7 17 19 22 35 36 38 0\n-6 44 48 49 0\n-21 0\n-31 48 49 0\n-37 44 49 0\n-39 44 48 0\n-49 6 31 37 0\n-7 47 49 52 0\n-22 52 0\n-36 49 0\n-38 47 49 0\n-39 47 52 0\n-12 41 0\n-44 13 0\n-17 47 0\n-18 46 0\n-48 19 0\n-20 49 0\n-49 20 0\n-51 29 0\n-30 0\n-32 45 0\n-45 32 0\n-52 35 0\n-13 53 0\n-32 53 0\n-44 54 0\n-45 54 0\n-29 55 0\n-35 55 0\n-19 56 0\n-20 56 0\n-41 57 0\n-46 57 0\n-47 57 0\n-48 57 0\n-49 57 0\n-55 58 0\n-54 58 0\n-54 -55 59 0\n-58 60 0\n-53 60 0\n-53 -58 61 0\n-53 -59 62 0\n-56 63 0\n-57 64 0\n-64 65 0\n-63 -64 66 0\n-60 -66 67 0\n-61 -65 67 0\n-62 67 0\n-67 0\n1 3 4 8 9 10 11 14 15 26 28 31 32 40 42 43 44 45 50 0\n5 7 12 16 18 20 22 27 29 33 34 36 38 39 41 46 47 49 51 52 0\n6 7 13 17 19 21 22 30 31 35 36 37 38 39 44 47 48 49 52 0\n2 6 15 21 23 24 25 31 32 37 39 44 45 48 49 0\n"
  "100 -62 0 95 94 0\n101 6 7 13 17 19 22 31 35 36 37 38 39 44 47 48 49 52 0 46 64 98 0\n102 2 6 15 23 24 25 31 32 37 39 44 45 48 49 0 46 99 0\n103 41 46 47 49 55 0 73 67 40 59 51 54 55 61 53 72 63 39 52 56 41 42 38 97 0\n104 -41 47 49 60 0 64 84 81 73 67 51 54 55 58 82 70 48 53 52 85 68 7 12 44 43 101 0\n105 47 49 60 0 64 84 82 70 48 53 81 73 67 52 85 68 58 55 54 51 104 103 9 13 44 43 101 0\n106 49 60 0 84 82 71 70 85 69 48 31 105 14 30 49 33 47 32 45 29 102 0\n107 -2 60 0 84 82 70 106 17 62 5 6 50 34 15 35 36 37 1 18 71 85 69 19 21 22 26 25 27 24 96 0\n108 60 0 84 85 82 69 70 71 106 15 16 17 18 62 1 2 5 6 50 34 35 37 36 107 28 3 20 23 26 25 27 24 96 0\n109 -66 0 108 95 92 0\n110 -49 0 109 62 80 75 89 88 91 0\n111 -24 44 0 110 4 32 60 0\n112 -48 0 109 60 79 74 89 88 91 0\n113 -15 0 112 110 30 0\n114 -31 0 112 110 47 0\n115 45 44 0 110 112 114 113 45 49 111 48 65 31 33 29 102 0\n116 -45 0 100 95 110 66 71 69 82 87 86 83 93 90 89 76 77 78 103 0\n117 44 0 116 115 0\n118 -41 0 117 8 0\n119 -46 0 117 10 0\n120 -47 0 117 11 0\n121 13 0 117 57 0\n122 54 0 117 70 0\n123 55 0 119 120 110 118 103 0\n124 53 0 121 68 0\n125 59 0 123 122 83 0\n126 0 124 125 100 87 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021 Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record029
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "338b52cc4f392b4b4ab2b1a4e8d64d8b63392e1b91e0fb91b4731d26c9ca7198e539b1695954d54d4b5a364d3352d1b61d4743de0f43b0f13a4d9394cd32cf0ba2e4b52ccb1ae1b46c3b49ca719d1715d0f23c1f4c92a318960d84e0bac1c46914c70992529314950d44d0b4c348d1324c3342c4b0ac8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6d24924d249249a49a49a49369b4926926924d2492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 48), (facetIndex 75), (facetIndex 77)]))
 (.leaf ([(facetIndex 53), (facetIndex 70), (facetIndex 79), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 33), (facetIndex 37), (facetIndex 83), (facetIndex 85)]))
 (.branch 4
 (.leaf ([(facetIndex 44), (facetIndex 55), (facetIndex 63), (facetIndex 71), (facetIndex 76)]))
 (.leaf ([(facetIndex 35), (facetIndex 38), (facetIndex 86), (facetIndex 88)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 32), (facetIndex 40), (facetIndex 41), (facetIndex 58), (facetIndex 72), (facetIndex 74), (facetIndex 81), (facetIndex 89)]))
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 46), (facetIndex 61), (facetIndex 64)]))
 (.leaf ([(facetIndex 36), (facetIndex 54), (facetIndex 67), (facetIndex 78)]))))
 (.branch 9
 (.leaf ([(facetIndex 66), (facetIndex 68)]))
 (.branch 10
 (.leaf ([(facetIndex 34), (facetIndex 39), (facetIndex 62), (facetIndex 84), (facetIndex 87)]))
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 52)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5494292051170305053108780639600500371a0aa00603605594274925z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 42), (facetIndex 59), (facetIndex 60), (facetIndex 73)]))
 (.branch 2
 (.leaf ([(facetIndex 65), (facetIndex 69)]))
 (.leaf ([(facetIndex 82), (facetIndex 90), (facetIndex 98)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 95)]))
 (.leaf ([(facetIndex 96), (facetIndex 97)])))
 (.branch 6
 (.leaf ([(facetIndex 47), (facetIndex 51), (facetIndex 56), (facetIndex 57)]))
 (.leaf ([(facetIndex 91), (facetIndex 92), (facetIndex 93), (facetIndex 94)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "a47b6c8000008000000000800800002d000a00az23;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3, 4]
def grouped2_0006 : List Nat := [5]
def grouped2_0007 : List Nat := [5, 6, 7]
def grouped2_0008 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0009 : List Nat := [6, 7]
def grouped2_0010 : List Nat := [8, 9, 10]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1, 2]
def grouped3_0014 : List Nat := [1]
def grouped3_0015 : List Nat := [1, 2]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [3]
def grouped3_0018 : List Nat := [3, 4]
def grouped3_0019 : List Nat := [3, 4, 5, 6]
def grouped3_0020 : List Nat := [4]
def grouped3_0021 : List Nat := [5]
def grouped3_0022 : List Nat := [5, 6]
def grouped3_0023 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record029" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":9,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record029" 73

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record029" "{\"ridges\":[[19,521],[19,584],[20,521],[20,769],[20,776],[22,529],[22,656],[23,529],[23,784],[24,577],[24,641],[24,704],[42,529],[42,538],[46,584],[48,776],[51,594],[53,529],[53,656],[54,529],[54,784],[55,641],[55,704],[57,898],[60,540],[64,584],[69,529],[69,596],[70,656],[71,704],[73,521],[73,529],[73,568],[74,784],[75,769],[75,776],[76,584],[76,641],[77,776],[78,784],[79,656],[79,704],[80,784],[89,274],[90,538],[90,784],[93,594],[94,898],[96,584],[96,652],[97,596],[97,656],[98,568],[98,776],[98,784]],\"owners\":[[89,274,[10,36,52,54,94],[31,41,82,87,90]],[24,577,[19,46,51,56,64,69,77],[55,71,79]],[19,584,[91,92,96],[46,64,76,77]],[46,584,[96],[19,64,76,77,91,92]],[64,584,[91,92],[19,46,76,77,96]],[76,584,[92],[19,46,64,77,91,96]],[96,584,[19,46,77,92],[64,76,91]],[20,769,[23,54,56,57,78,80],[48,75,77]],[75,769,[23,54,56,57,80],[20,48,77,78]],[20,776,[90,92,98],[48,74,75,77]],[48,776,[98],[20,74,75,77,90,92]],[75,776,[90,92],[20,48,74,77,98]],[77,776,[90,98],[20,48,74,75,92]],[98,776,[20,48,77,92],[74,75,90]],[22,529,[23,42,51,54,60,69,73,74,78],[53,70,79]],[53,529,[23,60,69,73,74,78],[22,42,51,54,70,79]],[24,641,[22,47,53,57,65,70,80],[55,71,76]],[55,641,[22,65,70,80],[24,47,53,57,71,76]],[76,641,[22,53,57,70,80],[24,47,55,65,71]],[22,656,[93,94,97],[53,70,79,80]],[53,656,[97],[22,70,79,80,93,94]],[70,656,[93,94],[22,53,79,80,97]],[79,656,[94],[22,53,70,80,93,97]],[97,656,[22,53,80,94],[70,79,93]],[23,784,[90,94,98],[54,74,78,80]],[54,784,[98],[23,74,78,80,90,94]],[74,784,[94],[23,54,78,80,90,98]],[78,784,[90,94],[23,54,74,80,98]],[80,784,[90,98],[23,54,74,78,94]],[90,784,[23,78,80],[54,74,94,98]],[98,784,[23,54,80,94],[74,78,90]],[24,704,[91,93,96,97],[55,71,76,79]],[55,704,[96,97],[24,71,76,79,91,93]],[71,704,[91,93],[24,55,76,79,96,97]],[79,704,[91,96],[24,55,71,76,93,97]],[42,538,[90],[]],[90,538,[42],[]],[51,594,[93],[]],[93,594,[51],[]],[57,898,[94],[]],[94,898,[57],[]],[60,540,[],[]],[96,652,[65],[]],[69,596,[97],[]],[97,596,[69],[]],[73,568,[98],[]],[98,568,[73],[]]],\"edges\":[[34,[22,23,42,51,53,54,60,69,70,73,74,78,79,80,90,93,94,97,98]],[41,[19,24,46,51,55,56,64,69,71,76,77,79,91,92,93,96,97]],[43,[22,24,47,53,55,57,65,70,71,76,79,80,91,93,94,96,97]],[44,[20,23,48,54,56,57,74,75,77,78,80,90,92,94,98]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record029" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record029\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-12,-11],[-19,-13],[-19,-15],[-19,-18],[-20,-19],[-21,-19],[-35,-11],[-35,-31],[-36,-1],[-36,-8],[-36,-10],[-36,-17],[-36,-19],[-36,-30],[-36,-33],[-38,-11],[-38,-19],[-38,-31],[-38,-36],[-41,-7],[-41,-9],[-41,-13],[-41,-14],[-41,-18],[-41,-20],[-41,-21],[-41,-23],[-41,-39],[-42,-19],[-42,-41],[-43,-19],[-43,-41],[-44,-21],[-44,-43],[-45,-16],[-45,-21],[-45,-42],[-45,-43],[-45,-44],[-48,-36],[-40,1,8,17,19,45],[-2,-3,-31],[-6,2,13,16,21,25,27,35],[-2,42,43,46],[-13,46],[-25,42,43],[-34,43],[-46,2,13,35,43],[-3,5,19,21,22,36,38],[-33,5,19,21,22,38],[-3,41,43,48],[-15,48],[-33,41,43],[-35,41,48],[-48,3,15,35,43],[-4,5,11,16,19,24,27,31,32,36],[-18,5,24,27,31,32,36],[-4,-5,-11],[-4,-5,-31],[-4,-19,-31],[-5,-11,-27],[-5,-18,-31],[-19,-27,-31],[-6,4,14,18,22,26,28,38],[-20,4,26,28,38],[-34,4,18,22,28,38],[-4,44,45,47],[-18,47],[-28,44,45],[-37,45],[-47,4,18,38,45],[-5,41,45,48],[-19,48],[-32,45],[-36,41,45],[-38,41,48],[-41,5,36,38],[-48,5,19,38,45],[-6,42,44,46,47],[-20,46,47],[-29,42,44],[-37,42,46],[-11,41],[-41,11],[-16,44],[-44,16],[-22,45],[-45,22],[-24],[-46,26],[-27,47],[-47,27],[-31,48],[-48,31],[-49,12,15,33,35],[-50,18,28,37,38],[-51,7,9,10,23,30,32,39,40],[-52,49,50],[-53,52],[-54,51],[-55,54],[-56,53,55],[56],[-11,57],[-31,57],[-26,58],[-27,58],[-41,59],[-48,59],[-47,60],[-14,61],[-16,61],[-21,61],[-22,61],[-42,62],[-43,62],[-44,62],[-45,62],[-59,63],[-58,63],[-58,-59,64],[-63,65],[-57,65],[-57,-63,66],[-57,-64,67],[-60,68],[-62,69],[-61,69],[-61,-62,70],[-69,71],[-70,72],[-68,-69,72],[-65,-72,73],[-66,-71,73],[-67,73],[-73],[4,5,11,16,18,19,24,27,28,31,32,36,37,38,41,44,45,47,48],[2,6,13,16,20,21,25,27,29,34,35,37,42,43,44,46,47],[4,6,14,18,20,22,26,28,29,34,37,38,42,44,45,46,47],[3,5,15,19,21,22,32,33,35,36,38,41,43,45,48]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":45,\"b\":42},{\"tag\":\"incompatible\",\"a\":54,\"b\":46},{\"tag\":\"incompatible\",\"a\":54,\"b\":48},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":77,\"b\":42},{\"tag\":\"incompatible\",\"a\":77,\"b\":73},{\"tag\":\"incompatible\",\"a\":78,\"b\":10},{\"tag\":\"incompatible\",\"a\":78,\"b\":36},{\"tag\":\"incompatible\",\"a\":78,\"b\":41},{\"tag\":\"incompatible\",\"a\":78,\"b\":52},{\"tag\":\"incompatible\",\"a\":78,\"b\":54},{\"tag\":\"incompatible\",\"a\":78,\"b\":72},{\"tag\":\"incompatible\",\"a\":78,\"b\":75},{\"tag\":\"incompatible\",\"a\":80,\"b\":42},{\"tag\":\"incompatible\",\"a\":80,\"b\":54},{\"tag\":\"incompatible\",\"a\":80,\"b\":73},{\"tag\":\"incompatible\",\"a\":80,\"b\":78},{\"tag\":\"incompatible\",\"a\":90,\"b\":32},{\"tag\":\"incompatible\",\"a\":90,\"b\":40},{\"tag\":\"incompatible\",\"a\":90,\"b\":46},{\"tag\":\"incompatible\",\"a\":90,\"b\":47},{\"tag\":\"incompatible\",\"a\":90,\"b\":53},{\"tag\":\"incompatible\",\"a\":90,\"b\":55},{\"tag\":\"incompatible\",\"a\":90,\"b\":56},{\"tag\":\"incompatible\",\"a\":90,\"b\":58},{\"tag\":\"incompatible\",\"a\":90,\"b\":81},{\"tag\":\"incompatible\",\"a\":91,\"b\":54},{\"tag\":\"incompatible\",\"a\":91,\"b\":90},{\"tag\":\"incompatible\",\"a\":92,\"b\":54},{\"tag\":\"incompatible\",\"a\":92,\"b\":90},{\"tag\":\"incompatible\",\"a\":93,\"b\":56},{\"tag\":\"incompatible\",\"a\":93,\"b\":92},{\"tag\":\"incompatible\",\"a\":94,\"b\":51},{\"tag\":\"incompatible\",\"a\":94,\"b\":56},{\"tag\":\"incompatible\",\"a\":94,\"b\":91},{\"tag\":\"incompatible\",\"a\":94,\"b\":92},{\"tag\":\"incompatible\",\"a\":94,\"b\":93},{\"tag\":\"incompatible\",\"a\":98,\"b\":78},{\"tag\":\"mate\",\"ridge\":274,\"a\":89,\"owners\":[10,36,52,54,94]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[19,20,73]},{\"tag\":\"mate\",\"ridge\":577,\"a\":24,\"owners\":[19,46,51,56,64,69,77]},{\"tag\":\"mate\",\"ridge\":584,\"a\":19,\"owners\":[91,92,96]},{\"tag\":\"mate\",\"ridge\":584,\"a\":46,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":584,\"a\":64,\"owners\":[91,92]},{\"tag\":\"mate\",\"ridge\":584,\"a\":76,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":584,\"a\":96,\"owners\":[19,46,77,92]},{\"tag\":\"mate\",\"ridge\":769,\"a\":20,\"owners\":[23,54,56,57,78,80]},{\"tag\":\"mate\",\"ridge\":769,\"a\":75,\"owners\":[23,54,56,57,80]},{\"tag\":\"mate\",\"ridge\":776,\"a\":20,\"owners\":[90,92,98]},{\"tag\":\"mate\",\"ridge\":776,\"a\":48,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":776,\"a\":75,\"owners\":[90,92]},{\"tag\":\"mate\",\"ridge\":776,\"a\":77,\"owners\":[90,98]},{\"tag\":\"mate\",\"ridge\":776,\"a\":98,\"owners\":[20,48,77,92]},{\"tag\":\"mate\",\"ridge\":529,\"a\":22,\"owners\":[23,42,51,54,60,69,73,74,78]},{\"tag\":\"mate\",\"ridge\":529,\"a\":53,\"owners\":[23,60,69,73,74,78]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[22,23,42]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[22,23,73]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[22,54,73]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[23,42,69]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[23,53,73]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[54,69,73]},{\"tag\":\"mate\",\"ridge\":641,\"a\":24,\"owners\":[22,47,53,57,65,70,80]},{\"tag\":\"mate\",\"ridge\":641,\"a\":55,\"owners\":[22,65,70,80]},{\"tag\":\"mate\",\"ridge\":641,\"a\":76,\"owners\":[22,53,57,70,80]},{\"tag\":\"mate\",\"ridge\":656,\"a\":22,\"owners\":[93,94,97]},{\"tag\":\"mate\",\"ridge\":656,\"a\":53,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":656,\"a\":70,\"owners\":[93,94]},{\"tag\":\"mate\",\"ridge\":656,\"a\":79,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":656,\"a\":97,\"owners\":[22,53,80,94]},{\"tag\":\"mate\",\"ridge\":784,\"a\":23,\"owners\":[90,94,98]},{\"tag\":\"mate\",\"ridge\":784,\"a\":54,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":784,\"a\":74,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":784,\"a\":78,\"owners\":[90,94]},{\"tag\":\"mate\",\"ridge\":784,\"a\":80,\"owners\":[90,98]},{\"tag\":\"mate\",\"ridge\":784,\"a\":90,\"owners\":[23,78,80]},{\"tag\":\"mate\",\"ridge\":784,\"a\":98,\"owners\":[23,54,80,94]},{\"tag\":\"mate\",\"ridge\":704,\"a\":24,\"owners\":[91,93,96,97]},{\"tag\":\"mate\",\"ridge\":704,\"a\":55,\"owners\":[96,97]},{\"tag\":\"mate\",\"ridge\":704,\"a\":71,\"owners\":[91,93]},{\"tag\":\"mate\",\"ridge\":704,\"a\":79,\"owners\":[91,96]},{\"tag\":\"mate\",\"ridge\":538,\"a\":42,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":538,\"a\":90,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":594,\"a\":51,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":594,\"a\":93,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":898,\"a\":57,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":898,\"a\":94,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":540,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":652,\"a\":96,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":596,\"a\":69,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":596,\"a\":97,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":568,\"a\":73,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":568,\"a\":98,\"owners\":[73]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[45,48,75,77],\"full_literals\":[-49,12,15,33,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[53,70,79,80],\"full_literals\":[-50,18,28,37,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[32,40,41,58,72,74,81,89],\"full_literals\":[-51,7,9,10,23,30,32,39,40]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,49,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-53,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-54,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-55,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-56,53,55],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":9,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":42,\"full_literals\":[-11,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":73,\"full_literals\":[-31,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":65,\"full_literals\":[-26,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-27,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":90,\"full_literals\":[-41,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":98,\"full_literals\":[-48,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":97,\"full_literals\":[-47,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":47,\"full_literals\":[-14,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":51,\"full_literals\":[-16,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":56,\"full_literals\":[-21,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":57,\"full_literals\":[-22,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":91,\"full_literals\":[-42,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":92,\"full_literals\":[-43,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":93,\"full_literals\":[-44,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":94,\"full_literals\":[-45,62]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-59,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-63,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-57,-64,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-62,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-69,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-65,-72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-71,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[22,23,42,51,53,54,60,69,70,73,74,78,79,80,90,93,94,97,98]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[19,24,46,51,55,56,64,69,71,76,77,79,91,92,93,96,97]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[22,24,47,53,55,57,65,70,71,76,79,80,91,93,94,96,97]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[20,23,48,54,56,57,74,75,77,78,80,90,92,94,98]}]}"
  "p cnf 73 140\n-12 -11 0\n-19 -13 0\n-19 -15 0\n-19 -18 0\n-20 -19 0\n-21 -19 0\n-35 -11 0\n-35 -31 0\n-36 -1 0\n-36 -8 0\n-36 -10 0\n-36 -17 0\n-36 -19 0\n-36 -30 0\n-36 -33 0\n-38 -11 0\n-38 -19 0\n-38 -31 0\n-38 -36 0\n-41 -7 0\n-41 -9 0\n-41 -13 0\n-41 -14 0\n-41 -18 0\n-41 -20 0\n-41 -21 0\n-41 -23 0\n-41 -39 0\n-42 -19 0\n-42 -41 0\n-43 -19 0\n-43 -41 0\n-44 -21 0\n-44 -43 0\n-45 -16 0\n-45 -21 0\n-45 -42 0\n-45 -43 0\n-45 -44 0\n-48 -36 0\n-40 1 8 17 19 45 0\n-2 -3 -31 0\n-6 2 13 16 21 25 27 35 0\n-2 42 43 46 0\n-13 46 0\n-25 42 43 0\n-34 43 0\n-46 2 13 35 43 0\n-3 5 19 21 22 36 38 0\n-33 5 19 21 22 38 0\n-3 41 43 48 0\n-15 48 0\n-33 41 43 0\n-35 41 48 0\n-48 3 15 35 43 0\n-4 5 11 16 19 24 27 31 32 36 0\n-18 5 24 27 31 32 36 0\n-4 -5 -11 0\n-4 -5 -31 0\n-4 -19 -31 0\n-5 -11 -27 0\n-5 -18 -31 0\n-19 -27 -31 0\n-6 4 14 18 22 26 28 38 0\n-20 4 26 28 38 0\n-34 4 18 22 28 38 0\n-4 44 45 47 0\n-18 47 0\n-28 44 45 0\n-37 45 0\n-47 4 18 38 45 0\n-5 41 45 48 0\n-19 48 0\n-32 45 0\n-36 41 45 0\n-38 41 48 0\n-41 5 36 38 0\n-48 5 19 38 45 0\n-6 42 44 46 47 0\n-20 46 47 0\n-29 42 44 0\n-37 42 46 0\n-11 41 0\n-41 11 0\n-16 44 0\n-44 16 0\n-22 45 0\n-45 22 0\n-24 0\n-46 26 0\n-27 47 0\n-47 27 0\n-31 48 0\n-48 31 0\n-49 12 15 33 35 0\n-50 18 28 37 38 0\n-51 7 9 10 23 30 32 39 40 0\n-52 49 50 0\n-53 52 0\n-54 51 0\n-55 54 0\n-56 53 55 0\n56 0\n-11 57 0\n-31 57 0\n-26 58 0\n-27 58 0\n-41 59 0\n-48 59 0\n-47 60 0\n-14 61 0\n-16 61 0\n-21 61 0\n-22 61 0\n-42 62 0\n-43 62 0\n-44 62 0\n-45 62 0\n-59 63 0\n-58 63 0\n-58 -59 64 0\n-63 65 0\n-57 65 0\n-57 -63 66 0\n-57 -64 67 0\n-60 68 0\n-62 69 0\n-61 69 0\n-61 -62 70 0\n-69 71 0\n-70 72 0\n-68 -69 72 0\n-65 -72 73 0\n-66 -71 73 0\n-67 73 0\n-73 0\n4 5 11 16 18 19 24 27 28 31 32 36 37 38 41 44 45 47 48 0\n2 6 13 16 20 21 25 27 29 34 35 37 42 43 44 46 47 0\n4 6 14 18 20 22 26 28 29 34 37 38 42 44 45 46 47 0\n3 5 15 19 21 22 32 33 35 36 38 41 43 45 48 0\n"
  "141 -67 0 136 135 0\n142 4 5 11 16 18 19 27 28 31 32 36 37 38 41 44 45 47 48 0 89 137 0\n143 -45 37 63 0 120 107 92 106 90 80 45 119 108 109 54 35 36 37 38 39 81 79 47 46 44 138 0\n144 -44 45 36 59 0 109 108 72 87 74 76 54 73 52 33 34 50 49 140 0\n145 45 36 65 0 122 120 107 92 68 119 108 109 76 73 123 105 104 70 74 72 144 85 67 69 142 0\n146 -45 63 0 120 106 90 37 143 82 0\n147 65 0 122 119 108 146 75 145 0\n148 -72 0 147 136 133 0\n149 -70 0 148 131 0\n150 5 48 45 11 18 19 27 28 31 32 36 37 38 41 16 44 47 0 89 142 56 0\n151 63 45 36 0 89 74 70 119 120 108 109 144 107 83 73 93 76 72 85 69 92 57 150 0\n152 47 48 19 44 41 45 36 0 72 76 93 69 85 83 74 70 68 91 150 0\n153 48 19 44 41 45 36 0 148 87 74 52 54 76 72 152 110 126 132 127 128 116 113 53 51 140 0\n154 19 44 41 45 36 0 141 136 69 151 87 70 153 94 109 18 105 78 124 125 59 62 134 121 66 71 130 106 127 128 90 65 115 111 81 79 139 0\n155 44 41 45 36 0 70 85 154 2 3 4 5 6 17 29 31 73 81 47 46 94 8 60 63 55 71 42 43 48 138 0\n156 -44 0 149 86 117 112 129 0\n157 -16 0 156 85 0\n158 45 36 0 141 156 157 70 87 69 155 22 23 24 25 26 30 32 84 108 81 47 46 7 16 104 77 125 58 61 121 71 106 90 64 44 138 0\n159 -45 0 149 88 118 114 129 0\n160 -37 0 159 70 0\n161 -32 0 159 74 0\n162 -28 0 159 156 69 0\n163 36 0 159 158 0\n164 -1 0 163 9 0\n165 -8 0 163 10 0\n166 -10 0 163 11 0\n167 -17 0 163 12 0\n168 -19 0 163 13 0\n169 -30 0 163 14 0\n170 -33 0 163 15 0\n171 -38 0 163 19 0\n172 -48 0 163 40 0\n173 41 0 163 159 75 0\n174 -40 0 165 159 164 168 167 41 0\n175 -15 0 172 52 0\n176 -7 0 173 20 0\n177 -9 0 173 21 0\n178 -18 0 173 24 0\n179 -23 0 173 27 0\n180 -39 0 173 28 0\n181 11 0 173 84 0\n182 -51 0 174 176 166 180 169 161 177 179 97 0\n183 -50 0 178 171 160 162 96 0\n184 -12 0 181 1 0\n185 -35 0 181 7 0\n186 -54 0 182 100 0\n187 -49 0 184 170 175 185 95 0\n188 -55 0 186 101 0\n189 -52 0 187 183 98 0\n190 53 0 188 103 102 0\n191 0 190 189 99 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029 Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record029
