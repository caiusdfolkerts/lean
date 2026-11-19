module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00008Data
public import GraphInputsRow29Part00008Frames
public import GraphInputsRow29Part00008Leaves
public import GraphInputsRow29Part00008Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record012
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 8072706730108125184, (certNat% 3), (certNat% 4), (certNat% 5), 29703993819136, 15199683102113792]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record012_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record013
def vertexColumn : Fields := ⟨10, (certNat% 6)⟩
def kindColumn : Fields := ⟨3, (certNat% 7)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨83, by decide⟩, ⟨95, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨113, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), 774056185954304, (certNat% 10), 76561193665298432]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), 879609302220800, 6755399441055744, (certNat% 13)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17), (certNat% 18), 422212465065984]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), 2146246697418752, (certNat% 21), (certNat% 22), (certNat% 23), (certNat% 24)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c5 c4
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record013_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record014
def vertexColumn : Fields := ⟨10, (certNat% 25)⟩
def kindColumn : Fields := ⟨3, (certNat% 26)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), (certNat% 29), 17732923532771328, (certNat% 30), (certNat% 31), 564251328512]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record014_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "d6354d31acc725c5713c1f392acb1a9687ae1ac6a9b1695a361db0e63a4e2b86e8791e1783ee47516c5a9565391e785d16c569715955554d4756354d4b4ad1b51d1743de0ec3c4e9364e532cc7362cab1ad1bc1e8761e4731c6785d1715c3743c8f07f849485a0ea86918a61382e464590e5852950d1342d28c530cc4b0ac1b21c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6d24934db6926d26db4926d36db4924926db69269269249b492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 72)]))
 (.leaf ([(facetIndex 83), (facetIndex 102)])))
 (.branch 3
 (.leaf ([(facetIndex 47), (facetIndex 48), (facetIndex 73), (facetIndex 95)]))
 (.branch 4
 (.leaf ([(facetIndex 33), (facetIndex 39), (facetIndex 50), (facetIndex 67), (facetIndex 75)]))
 (.leaf ([(facetIndex 49), (facetIndex 63), (facetIndex 66), (facetIndex 74)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 79), (facetIndex 84), (facetIndex 103)]))
 (.branch 7
 (.leaf ([(facetIndex 94), (facetIndex 100), (facetIndex 105)]))
 (.leaf ([(facetIndex 32), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 64), (facetIndex 86), (facetIndex 101)]))))
 (.branch 9
 (.leaf ([(facetIndex 78), (facetIndex 85), (facetIndex 98), (facetIndex 99)]))
 (.branch 10
 (.leaf ([(facetIndex 88), (facetIndex 97), (facetIndex 104)]))
 (.leaf ([(facetIndex 51), (facetIndex 96)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "695176889a26000009078510005800342000003407477700000000a3422000000030000037z20;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3, 4]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6, 7]
def grouped3_0012 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0013 : List Nat := [6]
def grouped3_0014 : List Nat := [6, 7]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [8, 9, 10]
def grouped3_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [9, 10]
def grouped3_0020 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record004" 73

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record004" "{\"ridges\":[[12,268],[14,385],[17,273],[17,280],[26,896],[29,268],[32,278],[37,385],[40,273],[40,280],[47,402],[49,273],[49,784],[51,771],[54,280],[57,268],[58,268],[59,268],[59,385],[61,308],[62,340],[64,784],[65,385],[68,385],[70,273],[70,280],[71,273],[71,280],[73,432],[74,784],[75,273],[75,784],[78,278],[88,278],[91,642],[94,778],[95,688],[96,402],[98,308],[99,340],[101,540],[104,340],[105,840]],\"owners\":[[12,268,[78,83,84,98,99,101,102,103],[29,54,57,58,59]],[29,268,[98,99,101,102,103],[12,54,57,58,59,78,83,84]],[57,268,[78,83,84,99,101,103],[12,29,54,58,59,98,102]],[58,268,[78,83,84,98,101,102],[12,29,54,57,59,99,103]],[59,268,[78,84,98,99,101,103],[12,29,54,57,58,83,102]],[14,385,[43,47,51,72,73,75],[37,59,65,68]],[37,385,[72,73,75],[14,43,47,51,59,65,68]],[59,385,[47,51,73,75],[14,37,43,65,68,72]],[65,385,[43,47,51,75],[14,37,59,68,72,73]],[68,385,[43,47,72,73],[14,37,51,59,65,75]],[17,273,[32,47,49,61,62,64,73,74,75],[40,54,70,71]],[40,273,[61,62,64,73,74,75],[17,32,47,49,54,70,71]],[49,273,[17,54,61,62,70,71,73],[32,40,47,64,74,75]],[70,273,[32,47,49,62,64,74,75],[17,40,54,61,71,73]],[71,273,[32,47,49,61,64,73,75],[17,40,54,62,70,74]],[75,273,[17,32,40,54,61,62,70,71],[47,49,64,73,74]],[17,280,[78,94,98,99,101,105],[40,54,70,71]],[40,280,[98,99,101,105],[17,54,70,71,78,94]],[54,280,[94,105],[17,40,70,71,78,98,99,101]],[70,280,[78,94,99,101,105],[17,40,54,71,98]],[71,280,[78,94,98,101],[17,40,54,70,99,105]],[91,642,[48,50,95],[22,38,51,89,90,96]],[26,896,[51,75,96],[68,91]],[32,278,[78,88],[]],[78,278,[32,88],[]],[88,278,[32,78],[]],[51,771,[39,49],[]],[47,402,[96],[]],[96,402,[47],[]],[49,784,[101,104,105],[64,74,75,88,94,96]],[64,784,[94,96,105],[49,74,75,88,101,104]],[74,784,[88,94,96,101],[49,64,75,104,105]],[75,784,[88,94,101,104,105],[49,64,74,96]],[61,308,[98],[]],[98,308,[61],[]],[62,340,[99,104],[]],[99,340,[62,104],[]],[104,340,[62,99],[]],[73,432,[],[]],[101,540,[79,100],[]],[94,778,[84],[]],[95,688,[],[]],[105,840,[103],[]]],\"edges\":[[28,[12,17,29,40,43,54,57,58,59,70,71,72,78,83,84,94,98,99,101,102,103,105]],[33,[17,32,40,47,49,54,61,62,64,70,71,73,74,75,78,88,94,96,98,99,101,104,105]],[42,[14,26,37,43,47,51,59,65,68,72,73,75,83,91,96,102]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,31,33,34,40,41,43,44,45],[-5,40,41,43,44,45],[-17,31,33,34,41,43,45],[-18,31,33,34,40,43,44],[-19,31,34,40,41,43,45],[-2,10,11,15,27,28,30],[-7,27,28,30],[-19,11,15,28,30],[-23,10,11,15,30],[-24,10,11,27,28],[-3,6,11,13,20,21,22,28,29,30],[-9,20,21,22,28,29,30],[-13,3,16,20,21,25,26,28],[-25,6,11,13,21,22,29,30],[-26,6,11,13,20,22,28,30],[-30,3,6,9,16,20,21,25,26],[-3,31,37,40,41,43,47],[-9,40,41,43,47],[-16,37,47],[-25,31,37,41,43,47],[-26,31,37,40,43],[-36,12,14,38],[-4,15,30,39],[-6,31,35],[-31,6,35],[-35,6,31],[-15,8,13],[-11,39],[-39,11],[-13,43,46,47],[-22,37,39,47],[-29,35,37,39,43],[-30,35,37,43,46,47],[-20,40],[-40,20],[-21,41,46],[-41,21,46],[-46,21,41],[-28],[-43,32,42],[-37,34],[-38],[-47,45],[-10,48],[-27,48],[-33,49],[-44,49],[-11,50],[-12,50],[-8,51],[-14,51],[-30,51],[-13,52],[-29,52],[-32,53],[-34,53],[-45,53],[-37,54],[-42,54],[-47,54],[-6,55],[-20,55],[-21,55],[-22,55],[-43,55],[-31,56],[-40,56],[-41,56],[-35,57],[-46,57],[-39,58],[-49,59],[-48,59],[-52,60],[-51,60],[-60,61],[-50,61],[-61,62],[-59,62],[-59,-61,63],[-55,64],[-54,64],[-54,-55,65],[-64,66],[-65,67],[-53,66],[-53,-64,67],[-58,68],[-57,68],[-68,69],[-56,69],[-56,-68,70],[-69,71],[-70,72],[-66,-69,72],[-67,72],[-62,-72,73],[-63,-71,73],[-73],[1,3,5,9,10,16,17,18,19,25,26,27,31,33,34,37,40,41,43,44,45,47],[3,6,9,11,13,16,20,21,22,25,26,28,29,30,31,35,37,39,40,41,43,46,47],[2,4,7,10,11,15,19,23,24,27,28,30,33,36,39,44]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":268,\"a\":12,\"owners\":[78,83,84,98,99,101,102,103]},{\"tag\":\"mate\",\"ridge\":268,\"a\":29,\"owners\":[98,99,101,102,103]},{\"tag\":\"mate\",\"ridge\":268,\"a\":57,\"owners\":[78,83,84,99,101,103]},{\"tag\":\"mate\",\"ridge\":268,\"a\":58,\"owners\":[78,83,84,98,101,102]},{\"tag\":\"mate\",\"ridge\":268,\"a\":59,\"owners\":[78,84,98,99,101,103]},{\"tag\":\"mate\",\"ridge\":385,\"a\":14,\"owners\":[43,47,51,72,73,75]},{\"tag\":\"mate\",\"ridge\":385,\"a\":37,\"owners\":[72,73,75]},{\"tag\":\"mate\",\"ridge\":385,\"a\":59,\"owners\":[47,51,73,75]},{\"tag\":\"mate\",\"ridge\":385,\"a\":65,\"owners\":[43,47,51,75]},{\"tag\":\"mate\",\"ridge\":385,\"a\":68,\"owners\":[43,47,72,73]},{\"tag\":\"mate\",\"ridge\":273,\"a\":17,\"owners\":[32,47,49,61,62,64,73,74,75]},{\"tag\":\"mate\",\"ridge\":273,\"a\":40,\"owners\":[61,62,64,73,74,75]},{\"tag\":\"mate\",\"ridge\":273,\"a\":49,\"owners\":[17,54,61,62,70,71,73]},{\"tag\":\"mate\",\"ridge\":273,\"a\":70,\"owners\":[32,47,49,62,64,74,75]},{\"tag\":\"mate\",\"ridge\":273,\"a\":71,\"owners\":[32,47,49,61,64,73,75]},{\"tag\":\"mate\",\"ridge\":273,\"a\":75,\"owners\":[17,32,40,54,61,62,70,71]},{\"tag\":\"mate\",\"ridge\":280,\"a\":17,\"owners\":[78,94,98,99,101,105]},{\"tag\":\"mate\",\"ridge\":280,\"a\":40,\"owners\":[98,99,101,105]},{\"tag\":\"mate\",\"ridge\":280,\"a\":54,\"owners\":[94,105]},{\"tag\":\"mate\",\"ridge\":280,\"a\":70,\"owners\":[78,94,99,101,105]},{\"tag\":\"mate\",\"ridge\":280,\"a\":71,\"owners\":[78,94,98,101]},{\"tag\":\"mate\",\"ridge\":642,\"a\":91,\"owners\":[48,50,95]},{\"tag\":\"mate\",\"ridge\":896,\"a\":26,\"owners\":[51,75,96]},{\"tag\":\"mate\",\"ridge\":278,\"a\":32,\"owners\":[78,88]},{\"tag\":\"mate\",\"ridge\":278,\"a\":78,\"owners\":[32,88]},{\"tag\":\"mate\",\"ridge\":278,\"a\":88,\"owners\":[32,78]},{\"tag\":\"mate\",\"ridge\":771,\"a\":51,\"owners\":[39,49]},{\"tag\":\"mate\",\"ridge\":402,\"a\":47,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":402,\"a\":96,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":784,\"a\":49,\"owners\":[101,104,105]},{\"tag\":\"mate\",\"ridge\":784,\"a\":64,\"owners\":[94,96,105]},{\"tag\":\"mate\",\"ridge\":784,\"a\":74,\"owners\":[88,94,96,101]},{\"tag\":\"mate\",\"ridge\":784,\"a\":75,\"owners\":[88,94,101,104,105]},{\"tag\":\"mate\",\"ridge\":308,\"a\":61,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":308,\"a\":98,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":340,\"a\":62,\"owners\":[99,104]},{\"tag\":\"mate\",\"ridge\":340,\"a\":99,\"owners\":[62,104]},{\"tag\":\"mate\",\"ridge\":340,\"a\":104,\"owners\":[62,99]},{\"tag\":\"mate\",\"ridge\":432,\"a\":73,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":540,\"a\":101,\"owners\":[79,100]},{\"tag\":\"mate\",\"ridge\":778,\"a\":94,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":688,\"a\":95,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":840,\"a\":105,\"owners\":[103]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":43,\"full_literals\":[-10,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":72,\"full_literals\":[-27,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-33,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":102,\"full_literals\":[-44,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":47,\"full_literals\":[-11,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":48,\"full_literals\":[-12,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":39,\"full_literals\":[-8,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":50,\"full_literals\":[-14,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":75,\"full_literals\":[-30,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":49,\"full_literals\":[-13,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-29,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-32,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-34,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":103,\"full_literals\":[-45,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":94,\"full_literals\":[-37,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":100,\"full_literals\":[-42,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":105,\"full_literals\":[-47,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":32,\"full_literals\":[-6,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":61,\"full_literals\":[-20,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":62,\"full_literals\":[-21,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":64,\"full_literals\":[-22,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":101,\"full_literals\":[-43,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":78,\"full_literals\":[-31,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":98,\"full_literals\":[-40,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":99,\"full_literals\":[-41,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":88,\"full_literals\":[-35,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":104,\"full_literals\":[-46,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":96,\"full_literals\":[-39,58]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-55,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-64,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-68,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-69,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-62,-72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-71,73],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":28,\"owners\":[12,17,29,40,43,54,57,58,59,70,71,72,78,83,84,94,98,99,101,102,103,105]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[17,32,40,47,49,54,61,62,64,70,71,73,74,75,78,88,94,96,98,99,101,104,105]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[14,26,37,43,47,51,59,65,68,72,73,75,83,91,96,102]}]}"
  "103 3 6 9 11 13 16 20 21 22 25 26 29 30 31 35 37 39 40 41 43 46 47 0 39 101 0\n104 2 4 7 10 11 15 19 23 24 27 30 33 36 39 44 0 39 102 0\n105 62 0 42 39 78 79 76 77 72 73 74 75 48 49 46 47 44 45 53 50 51 52 29 10 22 27 7 23 8 6 9 104 0\n106 -72 0 105 99 97 0\n107 -70 0 106 94 0\n108 -67 0 106 96 0\n109 -65 0 108 85 0\n110 61 56 64 0 39 81 65 62 35 82 58 66 21 63 60 68 18 19 61 17 20 16 13 38 26 64 76 77 74 48 54 29 103 0\n111 56 66 63 0 84 82 60 58 19 81 62 35 65 86 57 56 66 68 5 17 20 21 18 110 80 72 73 46 47 44 45 1 3 4 2 100 0\n112 66 63 0 107 39 84 81 82 61 62 63 64 65 58 60 35 19 111 92 88 89 71 69 70 28 32 33 25 37 30 11 14 15 12 103 0\n113 64 69 0 90 88 71 28 89 70 91 68 36 67 34 69 66 24 81 82 64 65 58 60 18 32 30 19 17 20 21 33 103 0\n114 43 69 0 108 113 87 57 43 90 88 71 56 41 31 19 28 89 70 91 68 36 67 34 69 66 24 18 32 30 17 20 21 33 103 0\n115 -43 32 0 109 40 65 59 83 0\n116 69 0 108 113 87 55 114 115 0\n117 71 0 116 93 0\n118 -66 0 116 106 95 0\n119 -63 0 117 99 98 0\n120 0 118 119 112 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e5274e334c6713ce4a72e2aca668bae1a66c5a9665a568d876c3a8e63a4e4789e0fb91665392e785d1715a5595955351d58d5352d4749d0f783b0f13a4d9394cb31cd8b32cab46c9b0ef07a1d8791e1745c9715d0f23c1fe43141b2921aa4619a160d84e0b99162469195150d50d1342d18c930cc8b12c2b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4db6d36db6926926da6d24db69a6924934db49a4926936d2492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 37), (facetIndex 76), (facetIndex 80), (facetIndex 82), (facetIndex 86)]))
 (.leaf ([(facetIndex 31), (facetIndex 42), (facetIndex 44), (facetIndex 45), (facetIndex 46)])))
 (.branch 3
 (.leaf ([(facetIndex 32), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60)]))
 (.leaf ([(facetIndex 34), (facetIndex 41), (facetIndex 47), (facetIndex 48)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 36), (facetIndex 51), (facetIndex 66), (facetIndex 72)]))
 (.leaf ([(facetIndex 30), (facetIndex 73), (facetIndex 81)])))
 (.branch 7
 (.leaf ([(facetIndex 35), (facetIndex 55), (facetIndex 61), (facetIndex 62)]))
 (.branch 8
 (.leaf ([(facetIndex 84), (facetIndex 85), (facetIndex 93), (facetIndex 99)]))
 (.leaf ([(facetIndex 50), (facetIndex 64), (facetIndex 71)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "7000007000000077005000000054800004080662222060004803311101300004630215z1e;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 49), (facetIndex 92)]))
 (.leaf ([(facetIndex 63), (facetIndex 98)])))
 (.branch 3
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 90), (facetIndex 96)]))
 (.branch 4
 (.leaf ([(facetIndex 43), (facetIndex 56), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 88), (facetIndex 94)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 53), (facetIndex 67)]))
 (.leaf ([(facetIndex 38), (facetIndex 65), (facetIndex 95), (facetIndex 97)])))
 (.branch 8
 (.leaf ([(facetIndex 52), (facetIndex 77), (facetIndex 89), (facetIndex 91)]))
 (.branch 9
 (.leaf ([(facetIndex 54), (facetIndex 68), (facetIndex 83)]))
 (.leaf ([(facetIndex 87)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "1626400727490008000227044000338506010000003085700000000300556z26;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4, 5]
def grouped2_0003 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0004 : List Nat := [6]
def grouped2_0005 : List Nat := [6, 7, 8]
def grouped2_0006 : List Nat := [7]
def grouped2_0007 : List Nat := [7, 8]
def grouped2_0008 : List Nat := [8]
def grouped3_0009 : List Nat := [0]
def grouped3_0010 : List Nat := [0, 1]
def grouped3_0011 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0013 : List Nat := [1]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [2, 3, 4]
def grouped3_0016 : List Nat := [3]
def grouped3_0017 : List Nat := [3, 4]
def grouped3_0018 : List Nat := [4]
def grouped3_0019 : List Nat := [5]
def grouped3_0020 : List Nat := [5, 6]
def grouped3_0021 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0022 : List Nat := [6]
def grouped3_0023 : List Nat := [7]
def grouped3_0024 : List Nat := [7, 8, 9]
def grouped3_0025 : List Nat := [8]
def grouped3_0026 : List Nat := [8, 9]
def grouped3_0027 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record009" 82

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record009" "{\"ridges\":[[6,138],[17,392],[24,580],[28,772],[29,896],[31,138],[37,580],[42,138],[44,138],[45,138],[46,138],[53,705],[60,268],[66,772],[67,833],[68,645],[71,392],[71,400],[72,896],[76,580],[78,652],[79,778],[82,578],[85,772],[86,580],[89,282],[90,712],[91,778],[93,642],[95,156],[96,840],[97,652],[99,772]],\"owners\":[[6,138,[74,77,78,88,89,90,91],[31,42,44,45,46]],[31,138,[88,89,90,91],[6,42,44,45,46,74,77,78]],[42,138,[77,78,90,91],[6,31,44,45,46,74,88,89]],[44,138,[74,77,78,89,90,91],[6,31,42,45,46,88]],[45,138,[74,77,78,88,89,91],[6,31,42,44,46,90]],[46,138,[74,78,88,90],[6,31,42,44,45,77,89,91]],[60,268,[75,79,94,96],[12,32,57,58,59,77,95,97]],[17,392,[77,89,91,95,97],[46,60,71]],[71,392,[77,91,97],[17,46,60,89,95]],[71,400,[29,83,93,99],[18,50,64,89,95]],[82,578,[53,90],[24,37,49,76,86,92]],[24,580,[63,67,96,98],[37,76,82,86]],[37,580,[96,98],[24,63,67,76,82,86]],[76,580,[63,67,98],[24,37,82,86,96]],[86,580,[63,67,96],[24,37,76,82,98]],[93,642,[39,53,78,90],[26,51,54,84,87,91]],[28,772,[40,67,68,79,87,96,97],[66,85,99]],[66,772,[79,87,96,97],[28,40,67,68,85,99]],[85,772,[67,68,96,97],[28,40,66,79,87,99]],[99,772,[40,67,79,96],[28,66,68,85,87,97]],[29,896,[54,68,87,91,97],[72,93,99]],[72,896,[87,91,97],[29,54,68,93,99]],[68,645,[39,65],[]],[89,282,[43,75],[]],[53,705,[],[]],[95,156,[56,74],[]],[67,833,[],[]],[78,652,[97],[]],[97,652,[78],[]],[79,778,[91],[]],[91,778,[79],[]],[90,712,[],[]],[96,840,[],[]]],\"edges\":[[27,[6,17,31,42,44,45,46,56,60,69,71,74,77,78,88,89,90,91,95,97]],[41,[24,37,49,53,63,67,76,82,86,90,92,96,98]],[44,[28,29,40,52,54,66,67,68,72,79,85,87,91,93,96,97,99]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-34,-16],[-34,-19],[-34,-23],[-39,-34],[-1,31,34,35,43,44,45,46],[-6,43,44,45,46],[-10,34,35,45,46],[-12,31,34,35,44,45,46],[-13,31,34,35,43,44,46],[-14,31,35,43,45],[-21,32,36,49,51],[-2,34,44,46,50,52],[-29,34,46,52],[-29,5,38,48,54],[-37,18,45],[-3,22,26,51,53],[-7,51,53],[-33,22,26,53],[-41,22,26,51],[-48,8,18,35,45],[-4,9,26,27,36,42,51,52],[-25,36,42,51,52],[-40,26,27,51,52],[-54,9,26,36,51],[-5,19,27,42,46,52],[-30,42,46,52],[-27,8,24],[-44,11,32],[-18],[-50,20,31],[-26],[-35,52],[-52,35],[-36,46],[-46,36],[-45],[-51],[-55,39,40,48,54],[-56,16,23,29],[-57,55,56],[-58,57],[-59,58],[-60,59],[60],[-15,61],[-47,61],[-22,62],[-53,62],[-35,63],[-36,63],[-11,64],[-20,64],[-28,64],[-31,65],[-32,65],[-43,65],[-49,65],[-8,66],[-9,66],[-24,67],[-52,67],[-17,68],[-34,68],[-46,68],[-19,69],[-27,69],[-38,69],[-42,70],[-62,71],[-61,71],[-65,72],[-64,72],[-72,73],[-63,73],[-71,74],[-71,-73,75],[-67,76],[-66,76],[-70,77],[-69,77],[-77,78],[-68,78],[-68,-77,79],[-78,80],[-79,81],[-76,80],[-76,-78,81],[-74,-81,82],[-75,-80,82],[-82],[1,2,6,10,12,13,14,20,21,28,29,31,34,35,43,44,45,46,50,52],[3,7,15,18,22,26,33,37,41,45,47,51,53],[4,5,9,17,19,25,26,27,30,36,40,42,46,48,51,52,54]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":77,\"b\":50},{\"tag\":\"incompatible\",\"a\":77,\"b\":54},{\"tag\":\"incompatible\",\"a\":77,\"b\":64},{\"tag\":\"incompatible\",\"a\":84,\"b\":77},{\"tag\":\"mate\",\"ridge\":138,\"a\":6,\"owners\":[74,77,78,88,89,90,91]},{\"tag\":\"mate\",\"ridge\":138,\"a\":31,\"owners\":[88,89,90,91]},{\"tag\":\"mate\",\"ridge\":138,\"a\":42,\"owners\":[77,78,90,91]},{\"tag\":\"mate\",\"ridge\":138,\"a\":44,\"owners\":[74,77,78,89,90,91]},{\"tag\":\"mate\",\"ridge\":138,\"a\":45,\"owners\":[74,77,78,88,89,91]},{\"tag\":\"mate\",\"ridge\":138,\"a\":46,\"owners\":[74,78,88,90]},{\"tag\":\"mate\",\"ridge\":268,\"a\":60,\"owners\":[75,79,94,96]},{\"tag\":\"mate\",\"ridge\":392,\"a\":17,\"owners\":[77,89,91,95,97]},{\"tag\":\"mate\",\"ridge\":392,\"a\":71,\"owners\":[77,91,97]},{\"tag\":\"mate\",\"ridge\":400,\"a\":71,\"owners\":[29,83,93,99]},{\"tag\":\"mate\",\"ridge\":578,\"a\":82,\"owners\":[53,90]},{\"tag\":\"mate\",\"ridge\":580,\"a\":24,\"owners\":[63,67,96,98]},{\"tag\":\"mate\",\"ridge\":580,\"a\":37,\"owners\":[96,98]},{\"tag\":\"mate\",\"ridge\":580,\"a\":76,\"owners\":[63,67,98]},{\"tag\":\"mate\",\"ridge\":580,\"a\":86,\"owners\":[63,67,96]},{\"tag\":\"mate\",\"ridge\":642,\"a\":93,\"owners\":[39,53,78,90]},{\"tag\":\"mate\",\"ridge\":772,\"a\":28,\"owners\":[40,67,68,79,87,96,97]},{\"tag\":\"mate\",\"ridge\":772,\"a\":66,\"owners\":[79,87,96,97]},{\"tag\":\"mate\",\"ridge\":772,\"a\":85,\"owners\":[67,68,96,97]},{\"tag\":\"mate\",\"ridge\":772,\"a\":99,\"owners\":[40,67,79,96]},{\"tag\":\"mate\",\"ridge\":896,\"a\":29,\"owners\":[54,68,87,91,97]},{\"tag\":\"mate\",\"ridge\":896,\"a\":72,\"owners\":[87,91,97]},{\"tag\":\"mate\",\"ridge\":645,\"a\":68,\"owners\":[39,65]},{\"tag\":\"mate\",\"ridge\":282,\"a\":89,\"owners\":[43,75]},{\"tag\":\"mate\",\"ridge\":705,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":156,\"a\":95,\"owners\":[56,74]},{\"tag\":\"mate\",\"ridge\":833,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":652,\"a\":78,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":652,\"a\":97,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":778,\"a\":79,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":778,\"a\":91,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":712,\"a\":90,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":840,\"a\":96,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[84,85,93,99],\"full_literals\":[-55,39,40,48,54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[50,64,71],\"full_literals\":[-56,16,23,29]},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,55,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0005\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-60,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-15,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":92,\"full_literals\":[-47,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":63,\"full_literals\":[-22,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":98,\"full_literals\":[-53,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":78,\"full_literals\":[-35,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":79,\"full_literals\":[-36,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":43,\"full_literals\":[-11,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":56,\"full_literals\":[-20,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":69,\"full_literals\":[-28,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-31,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":75,\"full_literals\":[-32,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":88,\"full_literals\":[-43,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":94,\"full_literals\":[-49,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":39,\"full_literals\":[-8,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":40,\"full_literals\":[-9,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":65,\"full_literals\":[-24,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":97,\"full_literals\":[-52,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":52,\"full_literals\":[-17,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":77,\"full_literals\":[-34,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":91,\"full_literals\":[-46,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":54,\"full_literals\":[-19,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":68,\"full_literals\":[-27,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":83,\"full_literals\":[-38,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":87,\"full_literals\":[-42,70]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-73,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-77,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-78,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-74,-81,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-75,-80,82],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":27,\"owners\":[6,17,31,42,44,45,46,56,60,69,71,74,77,78,88,89,90,91,95,97]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[24,37,49,53,63,67,76,82,86,90,92,96,98]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[28,29,40,52,54,66,67,68,72,79,85,87,91,93,96,97,99]}]}"
  "94 -37 0 36 29 15 0\n95 59 0 44 43 0\n96 58 0 95 42 0\n97 57 0 96 41 0\n98 1 2 6 10 12 13 14 20 21 28 29 31 34 35 43 44 46 50 52 0 36 91 0\n99 3 7 15 22 33 41 47 53 0 29 31 94 36 37 92 0\n100 4 5 9 17 19 25 27 30 36 40 42 46 48 52 54 0 31 37 93 0\n101 71 0 37 31 69 70 47 48 45 46 19 17 16 18 99 0\n102 74 0 101 75 0\n103 -81 0 102 90 88 0\n104 -79 0 103 85 0\n105 34 73 0 37 36 74 50 35 73 72 51 71 55 28 56 6 57 11 52 54 30 49 10 33 53 7 12 13 5 8 9 98 0\n106 76 73 0 104 36 29 37 31 97 105 63 83 80 67 79 68 4 3 2 1 74 50 35 49 33 77 78 60 58 59 27 20 24 23 38 40 39 14 25 0\n107 73 0 103 105 63 106 82 87 0\n108 75 0 107 101 76 0\n109 -80 0 108 90 89 0\n110 -78 0 109 84 0\n111 -76 0 109 86 0\n112 -77 0 110 81 0\n113 -68 0 110 82 0\n114 -67 0 111 77 0\n115 -66 0 111 78 0\n116 -70 0 112 79 0\n117 -69 0 112 80 0\n118 -17 0 113 62 0\n119 -46 0 113 64 0\n120 -52 0 114 61 0\n121 -8 0 115 58 0\n122 -9 0 115 59 0\n123 -42 0 116 68 0\n124 -19 0 117 65 0\n125 -27 0 117 66 0\n126 -36 0 119 34 0\n127 -35 0 120 32 0\n128 -48 0 121 29 127 36 20 0\n129 -54 0 122 31 126 37 24 0\n130 -30 0 123 119 120 26 0\n131 -25 0 123 126 37 120 22 0\n132 -4 0 123 31 122 126 125 37 120 21 0\n133 -40 0 125 31 37 120 23 0\n134 -5 0 125 123 124 119 120 25 0\n135 0 132 134 122 118 124 131 125 130 126 133 123 119 128 120 129 100 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record016
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e619c1f38a9a99a4e87ab1996358b61da8e63a4e1b91e2785e0fb91d46d1e2669c6699666594e479b1595354b5a358d9346d4749d17743b0e6364d5334d332cc73a2d8b92e2b4ac6b46c9b16c3ba1d8791cc729d1725c570de0f43c8f13c1f1d03ce0b0a1982ee05911c7094643919495154350b41dc0e8360e4318e0b42c2b21c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b49b6db6d36d36d26d34d349a49b6924924db6924924da4924d2492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 76), (facetIndex 78), (facetIndex 82), (facetIndex 83)]))
 (.leaf ([(facetIndex 45), (facetIndex 67), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 86), (facetIndex 90), (facetIndex 101)]))
 (.branch 4
 (.leaf ([(facetIndex 69), (facetIndex 73)]))
 (.leaf ([(facetIndex 92), (facetIndex 97)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 46), (facetIndex 68), (facetIndex 105)]))
 (.leaf ([(facetIndex 38), (facetIndex 87), (facetIndex 91)])))
 (.branch 8
 (.leaf ([(facetIndex 88), (facetIndex 100), (facetIndex 104)]))
 (.branch 9
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 96), (facetIndex 98)]))
 (.leaf ([(facetIndex 94), (facetIndex 95), (facetIndex 99)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "57002798489904620762000001000000300035100000000888800000000510000006z26;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3, 4]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0013 : List Nat := [6]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8, 9]
def grouped3_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [8, 9]
def grouped3_0018 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record016" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record016" 60

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record016" "{\"ridges\":[[8,578],[16,148],[22,400],[37,148],[41,577],[41,578],[51,578],[59,400],[60,578],[61,577],[61,578],[62,578],[64,148],[67,588],[69,652],[70,148],[71,148],[72,400],[73,708],[76,600],[77,280],[78,664],[80,616],[82,720],[83,848],[84,400],[90,588],[92,652],[97,708],[101,616]],\"owners\":[[41,577,[76,80,82,83],[8,51,60,61,62,67,73]],[61,577,[67,76,80,83],[8,41,51,60,62,73,82]],[8,578,[90,97,101],[41,51,60,61,62]],[41,578,[101],[8,51,60,61,62,90,97]],[51,578,[97],[8,41,60,61,62,90,101]],[60,578,[90,97],[8,41,51,61,62,101]],[61,578,[90,101],[8,41,51,60,62,97]],[62,578,[90,97,101],[8,41,51,60,61]],[16,148,[87,94,95,96,104],[37,64,70,71,72]],[37,148,[104],[16,64,70,71,72,87,94,95,96]],[64,148,[94,95,96],[16,37,70,71,72,87,104]],[70,148,[87,95,96,104],[16,37,64,71,72,94]],[71,148,[87,94,96,104],[16,37,64,70,72,95]],[77,280,[88,99],[19,47,65,75,79,100,104,105]],[22,400,[96,100,104,105],[59,72,77,84]],[59,400,[104,105],[22,72,77,84,96,100]],[72,400,[100,105],[22,59,77,84,96,104]],[84,400,[96,100,104],[22,59,72,77,105]],[67,588,[90],[]],[90,588,[67],[]],[69,652,[92],[]],[92,652,[69],[]],[73,708,[97],[]],[97,708,[73],[]],[76,600,[],[]],[78,664,[105],[]],[80,616,[101],[]],[101,616,[80],[]],[82,720,[],[]],[83,848,[],[]]],\"edges\":[[32,[16,22,37,46,55,57,59,64,70,71,72,77,78,82,84,87,94,95,96,100,104,105]],[41,[8,41,51,60,61,62,67,73,76,80,82,83,90,97,101]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record016" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record016\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-5,21,24,25,26],[-12,15,21,24,26],[-1,30,35,38],[-5,38],[-7,35],[-11,30,35],[-12,30,38],[-13,30,35,38],[-2,28,32,33,34,39],[-4,39],[-14,32,33,34],[-17,28,33,34,39],[-18,28,32,34,39],[-22,29,36],[-3,34,37,39,40],[-10,39,40],[-19,37,40],[-27,34,37,39],[-15,30],[-30,15],[-16,31],[-31,16],[-20,35],[-35,20],[-21],[-23,40],[-24,38],[-38,24],[-25],[-26],[-15,41],[-24,41],[-30,42],[-38,42],[-43,16,20],[-16,43],[-20,43],[-44,31,35],[-31,44],[-35,44],[-6,45],[-40,45],[-28,46],[-29,47],[-37,47],[-39,47],[-8,48],[-9,48],[-34,48],[-32,49],[-33,49],[-36,49],[-41,50],[-51,43,44],[-44,51],[-43,51],[-43,-44,52],[-51,53],[-52,54],[-42,53],[-54,55],[-50,-53,55],[-46,56],[-45,56],[-49,57],[-48,57],[-57,58],[-47,58],[-58,59],[-56,59],[-55,-59,60],[-60],[2,3,4,6,8,9,10,14,17,18,19,22,23,25,27,28,32,33,34,37,39,40],[1,5,7,11,12,13,15,20,21,24,25,26,30,35,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":577,\"a\":41,\"owners\":[76,80,82,83]},{\"tag\":\"mate\",\"ridge\":577,\"a\":61,\"owners\":[67,76,80,83]},{\"tag\":\"mate\",\"ridge\":578,\"a\":8,\"owners\":[90,97,101]},{\"tag\":\"mate\",\"ridge\":578,\"a\":41,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":578,\"a\":51,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":578,\"a\":60,\"owners\":[90,97]},{\"tag\":\"mate\",\"ridge\":578,\"a\":61,\"owners\":[90,101]},{\"tag\":\"mate\",\"ridge\":578,\"a\":62,\"owners\":[90,97,101]},{\"tag\":\"mate\",\"ridge\":148,\"a\":16,\"owners\":[87,94,95,96,104]},{\"tag\":\"mate\",\"ridge\":148,\"a\":37,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":148,\"a\":64,\"owners\":[94,95,96]},{\"tag\":\"mate\",\"ridge\":148,\"a\":70,\"owners\":[87,95,96,104]},{\"tag\":\"mate\",\"ridge\":148,\"a\":71,\"owners\":[87,94,96,104]},{\"tag\":\"mate\",\"ridge\":280,\"a\":77,\"owners\":[88,99]},{\"tag\":\"mate\",\"ridge\":400,\"a\":22,\"owners\":[96,100,104,105]},{\"tag\":\"mate\",\"ridge\":400,\"a\":59,\"owners\":[104,105]},{\"tag\":\"mate\",\"ridge\":400,\"a\":72,\"owners\":[100,105]},{\"tag\":\"mate\",\"ridge\":400,\"a\":84,\"owners\":[96,100,104]},{\"tag\":\"mate\",\"ridge\":588,\"a\":67,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":588,\"a\":90,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":652,\"a\":69,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":652,\"a\":92,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":708,\"a\":73,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":708,\"a\":97,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":600,\"a\":76,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":664,\"a\":78,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":616,\"a\":80,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":616,\"a\":101,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":720,\"a\":82,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":848,\"a\":83,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-15,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-24,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":90,\"full_literals\":[-30,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":101,\"full_literals\":[-38,42]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[69,73],\"full_literals\":[-43,16,20]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":69,\"full_literals\":[-16,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-20,43]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[92,97],\"full_literals\":[-44,31,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":92,\"full_literals\":[-31,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":97,\"full_literals\":[-35,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":46,\"full_literals\":[-6,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":105,\"full_literals\":[-40,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-28,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":88,\"full_literals\":[-29,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":100,\"full_literals\":[-37,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":104,\"full_literals\":[-39,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":55,\"full_literals\":[-8,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":57,\"full_literals\":[-9,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":96,\"full_literals\":[-34,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":94,\"full_literals\":[-32,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":95,\"full_literals\":[-33,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":99,\"full_literals\":[-36,49]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,43,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-44,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-53,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":32,\"owners\":[16,22,37,46,55,57,59,64,70,71,72,77,78,82,84,87,94,95,96,100,104,105]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[8,41,51,60,61,62,67,73,76,80,82,83,90,97,101]}]}"
  "75 2 3 4 6 8 9 10 14 17 18 19 22 23 27 28 32 33 34 37 39 40 0 29 73 0\n76 1 5 7 11 12 13 15 20 24 30 35 38 0 25 29 30 74 0\n77 53 0 58 60 55 56 33 34 40 37 3 6 8 19 4 27 7 5 76 0\n78 51 41 0 29 25 30 31 32 2 28 1 20 55 56 40 37 5 3 6 8 76 0\n79 44 -51 0 39 40 54 21 23 35 0\n80 -44 52 0 57 36 37 22 24 38 0\n81 55 0 77 61 62 59 53 78 79 80 0\n82 -59 0 81 72 71 0\n83 -58 0 82 69 0\n84 -56 0 82 70 0\n85 -57 0 83 67 0\n86 -47 0 83 68 0\n87 -46 0 84 63 0\n88 -45 0 84 64 0\n89 -49 0 85 65 0\n90 -48 0 85 66 0\n91 -29 0 86 44 0\n92 -37 0 86 45 0\n93 -39 0 86 46 0\n94 -28 0 87 43 0\n95 -6 0 88 41 0\n96 -40 0 88 42 0\n97 -32 0 89 50 0\n98 -33 0 89 51 0\n99 -36 0 89 52 0\n100 -8 0 90 47 0\n101 -9 0 90 48 0\n102 -34 0 90 49 0\n103 -19 0 92 96 17 0\n104 -4 0 93 10 0\n105 -10 0 93 96 16 0\n106 -23 0 96 26 0\n107 -2 0 97 93 98 102 94 9 0\n108 -18 0 97 93 102 94 13 0\n109 -14 0 98 97 102 11 0\n110 -17 0 98 93 102 94 12 0\n111 -22 0 99 91 14 0\n112 -3 0 102 92 93 96 15 0\n113 -27 0 102 92 93 18 0\n114 0 109 112 107 104 95 101 105 100 110 108 103 111 106 113 94 97 98 102 92 93 96 75 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00008.record016
