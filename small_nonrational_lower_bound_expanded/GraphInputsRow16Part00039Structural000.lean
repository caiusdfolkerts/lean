module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00039Data
public import GraphInputsRow16Part00039Frames
public import GraphInputsRow16Part00039Leaves
public import GraphInputsRow16Part00039Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record003
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 496429499940864, (certNat% 5), 533381251072, 6442450944]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record003_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record004
def vertexColumn : Fields := ⟨10, (certNat% 6)⟩
def kindColumn : Fields := ⟨3, (certNat% 7)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 10), 16000093207396352, 4398046511104]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [18014006996369408, 4053239664633446400, (certNat% 11), (certNat% 12), 378493992960, (certNat% 10)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [18013654272180224, 4053239664633446400, (certNat% 11), (certNat% 13), 722628247552, (certNat% 10)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 4053239664767664128, (certNat% 11), 1972523860230144, (certNat% 15), 15793385021374464, 2156073582592]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record004_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record011
def vertexColumn : Fields := ⟨10, (certNat% 16)⟩
def kindColumn : Fields := ⟨3, (certNat% 17)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 20), 125069447659520, (certNat% 21), 6598680379392, 253403070464]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record011_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record013
def vertexColumn : Fields := ⟨10, (certNat% 22)⟩
def kindColumn : Fields := ⟨3, (certNat% 23)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨77, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), 8444524313444352, 132875550720, 272129127874560, 125829120]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record013_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ab25c6995633a2e4b8ae8785ecc6a996725a95a5c56555568d934cd8b52d2b61d175a354e334cccb8ad2b1ae1b16d8751cc789d2729e1725e0f43c2f07caa458562384e8a4a9855151560d2344d48ca344c5322c4b0ad0721c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b69369a69b6d24924d24934924d249a492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 40), (facetIndex 43), (facetIndex 46)]))
 (.leaf ([(facetIndex 25), (facetIndex 30), (facetIndex 47), (facetIndex 48), (facetIndex 55), (facetIndex 56), (facetIndex 57)])))
 (.branch 3
 (.leaf ([(facetIndex 26), (facetIndex 39), (facetIndex 41), (facetIndex 62)]))
 (.leaf ([(facetIndex 42), (facetIndex 66), (facetIndex 69)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 35), (facetIndex 64), (facetIndex 70)]))
 (.leaf ([(facetIndex 37), (facetIndex 45)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 49), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 27), (facetIndex 29), (facetIndex 31), (facetIndex 34), (facetIndex 36)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1180c40800093b6c312280d042f9c0e7ee88z12;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6, 7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record000" 21

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record000" "{\"ridges\":[[17,529],[30,529],[44,562],[48,532],[56,529],[57,529],[63,816],[65,538],[72,600]],\"owners\":[[17,529,[38,44,61,63],[30,48,56,57]],[30,529,[61,63],[17,38,44,48,56,57]],[56,529,[38,44,63],[17,30,48,57,61]],[57,529,[38,44,61],[17,30,48,56,63]],[48,532,[],[17,30,56,57,65,72]],[65,538,[38],[]],[44,562,[],[]],[72,600,[61],[]],[63,816,[],[]]],\"edges\":[[34,[17,30,38,44,48,56,57,61,63,65,72]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-5,-4],[-7,-3],[-7,-5],[-11,-4],[-13,-11],[-15,-7],[-1,5,6,11,12],[-2,11,12],[-9,5,6,12],[-10,5,6,11],[-8],[-14,5],[-6],[-16,11],[-12],[-17,3,13,15],[-18,4,7],[-19,17],[-19,18],[-20,19],[-21,20],[21],[1,2,5,6,8,9,10,11,12,14,16]],\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":45,\"b\":35},{\"tag\":\"incompatible\",\"a\":45,\"b\":38},{\"tag\":\"incompatible\",\"a\":61,\"b\":37},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":70,\"b\":45},{\"tag\":\"mate\",\"ridge\":529,\"a\":17,\"owners\":[38,44,61,63]},{\"tag\":\"mate\",\"ridge\":529,\"a\":30,\"owners\":[61,63]},{\"tag\":\"mate\",\"ridge\":529,\"a\":56,\"owners\":[38,44,63]},{\"tag\":\"mate\",\"ridge\":529,\"a\":57,\"owners\":[38,44,61]},{\"tag\":\"mate\",\"ridge\":532,\"a\":48,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":538,\"a\":65,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":562,\"a\":44,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":600,\"a\":72,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":816,\"a\":63,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[35,64,70],\"full_literals\":[-17,3,13,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[37,45],\"full_literals\":[-18,4,7]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-19,17,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-19,false,18],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-20,19,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-21,false,20],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[17,30,38,44,48,56,57,61,63,65,72]}]}"
  "24 20 0 22 21 0\n25 19 0 24 20 0\n26 17 0 25 18 0\n27 18 0 25 19 0\n28 1 2 5 9 10 11 14 16 0 13 11 15 23 0\n29 5 11 0 15 13 7 9 10 12 8 14 28 0\n30 -5 0 27 1 3 17 0\n31 11 0 30 29 0\n32 -4 0 31 4 0\n33 -13 0 31 5 0\n34 7 0 32 27 17 0\n35 -3 0 34 2 0\n36 -15 0 34 6 0\n37 0 36 35 26 33 16 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "332aaa5a699563392e2ba1e17b31aa659695553352d2b61d17723a8da3c4e5354e334ce8b92ccb4ac6b86c5b61d4731d2729e1725e0f43c2f07e2a2a9161588e13a292a5151548d1362348ca384d1314e0b22c4b0ad0721c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "34da4d34d36934d2492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 27), (facetIndex 31), (facetIndex 32), (facetIndex 36), (facetIndex 47), (facetIndex 58), (facetIndex 68)]))
 (.leaf ([(facetIndex 28), (facetIndex 40), (facetIndex 41), (facetIndex 44), (facetIndex 51), (facetIndex 61), (facetIndex 71)])))
 (.branch 3
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 53), (facetIndex 63)]))
 (.leaf ([(facetIndex 33), (facetIndex 42), (facetIndex 55), (facetIndex 65)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 35), (facetIndex 57), (facetIndex 67)]))
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 48), (facetIndex 49)])))
 (.branch 7
 (.leaf ([(facetIndex 34), (facetIndex 50), (facetIndex 52)]))
 (.branch 8
 (.leaf ([(facetIndex 43)]))
 (.leaf ([(facetIndex 37)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "10004030201000403026165505517311228046300441z1c;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 62)]))
 (.branch 2
 (.leaf ([(facetIndex 72)]))
 (.leaf ([(facetIndex 54), (facetIndex 60)]))))
 (.branch 4
 (.leaf ([(facetIndex 56), (facetIndex 59)]))
 (.branch 5
 (.leaf ([(facetIndex 64), (facetIndex 70)]))
 (.leaf ([(facetIndex 66), (facetIndex 69)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "112814400260308z28;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
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
def grouped3_0014 : List Nat := [1]
def grouped3_0015 : List Nat := [1, 2]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [3]
def grouped3_0018 : List Nat := [3, 4, 5]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record001" 45

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record001" "{\"ridges\":[[11,529],[11,530],[13,289],[32,529],[32,530],[34,289],[39,529],[41,289],[45,289],[46,529],[46,530],[48,529],[48,530],[49,529],[49,530],[50,289],[52,289],[54,540],[60,600],[64,540],[66,300],[69,420],[70,600],[72,816]],\"owners\":[[11,529,[54,60,62],[32,39,46,48,49]],[32,529,[60,62],[11,39,46,48,49,54]],[39,529,[62],[11,32,46,48,49,54,60]],[46,529,[54,60],[11,32,39,48,49,62]],[48,529,[54,62],[11,32,39,46,49,60]],[49,529,[54,60],[11,32,39,46,48,62]],[11,530,[64,70,72],[32,39,46,48,49]],[32,530,[70,72],[11,39,46,48,49,64]],[46,530,[64,70],[11,32,39,48,49,72]],[48,530,[64,72],[11,32,39,46,49,70]],[49,530,[64,70],[11,32,39,46,48,72]],[13,289,[56,59,62],[34,41,45,50,52]],[34,289,[62],[13,41,45,50,52,56,59]],[41,289,[59,62],[13,34,45,50,52,56]],[45,289,[56,59],[13,34,41,50,52,62]],[50,289,[56,62],[13,34,41,45,52,59]],[52,289,[56,59],[13,34,41,45,50,62]],[54,540,[64],[]],[64,540,[54],[]],[66,300,[56],[]],[69,420,[59],[]],[60,600,[70],[]],[70,600,[60],[]],[72,816,[62],[]]],\"edges\":[[34,[11,32,39,46,48,49,54,60,62,64,70,72]],[37,[13,34,41,45,50,52,56,59,62,66,69,72]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-5,-4],[-11,-8],[-13,-5],[-19,-9],[-19,-10],[-19,-12],[-19,-14],[-1,15,18,19],[-3,18,19],[-6,19],[-10,15,18],[-11,15,19],[-12,15,18],[-1,20,23,24],[-3,23,24],[-10,20,23],[-11,20,24],[-12,20,23],[-2,16,17,19],[-4,19],[-7,17,19],[-9,16,17],[-13,16,19],[-14,16,17],[-15,20],[-20,15],[-21,16],[-22,17],[-18,23],[-23,18],[-24,19],[-25,9,10,11,12],[-26,4,13,14],[-27,8],[-28,5],[-29,25],[-30,27,28],[-31,27],[-31,28],[-32,26,31],[-33,26],[-32,30],[-33,31],[-34,29,33],[-34,32],[-35,34],[35],[-19,36],[-24,37],[-15,38],[-18,38],[-16,39],[-17,39],[-20,40],[-23,40],[-38,41],[-37,41],[-41,42],[-36,42],[-40,43],[-39,-43,44],[-42,-44,45],[-45],[1,3,6,10,11,12,15,18,19,20,23,24],[2,4,7,9,13,14,16,17,19,21,22,24]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":37,\"b\":34},{\"tag\":\"incompatible\",\"a\":48,\"b\":43},{\"tag\":\"incompatible\",\"a\":50,\"b\":37},{\"tag\":\"incompatible\",\"a\":62,\"b\":45},{\"tag\":\"incompatible\",\"a\":62,\"b\":46},{\"tag\":\"incompatible\",\"a\":62,\"b\":49},{\"tag\":\"incompatible\",\"a\":62,\"b\":52},{\"tag\":\"mate\",\"ridge\":529,\"a\":11,\"owners\":[54,60,62]},{\"tag\":\"mate\",\"ridge\":529,\"a\":32,\"owners\":[60,62]},{\"tag\":\"mate\",\"ridge\":529,\"a\":39,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":529,\"a\":46,\"owners\":[54,60]},{\"tag\":\"mate\",\"ridge\":529,\"a\":48,\"owners\":[54,62]},{\"tag\":\"mate\",\"ridge\":529,\"a\":49,\"owners\":[54,60]},{\"tag\":\"mate\",\"ridge\":530,\"a\":11,\"owners\":[64,70,72]},{\"tag\":\"mate\",\"ridge\":530,\"a\":32,\"owners\":[70,72]},{\"tag\":\"mate\",\"ridge\":530,\"a\":46,\"owners\":[64,70]},{\"tag\":\"mate\",\"ridge\":530,\"a\":48,\"owners\":[64,72]},{\"tag\":\"mate\",\"ridge\":530,\"a\":49,\"owners\":[64,70]},{\"tag\":\"mate\",\"ridge\":289,\"a\":13,\"owners\":[56,59,62]},{\"tag\":\"mate\",\"ridge\":289,\"a\":34,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":289,\"a\":41,\"owners\":[59,62]},{\"tag\":\"mate\",\"ridge\":289,\"a\":45,\"owners\":[56,59]},{\"tag\":\"mate\",\"ridge\":289,\"a\":50,\"owners\":[56,62]},{\"tag\":\"mate\",\"ridge\":289,\"a\":52,\"owners\":[56,59]},{\"tag\":\"mate\",\"ridge\":540,\"a\":54,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":540,\"a\":64,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":300,\"a\":66,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":420,\"a\":69,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":600,\"a\":60,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":600,\"a\":70,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":816,\"a\":72,\"owners\":[62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[45,46,48,49],\"full_literals\":[-25,9,10,11,12]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[34,50,52],\"full_literals\":[-26,4,13,14]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[43],\"full_literals\":[-27,8]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[37],\"full_literals\":[-28,5]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-29,false,25],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-30,27,28],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-31,27,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-31,false,28],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-32,26,31],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-33,26,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-32,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-33,false,31],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-34,29,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-34,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-35,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":62,\"full_literals\":[-19,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":72,\"full_literals\":[-24,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":54,\"full_literals\":[-15,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":60,\"full_literals\":[-18,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":56,\"full_literals\":[-16,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":59,\"full_literals\":[-17,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":64,\"full_literals\":[-20,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-23,40]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-43,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-42,-44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[11,32,39,46,48,49,54,60,62,64,70,72]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[13,34,41,45,50,52,56,59,62,66,69,72]}]}"
  "66 34 0 47 46 0\n67 32 0 66 45 0\n68 30 0 67 42 0\n69 42 0 58 59 56 57 48 50 51 49 10 12 8 11 26 13 9 30 64 0\n70 -44 0 69 63 62 0\n71 39 19 0 31 20 52 53 22 24 27 19 23 28 21 65 0\n72 19 0 70 10 31 71 61 60 54 55 14 16 17 18 25 15 29 64 0\n73 -9 0 72 4 0\n74 -10 0 72 5 0\n75 -12 0 72 6 0\n76 -14 0 72 7 0\n77 26 0 67 66 73 75 74 40 41 38 44 34 36 2 32 0\n78 28 0 68 66 73 75 74 39 37 43 34 44 2 36 32 0\n79 5 0 78 35 0\n80 -4 0 79 1 0\n81 -13 0 79 3 0\n82 0 80 81 77 76 33 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ccaaa969a655a364d8ce8b8ae8785ecc6a9965a5556354d4cd8b4ad8745dc8ea368f1394d538cd33a2e4b32e2b2ae1b16d8751cc789c6785c970de0f43c2f07d26299161588e13925295151548d1362348ca384d1314e0b22c4b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b69349a69b69349a692492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 55), (facetIndex 63)]))
 (.branch 2
 (.leaf ([(facetIndex 57), (facetIndex 64)]))
 (.leaf ([(facetIndex 60), (facetIndex 65)]))))
 (.branch 4
 (.leaf ([(facetIndex 67), (facetIndex 75)]))
 (.branch 5
 (.leaf ([(facetIndex 69), (facetIndex 76)]))
 (.leaf ([(facetIndex 72), (facetIndex 77)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2c605020611002008z2a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4, 5]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record002" 39

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record002" "{\"ridges\":[[8,521],[8,522],[11,530],[14,546],[30,521],[30,522],[33,530],[35,546],[40,522],[40,529],[40,530],[42,521],[42,522],[42,546],[44,521],[44,522],[45,521],[45,522],[47,530],[47,546],[49,530],[50,530],[52,546],[53,546],[55,540],[57,556],[60,564],[63,600],[64,680],[65,816],[67,540],[69,556],[75,600],[76,680]],\"owners\":[[8,521,[55,57,63,64],[30,40,42,44,45]],[30,521,[63,64],[8,40,42,44,45,55,57]],[42,521,[55,63],[8,30,40,44,45,57,64]],[44,521,[55,57,64],[8,30,40,42,45,63]],[45,521,[55,57,63],[8,30,40,42,44,64]],[8,522,[67,69,75,76],[30,40,42,44,45]],[30,522,[75,76],[8,40,42,44,45,67,69]],[40,522,[69,76],[8,30,42,44,45,67,75]],[42,522,[67,75],[8,30,40,44,45,69,76]],[44,522,[67,69,76],[8,30,40,42,45,75]],[45,522,[67,69,75],[8,30,40,42,44,76]],[40,529,[60,65],[11,33,47,49,50,55,63]],[11,530,[67,72,75,77],[33,40,47,49,50]],[33,530,[75,77],[11,40,47,49,50,67,72]],[40,530,[72,77],[11,33,47,49,50,67,75]],[47,530,[67,75],[11,33,40,49,50,72,77]],[49,530,[67,72,77],[11,33,40,47,50,75]],[50,530,[67,72,75],[11,33,40,47,49,77]],[14,546,[69,72,76,77],[35,42,47,52,53]],[35,546,[76,77],[14,42,47,52,53,69,72]],[42,546,[72,77],[14,35,47,52,53,69,76]],[47,546,[69,76],[14,35,42,52,53,72,77]],[52,546,[69,72,77],[14,35,42,47,53,76]],[53,546,[69,72,76],[14,35,42,47,52,77]],[55,540,[67],[]],[67,540,[55],[]],[57,556,[69],[]],[69,556,[57],[]],[60,564,[72],[]],[63,600,[75],[]],[75,600,[63],[]],[64,680,[76],[]],[76,680,[64],[]],[65,816,[77],[]]],\"edges\":[[29,[8,30,40,42,44,45,55,57,63,64,67,69,75,76]],[34,[11,33,40,47,49,50,55,60,63,65,67,72,75,77]],[38,[14,35,42,47,52,53,57,60,64,65,69,72,76,77]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,16,17,19,20],[-4,19,20],[-8,16,19],[-9,16,17,20],[-10,16,17,19],[-1,22,23,25,26],[-4,25,26],[-7,23,26],[-8,22,25],[-9,22,23,26],[-10,22,23,25],[-7,18,21],[-2,22,24,25,27],[-5,25,27],[-7,24,27],[-11,22,25],[-12,22,24,27],[-13,22,24,25],[-3,23,24,26,27],[-6,26,27],[-8,24,27],[-11,23,26],[-14,23,24,27],[-15,23,24,26],[-16,22],[-22,16],[-17,23],[-23,17],[-18,24],[-19,25],[-25,19],[-20,26],[-26,20],[-21,27],[-16,28],[-19,28],[-17,29],[-20,29],[-18,30],[-21,30],[-22,31],[-25,31],[-23,32],[-26,32],[-24,33],[-27,33],[-30,34],[-29,34],[-34,35],[-28,35],[-33,36],[-32,36],[-32,-33,37],[-37,38],[-31,-36,38],[-35,-38,39],[-39],[1,4,7,8,9,10,16,17,19,20,22,23,25,26],[2,5,7,11,12,13,16,18,19,21,22,24,25,27],[3,6,8,11,14,15,17,18,20,21,23,24,26,27]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":521,\"a\":8,\"owners\":[55,57,63,64]},{\"tag\":\"mate\",\"ridge\":521,\"a\":30,\"owners\":[63,64]},{\"tag\":\"mate\",\"ridge\":521,\"a\":42,\"owners\":[55,63]},{\"tag\":\"mate\",\"ridge\":521,\"a\":44,\"owners\":[55,57,64]},{\"tag\":\"mate\",\"ridge\":521,\"a\":45,\"owners\":[55,57,63]},{\"tag\":\"mate\",\"ridge\":522,\"a\":8,\"owners\":[67,69,75,76]},{\"tag\":\"mate\",\"ridge\":522,\"a\":30,\"owners\":[75,76]},{\"tag\":\"mate\",\"ridge\":522,\"a\":40,\"owners\":[69,76]},{\"tag\":\"mate\",\"ridge\":522,\"a\":42,\"owners\":[67,75]},{\"tag\":\"mate\",\"ridge\":522,\"a\":44,\"owners\":[67,69,76]},{\"tag\":\"mate\",\"ridge\":522,\"a\":45,\"owners\":[67,69,75]},{\"tag\":\"mate\",\"ridge\":529,\"a\":40,\"owners\":[60,65]},{\"tag\":\"mate\",\"ridge\":530,\"a\":11,\"owners\":[67,72,75,77]},{\"tag\":\"mate\",\"ridge\":530,\"a\":33,\"owners\":[75,77]},{\"tag\":\"mate\",\"ridge\":530,\"a\":40,\"owners\":[72,77]},{\"tag\":\"mate\",\"ridge\":530,\"a\":47,\"owners\":[67,75]},{\"tag\":\"mate\",\"ridge\":530,\"a\":49,\"owners\":[67,72,77]},{\"tag\":\"mate\",\"ridge\":530,\"a\":50,\"owners\":[67,72,75]},{\"tag\":\"mate\",\"ridge\":546,\"a\":14,\"owners\":[69,72,76,77]},{\"tag\":\"mate\",\"ridge\":546,\"a\":35,\"owners\":[76,77]},{\"tag\":\"mate\",\"ridge\":546,\"a\":42,\"owners\":[72,77]},{\"tag\":\"mate\",\"ridge\":546,\"a\":47,\"owners\":[69,76]},{\"tag\":\"mate\",\"ridge\":546,\"a\":52,\"owners\":[69,72,77]},{\"tag\":\"mate\",\"ridge\":546,\"a\":53,\"owners\":[69,72,76]},{\"tag\":\"mate\",\"ridge\":540,\"a\":55,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":540,\"a\":67,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":556,\"a\":57,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":556,\"a\":69,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":564,\"a\":60,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":600,\"a\":63,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":600,\"a\":75,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":680,\"a\":64,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":680,\"a\":76,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":816,\"a\":65,\"owners\":[77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":55,\"full_literals\":[-16,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-19,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":57,\"full_literals\":[-17,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":64,\"full_literals\":[-20,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":60,\"full_literals\":[-18,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-21,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-22,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":75,\"full_literals\":[-25,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":69,\"full_literals\":[-23,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-26,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":72,\"full_literals\":[-24,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":77,\"full_literals\":[-27,33]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-33,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-37,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-36,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-35,-38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[8,30,40,42,44,45,55,57,63,64,67,69,75,76]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[11,33,40,47,49,50,55,60,63,65,67,72,75,77]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[14,35,42,47,52,53,57,60,64,65,69,72,76,77]}]}"
  "61 35 0 49 50 47 48 35 36 39 40 37 38 1 3 4 5 26 2 31 12 28 33 58 0\n62 -38 0 61 57 56 0\n63 -37 0 62 54 0\n64 32 31 0 42 30 41 25 9 43 44 8 27 6 10 11 32 7 58 0\n65 31 0 63 41 42 16 25 30 64 53 45 46 15 29 13 17 18 34 14 59 0\n66 -36 0 65 62 55 0\n67 -33 0 66 51 0\n68 -32 0 66 52 0\n69 -24 0 67 45 0\n70 -27 0 67 46 0\n71 -23 0 68 43 0\n72 -26 0 68 44 0\n73 -8 0 69 70 21 0\n74 -18 0 69 29 0\n75 -21 0 70 34 0\n76 -11 0 71 72 22 0\n77 -17 0 71 27 0\n78 -3 0 71 69 72 70 19 0\n79 -14 0 71 69 70 23 0\n80 -15 0 71 69 72 24 0\n81 -20 0 72 32 0\n82 -6 0 72 70 20 0\n83 0 78 79 82 73 76 80 77 74 81 75 71 69 72 70 60 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record002
