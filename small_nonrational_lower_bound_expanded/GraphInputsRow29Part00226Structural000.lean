module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00226Data
public import GraphInputsRow29Part00226Frames
public import GraphInputsRow29Part00226Leaves
public import GraphInputsRow29Part00226Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨50, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨77, by decide⟩, ⟨85, by decide⟩, ⟨92, by decide⟩, ⟨95, by decide⟩, ⟨102, by decide⟩, ⟨105, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨122, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 137422176256, 35046933135360, (certNat% 4)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001
def vertexColumn : Fields := ⟨10, (certNat% 5)⟩
def kindColumn : Fields := ⟨3, (certNat% 6)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩, ⟨110, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), 35888059530608640, (certNat% 10), 140187732541440]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002
def vertexColumn : Fields := ⟨10, (certNat% 11)⟩
def kindColumn : Fields := ⟨3, (certNat% 12)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩, ⟨95, by decide⟩, ⟨98, by decide⟩, ⟨105, by decide⟩, ⟨108, by decide⟩, ⟨115, by decide⟩, ⟨118, by decide⟩, ⟨125, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 15), 140187732541440, 1148417904979476480, (certNat% 16)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004
def vertexColumn : Fields := ⟨10, (certNat% 17)⟩
def kindColumn : Fields := ⟨3, (certNat% 18)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨84, by decide⟩, ⟨89, by decide⟩, ⟨96, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), 137640280064, 51539607552]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), 287762808832, 51539607552]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 22), 8724152320, 21751660544, 35517366272, 412316860416]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), 176160768, 21474836480]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), 8757706752, (certNat% 28), (certNat% 29), 4611703610613432320]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), 8757706752, (certNat% 27), (certNat% 32), (certNat% 33)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), (certNat% 36), (certNat% 27)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3802297500958720, (certNat% 37), (certNat% 38), 292057776128, 6917546619827126272, (certNat% 39)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 31), (certNat% 39), 2306124484190404608, (certNat% 20)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), (certNat% 43), (certNat% 27)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8070609168473522176, (certNat% 44), (certNat% 38), 171798691840, 3379898743783424, (certNat% 45)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2393015618371584, 19791242854400, (certNat% 27), (certNat% 38), (certNat% 43), (certNat% 32)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 38), 463856467968, 19791242854400, 27262976, 4294967296]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4612108709208784896, 19791242854400, (certNat% 27), (certNat% 36), (certNat% 38), (certNat% 47)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [422690754134016, (certNat% 27), 60817408, (certNat% 48), (certNat% 47), (certNat% 49), (certNat% 50)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c21 c16
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c22 c15
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c23 c12
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c24 c11
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c25 c8
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c26 c7
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c27 c4
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009
def vertexColumn : Fields := ⟨10, (certNat% 51)⟩
def kindColumn : Fields := ⟨3, (certNat% 52)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 54), (certNat% 55), 4415431901184]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), 4415431901184, (certNat% 58), (certNat% 59), (certNat% 60)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 62), 4616189618054758400, (certNat% 63), 4449791639552, 36310271995674624]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), (certNat% 65), (certNat% 66), 4415431901184, 1407374883553280]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 68), (certNat% 69), 4415427706880, (certNat% 70)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), (certNat% 66), 577586652210266112, 4415431901184, 36310271995674624]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), (certNat% 73), (certNat% 74), (certNat% 58), 4415431901184, 1407374883553280]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), (certNat% 58), (certNat% 63), 4449791639552, 22517998136852480, (certNat% 76)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 78), 4415293489152, (certNat% 79)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 80), (certNat% 81), (certNat% 79), (certNat% 82), 4503602311725056, (certNat% 83)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 84), (certNat% 65), 19140298416324608, (certNat% 79), 4449791639552, (certNat% 85)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 86), (certNat% 57), 595601050719748096, (certNat% 87), 4449791639552, 40532396646334464]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 88), (certNat% 82), (certNat% 89), (certNat% 73), (certNat% 90)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 91), (certNat% 82), (certNat% 92), (certNat% 73), (certNat% 93)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 94), 19140298416324608, (certNat% 73), (certNat% 93), (certNat% 95), 4415427706880]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 96), (certNat% 93), (certNat% 65), 4449791639552, 595601050719748096, 40532396646334464]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), (certNat% 98), (certNat% 82), (certNat% 92), (certNat% 99), 635007547459239936]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 100), (certNat% 79), (certNat% 101), (certNat% 65), 4449791639552, 595601050719748096, 40532396646334464]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c26 c21
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c27 c16
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c28 c15
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c29 c14
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c30 c11
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c31 c10
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c32 c3
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c33 c2
  c34
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "dc2f07c368ba1e8d9354d332c9b16cc72e2b4ab29c8f2aaa9a99a5635a2e4ba1e4789e785d16c6715c4f1725a99a5693a59999565954d59354d3362d4b46d8751d2766338e5334e334ccb31ce2b4ae1b46c9b91cc789d2719e1745c9715e0f43c8f0bc1f951548a8aa85a0e584e1544d14a4a9515151550d28c9322c2b05c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db69b6db6db4da69a6d26d269a4da49a6d369b4d369a4da6db692492489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 49), (facetIndex 62), (facetIndex 82), (facetIndex 89)]))
 (.leaf ([(facetIndex 51), (facetIndex 74), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 52), (facetIndex 55), (facetIndex 57), (facetIndex 67), (facetIndex 93), (facetIndex 97)]))
 (.branch 4
 (.leaf ([(facetIndex 65), (facetIndex 90), (facetIndex 96), (facetIndex 98)]))
 (.leaf ([(facetIndex 31), (facetIndex 34), (facetIndex 35), (facetIndex 41), (facetIndex 87)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 46), (facetIndex 79), (facetIndex 81), (facetIndex 84), (facetIndex 88)]))
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 71), (facetIndex 85), (facetIndex 86), (facetIndex 101)]))
 (.leaf ([(facetIndex 70), (facetIndex 99), (facetIndex 100)]))))
 (.branch 9
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 91), (facetIndex 92)]))
 (.branch 10
 (.leaf ([(facetIndex 54), (facetIndex 77), (facetIndex 95)]))
 (.leaf ([(facetIndex 48), (facetIndex 61)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "6773239028830546650050509011006700203000a000202902100a05066040000044884z1f;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record003" 110

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record003" "{\"ridges\":[[3,131],[4,146],[5,161],[10,161],[11,296],[12,145],[12,208],[14,161],[14,224],[15,352],[17,532],[18,162],[19,546],[19,552],[21,592],[24,131],[28,146],[30,530],[36,146],[40,546],[40,552],[42,146],[43,306],[44,561],[45,146],[45,208],[47,224],[48,579],[53,296],[55,204],[58,145],[58,208],[59,592],[60,352],[62,408],[63,224],[64,296],[65,608],[68,208],[69,352],[70,561],[71,161],[71,432],[72,208],[73,224],[76,530],[78,546],[78,552],[79,198],[80,592],[81,102],[81,608],[82,664],[83,162],[83,546],[83,552],[84,114],[85,114],[85,608],[86,688],[87,706],[88,608],[88,706],[89,792],[91,108],[94,592],[97,712],[98,608],[98,840],[99,224],[99,432],[100,608],[100,688],[101,816]],\"owners\":[[3,131,[4,5,28,34,45,47],[24]],[24,131,[4,5,45,47],[3,28,34]],[12,145,[4,28,36,42,49,62,71],[58,68,72]],[58,145,[4,36,42,62,71],[12,28,49,68,72]],[4,146,[74,79,82,84,86,87],[28,36,42,45]],[28,146,[82,84,86,87],[4,36,42,45,74,79]],[36,146,[79,84,86,87],[4,28,42,45,74,82]],[42,146,[74,79,82,87],[4,28,36,45,84,86]],[45,146,[74,82,86],[4,28,36,42,79,84,87]],[18,162,[5,42,47,84,86,88],[83]],[83,162,[5,42,47,84],[18,86,88]],[11,296,[77,90,92,96,98],[39,53,64,66]],[53,296,[96,98],[11,39,64,66,77,90,92]],[64,296,[77,92],[11,39,53,66,90,96,98]],[12,208,[79,84,87,99,100],[45,58,68,72]],[45,208,[99,100],[12,58,68,72,79,84,87]],[58,208,[84,87,99,100],[12,45,68,72,79]],[68,208,[79,87],[12,45,58,72,84,99,100]],[72,208,[79,84,87,100],[12,45,58,68,99]],[14,224,[84,88,96,97,99,100],[47,63,68,73]],[47,224,[96,97,99,100],[14,63,68,73,84,88]],[63,224,[84,88,99,100],[14,47,68,73,96,97]],[73,224,[84,88,97,100],[14,47,63,68,96,99]],[99,224,[14,47,63,88,97],[68,73,84,96,100]],[15,352,[90,95,96,98,99,101],[60,64,69,73]],[60,352,[96,98,99,101],[15,64,69,73,90,95]],[69,352,[90,95,96,98],[15,60,64,73,99,101]],[30,530,[82,85,86,87],[17,38,44,46,76,80]],[76,530,[44,46,85,86,87],[17,30,38,80,82]],[17,532,[21,51,59,89,94],[30,76]],[19,546,[33,44,48,81,85,86,88],[40,78,83]],[40,546,[81,85,86,88],[19,33,44,48,78,83]],[78,546,[44,48,85,86,88],[19,33,40,81,83]],[83,546,[33,44,48,81,85],[19,40,78,86,88]],[19,552,[54,65,91,92,97,98],[40,78,83]],[40,552,[91,92,97,98],[19,54,65,78,83]],[78,552,[65,97,98],[19,40,54,83,91,92]],[83,552,[54,65,91,92,98],[19,40,78,97]],[21,592,[46,70,85,87,100,101],[59,80,94]],[59,592,[85,87,100,101],[21,46,70,80,94]],[80,592,[70,100,101],[21,46,59,85,87,94]],[94,592,[46,70,85,87,100],[21,59,80,101]],[81,102,[31],[]],[79,198,[34],[]],[48,579,[35,46],[]],[84,114,[41,85],[]],[85,114,[41,84],[]],[43,306,[],[]],[44,561,[70],[]],[70,561,[44],[]],[65,608,[81,85,88,95,100,101],[48,61,70,91,97,98]],[81,608,[65,70,97,98,100,101],[48,61,85,88,91,95]],[85,608,[61,65,91,95,97,98],[48,70,81,88,100,101]],[88,608,[61,65,70,91,95,98,101],[48,81,85,97,100]],[98,608,[48,61,70,81,85,88,100],[65,91,95,97,101]],[100,608,[48,61,65,81,91,95,98],[70,85,88,97,101]],[91,108,[52,90],[]],[55,204,[],[]],[62,408,[],[]],[71,432,[99],[]],[99,432,[71],[]],[82,664,[],[]],[86,688,[100],[]],[100,688,[86],[]],[87,706,[88],[]],[88,706,[87],[]],[89,792,[],[]],[98,840,[93],[]],[97,712,[],[]],[101,816,[],[]]],\"edges\":[[27,[3,10,18,24,36,49,55,62,63,66,67,74,82,83,96,97]],[32,[4,12,28,36,42,45,49,58,62,68,71,72,74,79,82,84,86,87,99,100]],[34,[17,21,30,38,44,46,51,59,70,76,80,82,85,86,87,89,94,100,101]],[37,[11,15,32,39,43,53,60,64,66,69,71,73,77,90,92,95,96,98,99,101]],[38,[19,33,40,44,48,54,61,65,70,78,81,83,85,86,88,91,92,95,97,98,100,101]],[39,[12,14,34,45,47,55,58,63,67,68,72,73,79,84,87,88,96,97,99,100]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-46,-23],[-47,-46],[-52,-31],[-52,-44],[-52,-47],[-54,-46],[-70,-46],[-76,-46],[-1,2,3,14,19,29,31],[-13,2,3,29,31],[-6,2,14,21,26,33,43,52],[-39,2,21,26,43,52],[-2,55,59,62,64,66,67],[-14,62,64,66,67],[-21,59,64,66,67],[-26,55,59,62,67],[-29,55,62,66],[-3,-7,-52],[-4,-7,-52],[-10,3,26,31,64,66,68],[-63,3,26,31,64],[-5,57,70,72,76,78],[-36,76,78],[-45,57,72],[-6,59,64,67,79,80],[-29,79,80],[-39,64,67,79,80],[-49,59,67],[-53,59,64,67,80],[-7,64,68,76,77,79,80],[-31,76,77,79,80],[-44,64,68,79,80],[-54,64,68,77,80],[-79,7,31,44,68,77],[-8,70,75,76,78,79,81],[-41,76,78,79,81],[-50,70,75,76,78],[-15,62,65,66,67],[-56,28,30,65,66,67],[-9,12,34,40,69,74],[-11,18,28,32,61,65,66,68],[-24,61,65,66,68],[-58,28,32,65,66,68],[-63,18,28,32,61,65],[-11,37,46,71,72,77,78],[-24,71,72,77,78],[-58,46,77,78],[-63,37,46,71,72,78],[-12,30,51,65,67,80,81],[-40,65,67,80,81],[-60,51,80,81],[-74,30,51,65,67,80],[-61,16],[-59,19],[-32,20,30],[-64,25,65],[-65,25,64],[-27],[-28,51],[-51,28],[-46,61,65,68,75,80,81],[-61,46,51,77,78,80,81],[-65,42,46,71,75,77,78],[-68,42,46,51,71,75,78,81],[-78,32,42,51,61,65,68,80],[-80,32,42,46,61,71,75,78],[-71,35,70],[-38],[-43],[-52,79],[-79,52],[-62],[-66,80],[-80,66],[-67,68],[-68,67],[-69],[-78,73],[-77],[-81],[-22,82],[-33,82],[-34,83],[-55,83],[-35,84],[-48,84],[-73,84],[-46,85],[-70,85],[-76,85],[-78,85],[-16,86],[-19,86],[-20,86],[-25,86],[-67,86],[-30,87],[-61,87],[-64,87],[-68,87],[-88,27,28,52,65,66,81],[-28,88],[-52,88],[-65,88],[-66,88],[-89,51,79,80],[-51,89],[-79,89],[-80,89],[-17,90],[-18,90],[-71,90],[-72,90],[-37,91],[-57,91],[-75,91],[-32,92],[-42,92],[-83,93],[-82,93],[-86,94],[-85,94],[-85,-86,95],[-94,96],[-95,97],[-84,96],[-84,-94,97],[-96,98],[-97,99],[-93,98],[-93,-96,99],[-100,88,89],[-89,100],[-88,100],[-88,-89,101],[-102,87,100],[-100,102],[-101,103],[-87,102],[-87,-100,103],[-87,-101,104],[-92,105],[-91,105],[-105,106],[-90,106],[-106,107],[-102,107],[-102,-106,108],[-103,108],[-103,-106,109],[-104,109],[-109,110],[-98,-108,110],[-99,-107,110],[-110],[1,4,10,13,21,33,38,43,44,47,48,55,62,63,76,77],[2,6,14,21,26,29,33,39,43,49,52,53,55,59,62,64,66,67,79,80],[9,12,15,22,28,30,34,40,51,56,60,62,65,66,67,69,74,80,81],[5,8,17,23,27,36,41,45,47,50,52,54,57,70,72,75,76,78,79,81],[11,18,24,28,32,37,42,46,51,58,61,63,65,66,68,71,72,75,77,78,80,81],[6,7,19,29,31,38,39,44,48,49,53,54,59,64,67,68,76,77,79,80]],\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":65,\"b\":39},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":71,\"b\":47},{\"tag\":\"incompatible\",\"a\":71,\"b\":63},{\"tag\":\"incompatible\",\"a\":71,\"b\":66},{\"tag\":\"incompatible\",\"a\":73,\"b\":65},{\"tag\":\"incompatible\",\"a\":90,\"b\":65},{\"tag\":\"incompatible\",\"a\":96,\"b\":65},{\"tag\":\"mate\",\"ridge\":131,\"a\":3,\"owners\":[4,5,28,34,45,47]},{\"tag\":\"mate\",\"ridge\":131,\"a\":24,\"owners\":[4,5,45,47]},{\"tag\":\"mate\",\"ridge\":145,\"a\":12,\"owners\":[4,28,36,42,49,62,71]},{\"tag\":\"mate\",\"ridge\":145,\"a\":58,\"owners\":[4,36,42,62,71]},{\"tag\":\"mate\",\"ridge\":146,\"a\":4,\"owners\":[74,79,82,84,86,87]},{\"tag\":\"mate\",\"ridge\":146,\"a\":28,\"owners\":[82,84,86,87]},{\"tag\":\"mate\",\"ridge\":146,\"a\":36,\"owners\":[79,84,86,87]},{\"tag\":\"mate\",\"ridge\":146,\"a\":42,\"owners\":[74,79,82,87]},{\"tag\":\"mate\",\"ridge\":146,\"a\":45,\"owners\":[74,82,86]},{\"tag\":\"three\",\"ridge\":161,\"vertices\":[5,14,71]},{\"tag\":\"three\",\"ridge\":161,\"vertices\":[10,14,71]},{\"tag\":\"mate\",\"ridge\":162,\"a\":18,\"owners\":[5,42,47,84,86,88]},{\"tag\":\"mate\",\"ridge\":162,\"a\":83,\"owners\":[5,42,47,84]},{\"tag\":\"mate\",\"ridge\":296,\"a\":11,\"owners\":[77,90,92,96,98]},{\"tag\":\"mate\",\"ridge\":296,\"a\":53,\"owners\":[96,98]},{\"tag\":\"mate\",\"ridge\":296,\"a\":64,\"owners\":[77,92]},{\"tag\":\"mate\",\"ridge\":208,\"a\":12,\"owners\":[79,84,87,99,100]},{\"tag\":\"mate\",\"ridge\":208,\"a\":45,\"owners\":[99,100]},{\"tag\":\"mate\",\"ridge\":208,\"a\":58,\"owners\":[84,87,99,100]},{\"tag\":\"mate\",\"ridge\":208,\"a\":68,\"owners\":[79,87]},{\"tag\":\"mate\",\"ridge\":208,\"a\":72,\"owners\":[79,84,87,100]},{\"tag\":\"mate\",\"ridge\":224,\"a\":14,\"owners\":[84,88,96,97,99,100]},{\"tag\":\"mate\",\"ridge\":224,\"a\":47,\"owners\":[96,97,99,100]},{\"tag\":\"mate\",\"ridge\":224,\"a\":63,\"owners\":[84,88,99,100]},{\"tag\":\"mate\",\"ridge\":224,\"a\":73,\"owners\":[84,88,97,100]},{\"tag\":\"mate\",\"ridge\":224,\"a\":99,\"owners\":[14,47,63,88,97]},{\"tag\":\"mate\",\"ridge\":352,\"a\":15,\"owners\":[90,95,96,98,99,101]},{\"tag\":\"mate\",\"ridge\":352,\"a\":60,\"owners\":[96,98,99,101]},{\"tag\":\"mate\",\"ridge\":352,\"a\":69,\"owners\":[90,95,96,98]},{\"tag\":\"mate\",\"ridge\":530,\"a\":30,\"owners\":[82,85,86,87]},{\"tag\":\"mate\",\"ridge\":530,\"a\":76,\"owners\":[44,46,85,86,87]},{\"tag\":\"mate\",\"ridge\":532,\"a\":17,\"owners\":[21,51,59,89,94]},{\"tag\":\"mate\",\"ridge\":546,\"a\":19,\"owners\":[33,44,48,81,85,86,88]},{\"tag\":\"mate\",\"ridge\":546,\"a\":40,\"owners\":[81,85,86,88]},{\"tag\":\"mate\",\"ridge\":546,\"a\":78,\"owners\":[44,48,85,86,88]},{\"tag\":\"mate\",\"ridge\":546,\"a\":83,\"owners\":[33,44,48,81,85]},{\"tag\":\"mate\",\"ridge\":552,\"a\":19,\"owners\":[54,65,91,92,97,98]},{\"tag\":\"mate\",\"ridge\":552,\"a\":40,\"owners\":[91,92,97,98]},{\"tag\":\"mate\",\"ridge\":552,\"a\":78,\"owners\":[65,97,98]},{\"tag\":\"mate\",\"ridge\":552,\"a\":83,\"owners\":[54,65,91,92,98]},{\"tag\":\"mate\",\"ridge\":592,\"a\":21,\"owners\":[46,70,85,87,100,101]},{\"tag\":\"mate\",\"ridge\":592,\"a\":59,\"owners\":[85,87,100,101]},{\"tag\":\"mate\",\"ridge\":592,\"a\":80,\"owners\":[70,100,101]},{\"tag\":\"mate\",\"ridge\":592,\"a\":94,\"owners\":[46,70,85,87,100]},{\"tag\":\"mate\",\"ridge\":102,\"a\":81,\"owners\":[31]},{\"tag\":\"mate\",\"ridge\":198,\"a\":79,\"owners\":[34]},{\"tag\":\"mate\",\"ridge\":579,\"a\":48,\"owners\":[35,46]},{\"tag\":\"mate\",\"ridge\":114,\"a\":84,\"owners\":[41,85]},{\"tag\":\"mate\",\"ridge\":114,\"a\":85,\"owners\":[41,84]},{\"tag\":\"mate\",\"ridge\":306,\"a\":43,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":561,\"a\":44,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":561,\"a\":70,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":608,\"a\":65,\"owners\":[81,85,88,95,100,101]},{\"tag\":\"mate\",\"ridge\":608,\"a\":81,\"owners\":[65,70,97,98,100,101]},{\"tag\":\"mate\",\"ridge\":608,\"a\":85,\"owners\":[61,65,91,95,97,98]},{\"tag\":\"mate\",\"ridge\":608,\"a\":88,\"owners\":[61,65,70,91,95,98,101]},{\"tag\":\"mate\",\"ridge\":608,\"a\":98,\"owners\":[48,61,70,81,85,88,100]},{\"tag\":\"mate\",\"ridge\":608,\"a\":100,\"owners\":[48,61,65,81,91,95,98]},{\"tag\":\"mate\",\"ridge\":108,\"a\":91,\"owners\":[52,90]},{\"tag\":\"mate\",\"ridge\":204,\"a\":55,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":408,\"a\":62,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":432,\"a\":71,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":432,\"a\":99,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":664,\"a\":82,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":688,\"a\":86,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":688,\"a\":100,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":706,\"a\":87,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":706,\"a\":88,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":792,\"a\":89,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":840,\"a\":98,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":712,\"a\":97,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":816,\"a\":101,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":38,\"full_literals\":[-22,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-33,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":51,\"full_literals\":[-34,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":74,\"full_literals\":[-55,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":52,\"full_literals\":[-35,84]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-48,84]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":93,\"full_literals\":[-73,84]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":65,\"full_literals\":[-46,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":90,\"full_literals\":[-70,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":96,\"full_literals\":[-76,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":98,\"full_literals\":[-78,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":31,\"full_literals\":[-16,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":34,\"full_literals\":[-19,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":35,\"full_literals\":[-20,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":41,\"full_literals\":[-25,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":87,\"full_literals\":[-67,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":46,\"full_literals\":[-30,87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-61,87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-64,87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":88,\"full_literals\":[-68,87]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[43,44,71,85,86,101],\"full_literals\":[-88,27,28,52,65,66,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":44,\"full_literals\":[-28,88]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":71,\"full_literals\":[-52,88]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":85,\"full_literals\":[-65,88]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-66,88]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[70,99,100],\"full_literals\":[-89,51,79,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":70,\"full_literals\":[-51,89]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":99,\"full_literals\":[-79,89]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":100,\"full_literals\":[-80,89]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":32,\"full_literals\":[-17,90]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":33,\"full_literals\":[-18,90]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":91,\"full_literals\":[-71,90]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":92,\"full_literals\":[-72,90]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":54,\"full_literals\":[-37,91]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":77,\"full_literals\":[-57,91]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":95,\"full_literals\":[-75,91]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":48,\"full_literals\":[-32,92]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":61,\"full_literals\":[-42,92]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-86,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-85,-86,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-94,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-95,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-84,false,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-84,-94,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-96,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-97,99],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-93,false,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-93,-96,99],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-100,88,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-89,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-88,false,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-88,-89,101],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-102,87,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-100,102],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-101,103],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-87,false,102],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-87,-100,103],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-87,-101,104],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-92,105],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-91,false,105],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-105,106],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-90,false,106],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-106,107],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-102,false,107],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-102,-106,108],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-103,false,108],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-103,-106,109],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-104,false,109],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-109,110],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-98,-108,110],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-99,-107,110],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":27,\"owners\":[3,10,18,24,36,49,55,62,63,66,67,74,82,83,96,97]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[4,12,28,36,42,45,49,58,62,68,71,72,74,79,82,84,86,87,99,100]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[17,21,30,38,44,46,51,59,70,76,80,82,85,86,87,89,94,100,101]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[11,15,32,39,43,53,60,64,66,69,71,73,77,90,92,95,96,98,99,101]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[19,33,40,44,48,54,61,65,70,78,81,83,85,86,88,91,92,95,97,98,100,101]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[12,14,34,45,47,55,58,63,67,68,72,73,79,84,87,88,96,97,99,100]}]}"
  "162 -88 28 52 65 66 0 58 80 101 0\n163 -109 0 155 152 0\n164 -104 0 163 151 0\n165 1 4 10 13 21 33 44 47 48 55 63 76 0 68 69 72 79 156 0\n166 2 6 14 21 26 29 33 39 49 52 53 55 59 64 66 67 79 80 0 69 72 157 0\n167 9 12 15 22 28 30 34 40 51 56 60 65 66 67 74 80 0 72 77 80 158 0\n168 5 8 17 23 36 41 45 47 50 52 54 57 70 72 75 76 78 79 0 58 80 159 0\n169 11 18 24 28 32 37 42 46 51 58 61 63 65 66 68 71 72 75 78 80 0 79 80 160 0\n170 6 7 19 29 31 39 44 48 49 53 54 59 64 67 68 76 79 80 0 68 79 161 0\n171 102 96 0 79 124 121 93 54 96 28 76 122 90 126 86 137 139 133 99 108 109 27 30 32 33 25 29 26 31 170 0\n172 100 98 0 72 130 119 84 128 124 121 93 54 96 16 28 95 120 82 133 134 108 109 103 104 105 26 56 15 27 14 25 29 13 166 0\n173 -65 98 0 163 79 172 128 126 85 124 122 89 67 91 88 121 95 57 99 140 150 144 142 143 118 116 63 0\n174 52 66 98 0 72 69 128 124 121 95 173 56 96 93 54 74 29 15 130 119 84 13 14 17 16 28 120 82 71 11 12 166 0\n175 66 98 0 72 79 128 124 121 95 173 56 130 119 84 93 54 96 16 76 122 90 120 82 126 86 17 14 13 15 174 3 4 5 70 34 18 19 21 20 9 10 165 0\n176 -101 98 0 164 163 175 73 128 126 85 124 122 89 67 121 92 53 91 88 94 138 141 150 97 144 55 142 143 118 116 66 0\n177 98 0 175 73 109 176 105 135 0\n178 -108 0 177 155 153 0\n179 -103 0 178 149 0\n180 -101 0 179 138 0\n181 -80 0 180 74 109 105 135 0\n182 -66 0 181 73 0\n183 -88 0 180 179 178 155 182 79 134 135 137 140 107 108 147 148 99 59 70 154 144 145 162 129 142 143 112 57 125 118 116 95 123 88 91 63 0\n184 -28 0 183 102 0\n185 -52 0 183 103 0\n186 -65 0 183 104 0\n187 -51 0 184 60 0\n188 -79 0 185 71 0\n189 -60 0 187 181 80 51 0\n190 -89 0 187 188 181 106 0\n191 -100 0 190 183 132 0\n192 106 87 0 80 181 182 186 187 184 98 100 42 144 145 142 143 111 112 113 117 118 114 116 41 44 43 65 61 169 0\n193 87 0 191 72 80 155 77 181 182 186 189 187 184 97 100 136 75 171 39 50 38 52 49 192 146 154 131 119 120 83 81 40 167 0\n194 102 0 193 139 0\n195 107 0 194 147 0\n196 -106 0 194 178 148 0\n197 -99 0 195 155 154 0\n198 -105 0 196 144 0\n199 -90 0 196 145 0\n200 -97 0 197 129 0\n201 -92 0 198 142 0\n202 -91 0 198 143 0\n203 -17 0 199 110 0\n204 -18 0 199 111 0\n205 -71 0 199 112 0\n206 -72 0 199 113 0\n207 -32 0 201 117 0\n208 -42 0 201 118 0\n209 -37 0 202 114 0\n210 -57 0 202 115 0\n211 -75 0 202 116 0\n212 -45 0 206 210 24 0\n213 46 78 0 79 80 181 211 206 205 182 186 187 209 208 207 184 204 46 47 62 45 48 64 169 0\n214 78 0 80 188 210 185 212 211 206 203 213 1 2 6 7 8 22 35 37 23 36 168 0\n215 73 0 214 78 0\n216 85 0 214 91 0\n217 84 0 215 87 0\n218 94 0 216 122 0\n219 0 217 218 200 127 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "dc2f07c368ce2e4b52b49d0f49b0ec8f1e2749b25c8f25a8ea4ea56558d69394e33a1e47b61b85e1cc6b16c749ca6695a4e9c66394e6c5a9665396958d4b59354d3362d2b46d8751d0f5c368d6338d934ccb392d4b32d2b2ac6b86d1b0ee4751cc785d1783d0f23c4f07e685a24c528c62584e8c5312c6294a6152560d44c9342c8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b69b6db4db6db4db6924db6d24d24da4db6924da6d36db69269a6da6da492491249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 31), (facetIndex 33), (facetIndex 47), (facetIndex 48), (facetIndex 65)]))
 (.branch 2
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 85), (facetIndex 93), (facetIndex 101)]))
 (.leaf ([(facetIndex 45), (facetIndex 88), (facetIndex 91)]))))
 (.branch 4
 (.leaf ([(facetIndex 61), (facetIndex 96), (facetIndex 99)]))
 (.branch 5
 (.leaf ([(facetIndex 89), (facetIndex 90), (facetIndex 103)]))
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 92)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 97), (facetIndex 98), (facetIndex 104)]))
 (.branch 8
 (.leaf ([(facetIndex 50), (facetIndex 51), (facetIndex 100)]))
 (.leaf ([(facetIndex 83), (facetIndex 84), (facetIndex 105)]))))
 (.branch 10
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 37), (facetIndex 43), (facetIndex 46), (facetIndex 59), (facetIndex 62), (facetIndex 70)]))
 (.branch 11
 (.leaf ([(facetIndex 39), (facetIndex 44), (facetIndex 53), (facetIndex 54), (facetIndex 60), (facetIndex 74), (facetIndex 75), (facetIndex 76)]))
 (.leaf ([(facetIndex 66), (facetIndex 86), (facetIndex 94)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "86401736630b1524420b188000011aaa0009000b00093a90000aa07700092a9000a0905500099z1d;"⟩
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
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [4, 5]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [7, 8]
def grouped3_0017 : List Nat := [8]
def grouped3_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [9, 10, 11]
def grouped3_0020 : List Nat := [10]
def grouped3_0021 : List Nat := [10, 11]
def grouped3_0022 : List Nat := [11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record005" 78

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record005" "{\"ridges\":[[5,274],[12,304],[18,580],[18,584],[20,608],[26,274],[30,579],[32,274],[39,579],[41,274],[42,274],[55,580],[60,101],[62,705],[63,304],[68,608],[70,833],[71,304],[73,304],[75,705],[76,833],[81,580],[81,584],[83,340],[84,594],[88,114],[95,580],[95,608],[96,224],[97,116],[99,720],[100,224],[100,676],[102,608],[104,224],[104,720],[105,848]],\"owners\":[[5,274,[77,83,85,89,90,91],[26,32,41,42]],[26,274,[85,89,90,91],[5,32,41,42,77,83]],[32,274,[83,89,90,91],[5,26,41,42,77,85]],[41,274,[77,83,91],[5,26,32,42,85,89,90]],[42,274,[77,83,85,89],[5,26,32,41,90,91]],[12,304,[85,89,90,101,103,105],[41,63,71,73]],[63,304,[89,90,103,105],[12,41,71,73,85,101]],[71,304,[85,89,101,105],[12,41,63,73,90,103]],[73,304,[85,89,90,103],[12,41,63,71,101,105]],[18,580,[30,60,62,84,97,99,100],[55,81,95]],[55,580,[84,97,99,100],[18,30,60,62,81,95]],[81,580,[60,62,97,99,100],[18,30,55,84,95]],[95,580,[30,62,84,99],[18,55,60,81,97,100]],[18,584,[20,39,68,70,102],[55,81]],[81,584,[20,68,70,102],[18,39,55]],[20,608,[60,75,76,97,100,104,105],[68,95,102]],[68,608,[97,100,104,105],[20,60,75,76,95,102]],[95,608,[75,76,104,105],[20,60,68,97,100,102]],[102,608,[60,75,97,100,104],[20,68,76,95,105]],[30,579,[39],[]],[39,579,[30],[]],[96,224,[43,66,74,75,86,92],[59,88,94,100,103,104]],[100,224,[43,66,74,86,88,92,103],[59,75,94,96,104]],[104,224,[43,59,66,74,86,92,94],[75,88,96,100,103]],[60,101,[50,59],[]],[100,676,[61,98],[]],[62,705,[75],[]],[75,705,[62],[]],[70,833,[76],[]],[76,833,[70],[]],[83,340,[],[]],[84,594,[],[]],[88,114,[89],[]],[97,116,[96],[]],[99,720,[104],[]],[104,720,[99],[]],[105,848,[],[]]],\"edges\":[[33,[5,12,26,32,41,42,48,63,65,71,73,77,83,85,89,90,91,101,103,105]],[41,[18,20,30,39,55,60,62,68,70,75,76,81,84,95,97,99,100,102,104,105]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,29,31,33,36,37,38],[-5,33,36,37,38],[-7,31,36,37,38],[-9,29,31,38],[-10,29,31,33,36],[-2,33,36,37,47,49,51],[-19,36,37,49,51],[-24,33,36,47,51],[-25,33,36,37,49],[-3,6,16,18,32,43,45,46],[-14,32,43,45,46],[-30,16,18,43,45,46],[-41,6,18,32,45],[-3,4,8,22,23,48],[-30,4,22,23,48],[-4,16,27,28,43,46,50,51],[-22,43,46,50,51],[-41,27,28,50,51],[-48,16,27,43,46,50],[-6,8],[-8,6],[-42,11,21,26,27,34,39],[-46,11,21,26,34,35,39,49],[-50,11,15,21,26,34,39,40],[-16,13,15],[-46,17,44],[-18,27],[-27,18],[-23,28],[-28,23],[-31],[-32],[-35,36],[-43,42],[-45,50],[-50,45],[-51],[-12,52],[-20,52],[-29,53],[-33,53],[-47,53],[-38,54],[-17,55],[-42,55],[-45,55],[-36,56],[-37,56],[-49,56],[-39,57],[-43,58],[-44,58],[-50,58],[-13,59],[-46,59],[-6,60],[-11,60],[-15,60],[-18,60],[-23,60],[-8,61],[-16,61],[-26,61],[-27,61],[-28,61],[-21,62],[-34,62],[-40,62],[-54,63],[-53,63],[-63,64],[-52,64],[-57,65],[-56,65],[-65,66],[-55,-65,67],[-66,68],[-67,69],[-64,68],[-59,70],[-70,71],[-58,71],[-58,-70,72],[-62,73],[-61,73],[-73,74],[-60,74],[-60,-73,75],[-75,77],[-71,76],[-71,-74,77],[-72,77],[-68,-77,78],[-69,-76,78],[-78],[1,2,5,7,9,10,12,19,20,24,25,29,31,33,36,37,38,47,49,51],[3,4,6,8,14,16,18,22,23,27,28,30,32,41,43,45,46,48,50,51]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":274,\"a\":5,\"owners\":[77,83,85,89,90,91]},{\"tag\":\"mate\",\"ridge\":274,\"a\":26,\"owners\":[85,89,90,91]},{\"tag\":\"mate\",\"ridge\":274,\"a\":32,\"owners\":[83,89,90,91]},{\"tag\":\"mate\",\"ridge\":274,\"a\":41,\"owners\":[77,83,91]},{\"tag\":\"mate\",\"ridge\":274,\"a\":42,\"owners\":[77,83,85,89]},{\"tag\":\"mate\",\"ridge\":304,\"a\":12,\"owners\":[85,89,90,101,103,105]},{\"tag\":\"mate\",\"ridge\":304,\"a\":63,\"owners\":[89,90,103,105]},{\"tag\":\"mate\",\"ridge\":304,\"a\":71,\"owners\":[85,89,101,105]},{\"tag\":\"mate\",\"ridge\":304,\"a\":73,\"owners\":[85,89,90,103]},{\"tag\":\"mate\",\"ridge\":580,\"a\":18,\"owners\":[30,60,62,84,97,99,100]},{\"tag\":\"mate\",\"ridge\":580,\"a\":55,\"owners\":[84,97,99,100]},{\"tag\":\"mate\",\"ridge\":580,\"a\":81,\"owners\":[60,62,97,99,100]},{\"tag\":\"mate\",\"ridge\":580,\"a\":95,\"owners\":[30,62,84,99]},{\"tag\":\"mate\",\"ridge\":584,\"a\":18,\"owners\":[20,39,68,70,102]},{\"tag\":\"mate\",\"ridge\":584,\"a\":81,\"owners\":[20,68,70,102]},{\"tag\":\"mate\",\"ridge\":608,\"a\":20,\"owners\":[60,75,76,97,100,104,105]},{\"tag\":\"mate\",\"ridge\":608,\"a\":68,\"owners\":[97,100,104,105]},{\"tag\":\"mate\",\"ridge\":608,\"a\":95,\"owners\":[75,76,104,105]},{\"tag\":\"mate\",\"ridge\":608,\"a\":102,\"owners\":[60,75,97,100,104]},{\"tag\":\"mate\",\"ridge\":579,\"a\":30,\"owners\":[39]},{\"tag\":\"mate\",\"ridge\":579,\"a\":39,\"owners\":[30]},{\"tag\":\"mate\",\"ridge\":224,\"a\":96,\"owners\":[43,66,74,75,86,92]},{\"tag\":\"mate\",\"ridge\":224,\"a\":100,\"owners\":[43,66,74,86,88,92,103]},{\"tag\":\"mate\",\"ridge\":224,\"a\":104,\"owners\":[43,59,66,74,86,92,94]},{\"tag\":\"mate\",\"ridge\":101,\"a\":60,\"owners\":[50,59]},{\"tag\":\"mate\",\"ridge\":676,\"a\":100,\"owners\":[61,98]},{\"tag\":\"mate\",\"ridge\":705,\"a\":62,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":705,\"a\":75,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":833,\"a\":70,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":833,\"a\":76,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":340,\"a\":83,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":594,\"a\":84,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":114,\"a\":88,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":116,\"a\":97,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":720,\"a\":99,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":720,\"a\":104,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":848,\"a\":105,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":48,\"full_literals\":[-12,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":65,\"full_literals\":[-20,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-29,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-33,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":101,\"full_literals\":[-47,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":91,\"full_literals\":[-38,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":61,\"full_literals\":[-17,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":96,\"full_literals\":[-42,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":99,\"full_literals\":[-45,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":89,\"full_literals\":[-36,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":90,\"full_literals\":[-37,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":103,\"full_literals\":[-49,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":92,\"full_literals\":[-39,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":97,\"full_literals\":[-43,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":98,\"full_literals\":[-44,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":104,\"full_literals\":[-50,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":50,\"full_literals\":[-13,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":100,\"full_literals\":[-46,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":30,\"full_literals\":[-6,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":43,\"full_literals\":[-11,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":59,\"full_literals\":[-15,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":62,\"full_literals\":[-18,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":70,\"full_literals\":[-23,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":39,\"full_literals\":[-8,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":60,\"full_literals\":[-16,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":74,\"full_literals\":[-26,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":75,\"full_literals\":[-27,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":76,\"full_literals\":[-28,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":66,\"full_literals\":[-21,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":86,\"full_literals\":[-34,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":94,\"full_literals\":[-40,62]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-73,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-73,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-75,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-74,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-68,-77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-69,-76,78],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[5,12,26,32,41,42,48,63,65,71,73,77,83,85,89,90,91,101,103,105]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[18,20,30,39,55,60,62,68,70,75,76,81,84,95,97,99,100,102,104,105]}]}"
  "98 1 2 5 7 9 10 12 19 20 24 25 29 33 36 37 38 47 49 0 31 37 96 0\n99 3 4 6 8 14 16 18 22 23 27 28 30 41 43 45 46 48 50 0 32 37 97 0\n100 68 0 31 37 77 79 75 71 72 74 69 70 38 39 47 48 49 43 40 41 42 7 3 9 1 4 5 2 6 8 98 0\n101 -77 0 100 95 93 0\n102 -75 0 101 89 0\n103 -72 0 101 92 0\n104 60 71 0 37 32 82 51 53 35 81 80 55 11 17 54 56 58 59 60 21 25 28 13 30 12 16 19 10 99 0\n105 71 0 32 102 37 81 82 80 51 53 55 35 17 11 104 88 85 61 62 64 65 20 16 19 18 27 29 14 15 99 0\n106 -74 0 105 101 91 0\n107 -73 0 106 86 0\n108 -60 0 106 87 0\n109 -62 0 107 84 0\n110 -61 0 107 85 0\n111 -6 0 108 56 0\n112 -11 0 108 57 0\n113 -15 0 108 58 0\n114 -18 0 108 59 0\n115 -23 0 108 60 0\n116 -21 0 109 66 0\n117 -34 0 109 67 0\n118 -40 0 109 68 0\n119 -8 0 110 61 0\n120 -16 0 110 62 0\n121 -26 0 110 63 0\n122 -27 0 110 64 0\n123 -28 0 110 65 0\n124 43 46 48 50 0 37 32 123 122 115 114 120 119 111 18 35 12 10 16 17 11 99 0\n125 -42 67 0 122 117 116 121 112 22 45 50 76 73 0\n126 -46 67 0 103 116 117 121 112 55 80 83 52 26 44 76 73 74 50 47 49 23 33 0\n127 43 50 46 0 122 120 19 124 0\n128 67 0 118 113 117 121 116 112 125 34 126 127 24 36 50 46 73 76 0\n129 76 0 105 90 0\n130 69 0 128 78 0\n131 0 130 129 95 94 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record005
