module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00025Data
public import GraphInputsRow29Part00025Frames
public import GraphInputsRow29Part00025Leaves
public import GraphInputsRow29Part00025Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00025.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 7177611906121728, (certNat% 3), 28991029248, 118747255799808, (certNat% 4)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 31172067328, (certNat% 6), (certNat% 4), (certNat% 7), (certNat% 8)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 32245809152, (certNat% 10), (certNat% 4), (certNat% 11), (certNat% 12)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 123145302310912, (certNat% 14), 30064771072, (certNat% 7), (certNat% 15)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), (certNat% 6), (certNat% 4), 7036874417766400, (certNat% 18)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), 72057594037927936, 141012366262272, (certNat% 20), (certNat% 21)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 515396075520, 25769803776, (certNat% 20), (certNat% 23), (certNat% 24)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c7 c5
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), (certNat% 3), 515396075520, 985162452041728, 29393682432, 123145302310912]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c10 c4
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c11 c3
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c12 c2
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c13 c1
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c14 c0
  c15
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00025.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00025.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008
def vertexColumn : Fields := ⟨10, (certNat% 27)⟩
def kindColumn : Fields := ⟨3, (certNat% 28)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨35, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨87, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨113, by decide⟩, ⟨121, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 4508032050397184, (certNat% 30), (certNat% 31), 976366325465088]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 33), (certNat% 30), 949978046398464, (certNat% 34)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 36), (certNat% 37), (certNat% 38), (certNat% 39), 870813209198592]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 36), (certNat% 37), (certNat% 38), (certNat% 41), 870813209198592]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), (certNat% 36), (certNat% 44), 1121501860331520, 3377699720527872, (certNat% 45)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00025.record008
