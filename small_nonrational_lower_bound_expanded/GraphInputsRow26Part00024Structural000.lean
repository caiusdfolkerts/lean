module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00024Data
public import GraphInputsRow26Part00024Frames
public import GraphInputsRow26Part00024Leaves
public import GraphInputsRow26Part00024Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00024.record045
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨69, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 555876352, 67371008, 72057679937798144, 18014398510530560]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00024.record045

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00024.record056
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056
def vertexColumn : Fields := ⟨10, (certNat% 4)⟩
def kindColumn : Fields := ⟨3, (certNat% 5)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 153122423837818880, (certNat% 7), (certNat% 8), 36028805608898560]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 45036007011123200, (certNat% 10), (certNat% 8), 144115222435594240]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), (certNat% 13), (certNat% 14)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), (certNat% 17), (certNat% 8), (certNat% 18)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 17), 153122423837818880, (certNat% 13), 36028805608898560]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 14), (certNat% 17), 36310280585609216, (certNat% 18)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), (certNat% 23), (certNat% 24)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 90071992547409920, 5764607523034234880]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 26), 4683743612465315840, 1170935907411296256]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), 5764607523034234880, 54043208413347840, (certNat% 29), (certNat% 26)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), 36028809903865856, (certNat% 31), (certNat% 32)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), 153122423837818880, (certNat% 35), 36028805608898560]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c14 c12
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), (certNat% 29), (certNat% 26), 45036007011123200, (certNat% 37)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 29), (certNat% 39), (certNat% 40), 54324679095091200, (certNat% 41)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c18 c15
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c19 c11
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c20 c6
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c21 c5
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c22 c4
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c23 c3
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c24 c2
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c25 c1
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c26 c0
  c27
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00024.record056
