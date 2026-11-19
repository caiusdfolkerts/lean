module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00022Data
public import GraphInputsRow24Part00022Frames
public import GraphInputsRow24Part00022Leaves
public import GraphInputsRow24Part00022Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨55, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 612489549339164672, 1688854155231232, (certNat% 3), (certNat% 4), 281474976710656]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 1724038527320064, (certNat% 3), (certNat% 6), (certNat% 4), 9223512774343131136]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), 844431372582912, 9225623836936896512, (certNat% 9), (certNat% 10), (certNat% 4)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003
def vertexColumn : Fields := ⟨10, (certNat% 11)⟩
def kindColumn : Fields := ⟨3, (certNat% 12)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨81, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 15), 562956395872256, (certNat% 16), 9126805504]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 3377699720527872, (certNat% 18), 562956395872256, (certNat% 16), (certNat% 19)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), (certNat% 23), (certNat% 24)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), (certNat% 27), (certNat% 28)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 3377699720527872, (certNat% 23), (certNat% 27), (certNat% 30), (certNat% 31)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 24), (certNat% 14), 2322168557862912, 4611686018427387904]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), (certNat% 35), (certNat% 36), 3448068464705536, 4611686018427387904]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), (certNat% 40), 563089548247040]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), (certNat% 43), 4616189618121867264, (certNat% 39), (certNat% 40)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 35), (certNat% 45), 4611967493404098560, (certNat% 21), 8589934592]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 31), (certNat% 47), (certNat% 48), 1689951519375360, 72057731485270016]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 43), (certNat% 50), (certNat% 51), 563089548247040, 72057594037927936, 4616189618121867264]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005
def vertexColumn : Fields := ⟨10, (certNat% 52)⟩
def kindColumn : Fields := ⟨3, (certNat% 53)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), (certNat% 55), (certNat% 56), (certNat% 57), 285890471526400]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3262896721100800, (certNat% 58), (certNat% 59), 756604737398243328, (certNat% 60), 72057594037927936]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [252201582488190976, 576460769483292672, (certNat% 61), 427718881574912, (certNat% 62), (certNat% 63), 4611704229088722944]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00022.record005
