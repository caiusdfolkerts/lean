module
prelude
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
def vertexColumn : Fields := ⟨10, hexnat% "3d19c3707ce48f2c6a3a4e87a39996358b61d86e8791e1783ee45c9c65998e539395952d58d3361d4749d0f78370ce3c4e9364e334ccb3c2e4b52e2b4ac6b86d1b0ed8729e1745c970de0f43c4f0bc1fc606c0f312648c6198960db091a4c51944d0b70360cc318c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6934db49249b69b4db4db4db4924d36d36da6da4da4da4c9249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨55, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40bc48008a00098800000", 612489549339164672, 1688854155231232, hexnat% "204000000000000000000", hexnat% "80000000021000000000", 281474976710656]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bc00881000099000000", 1724038527320064, hexnat% "204000000000000000000", hexnat% "400040008000000800000", hexnat% "80000000021000000000", 9223512774343131136]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000880000009000000", hexnat% "200000004a00000000000", 844431372582912, 9225623836936896512, hexnat% "7000000000000000000", hexnat% "400c40000000000800000", hexnat% "80000000021000000000"]
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
def vertexColumn : Fields := ⟨10, hexnat% "3e31c3707ce48f2728ea668da4e8ba1eb1635a361d8ce1b91e2785e0fb91724e9c65994e4b9c5635c34cd8751d2743de0dc338f13a4d938cd332cd8b52ccb4acab1ad1b26c3bc1e4731e2785d1725c3743c8f13c2f07d981b03cc499219a160d989324691944d0b70360cc318e0711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6936d36da6934db4d269b6da6da49269b69a6d36d249369b499249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨81, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2008b410c452000c00000", hexnat% "2010000001000000000000", hexnat% "4000000010000000000000", 562956395872256, hexnat% "6000000000044000000", 9126805504]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6200884010452000c00000", 3377699720527872, hexnat% "30100000000000000", 562956395872256, hexnat% "6000000000044000000", hexnat% "10000001000220000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "42068840134403e4c00000", hexnat% "2000000008000000000000", hexnat% "10000000000000000000", hexnat% "10100012000000000", hexnat% "20004000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2008b41160523e4c00000", hexnat% "2000000009400000000000", hexnat% "14000000000000000000", hexnat% "4002000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000240134403e4c00000", 3377699720527872, hexnat% "10100012000000000", hexnat% "14000000000000000000", hexnat% "4002880000000000000000", hexnat% "2000000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "42068901120523e4c00000", hexnat% "20004000000000000", hexnat% "2010000001000000000000", 2322168557862912, 4611686018427387904]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22160000010423e4c00000", hexnat% "10002010000000000", hexnat% "20100000000000000", hexnat% "4000880010000000000000", 3448068464705536, 4611686018427387904]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "221000401d440364000000", hexnat% "30100010000000000", hexnat% "6080000000000000000", hexnat% "4000800000000000400000", 563089548247040]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000301064521c0800000", hexnat% "2000000009000000000000", hexnat% "10000000000220000000", 4616189618121867264, hexnat% "6080000000000000000", hexnat% "4000800000000000400000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "42028900164521c4c00000", hexnat% "20100000000000000", hexnat% "14000000000020000000", 4611967493404098560, hexnat% "2000000008000000000000", 8589934592]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "216890009440364000000", hexnat% "2000000000000000000000", hexnat% "4000000010000000400000", hexnat% "24000000000000000", 1689951519375360, 72057731485270016]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2204810009440140000000", hexnat% "10000000000220000000", hexnat% "20004010000000000", hexnat% "4002080000000000400000", 563089548247040, 72057594037927936, 4616189618121867264]
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
def vertexColumn : Fields := ⟨10, hexnat% "8f0ea4e87a398762b83e747893a599366394e479e14e5c5595954d58d68d8b4ad8749d0f5c338d534cc73c2ccb4acab1ad1b16c3bc1d8729d1715c3783c8f0bc1fc6074628c619b111c709626194643931465854550d58330c6342c8b0ac8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6d26da69a49a4d24db4d24da49249a69349a4c9249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "104538210d2c8000000", hexnat% "2000000810000000000", hexnat% "10808000000000000", hexnat% "1080000a0000000000", 285890471526400]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3262896721100800, hexnat% "3001000000080000000", hexnat% "148000084000000000", 756604737398243328, hexnat% "14000000000000000", 72057594037927936]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [252201582488190976, 576460769483292672, hexnat% "1480000a4000000000", 427718881574912, hexnat% "3001000000000000000", hexnat% "1000a000000000000", 4611704229088722944]
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
