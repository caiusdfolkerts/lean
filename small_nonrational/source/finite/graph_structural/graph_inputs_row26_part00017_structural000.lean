module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00017Data
public import GraphInputsRow26Part00017Frames
public import GraphInputsRow26Part00017Leaves
public import GraphInputsRow26Part00017Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021
def vertexColumn : Fields := ⟨10, hexnat% "1d46d31c573926cb4a3ab1a8e8ba719a639b16659362db0e5386e8791e0fb91744e9366392e5c53971565555354b51b61d17783d0dc338f13a4d938ccb392ccb8acab1ae1b26c3bc1d8751cc729c6785d1725c3783c1f0f1c25184e0b8b1864390d44d0b41d30ca382c4b0ac4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6d36db6d26d36da4db6da4936936da49249a6d249b692249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffffe7ffbf3bfff00000", 566935683072, 70643622084608, 1729382256910270464]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffdfdfffffbfffcff00000", hexnat% "20000000400030000000", hexnat% "200000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffdfdfefefbf0fcff00000", 1157425104234217472, hexnat% "20200000000030000000", 1030792151040, 70368744177664]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "1fffffefefffffffff00000", hexnat% "10100000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c6 c7
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffff7ffbfbffff00000", 70643622084608, 576460752303423488]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffedffffbf7bdff00000", 566935683072, 70369281048576, hexnat% "120000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffcde7fbff7bffc00000", hexnat% "300000000000000000", 1730508156817113088, hexnat% "20000000400100000", 549757911040]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffdfddffff9effcfb00000", hexnat% "20000010000400000", 105553384701952, hexnat% "20200000000020000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffde7e9ff5affa00000", 1154610354468159488, 708669603840, hexnat% "20000000000400000", 580964351930793984]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffdfcdf7efbe02cbb00000", hexnat% "20000000400030000000", hexnat% "300000000004000000", hexnat% "20000010500400000", 580964351930793984, 1065151889408]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c18 c15
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c19 c14
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c20 c4
  c21
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record035
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035
def vertexColumn : Fields := ⟨10, hexnat% "e4b4a3a8da8e8ba719a639b16658d62db0e5386e8785ee47493a4d98e4b9715a539715654d52d70d5346d8745de0f4370da338f13a4d9334e332cf0b92d4b32e2b2ac6b86c9b16c3bc1d8751cc749ca719e1745c9715c3783d0f13c2f07c3c708b28683a518361382e079c12c6190e5450d44d0b41d"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6d24db6d34926db4936db4d249b4db6db4db6db4da6d36db6da6d2449249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨47, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30020c00880809201380000", 3746994889972252672, hexnat% "d0000000000000000000", hexnat% "8200208000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f0003c80809201380000", hexnat% "8200208000000000000000", hexnat% "c00000000000000000", hexnat% "30000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "38200e08800809001200000", 36028805610471424, hexnat% "80002000000000000000", hexnat% "70000000000000000000", 1441151880758558720]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "282f0203480809201380000", hexnat% "10000400000000000000000", hexnat% "808000000000000000", 576460752303423488]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8210e08080809201380000", hexnat% "80002000000000000000", hexnat% "40001000000000000000", hexnat% "30020000000000000000000", 864691128455135232]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "202f0003480008000380000", hexnat% "8000200000000200000000", hexnat% "c00800001000000000", hexnat% "10000000000800001000000", 9223372036854775808]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8210208080008000200000", hexnat% "80002000000200000000", hexnat% "40001000000000180000", hexnat% "30020000000001000000000", hexnat% "800c00000000000000", hexnat% "400000800001000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record035
