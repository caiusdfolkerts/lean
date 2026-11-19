module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00004Data
public import GraphInputsRow29Part00004Frames
public import GraphInputsRow29Part00004Leaves
public import GraphInputsRow29Part00004Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00004.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record024
def vertexColumn : Fields := ⟨10, hexnat% "7ce8b52cca72b2aaa6aa6a6693a1eac6a99a6999964d876338ae1b89ee8751cc671b26a96a669665391e6c5a95a5995954d475334ad1b49de0f43b0f23a8da398f1364e5354e334cc73a2d8b92ccb8ad2b2ac6b46c9b16c3ba1d8791cc789d2729c6745c9715c3723c4f0bc1f1703ce0b224c85a0e8560d88e1382e07b81c853116439154352344d0b41d"⟩
def kindColumn : Fields := ⟨3, hexnat% "934db6da4db6d24924d36db6936db49249369b6db6d36db6db6d26db6db6d2492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨53, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨107, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40081f00207c000000000f000000", hexnat% "2000008000024000000000000000", 9010498594930688, hexnat% "2040800000000000000000", hexnat% "810200000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4018320060ca402003003f000000", hexnat% "800002000000000000000000000", hexnat% "80000200000000000000000", hexnat% "10000040000000000000000", hexnat% "2000048000100000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22040880020010010000000", hexnat% "2000048000100000000000000000", hexnat% "810200000000000000000000000", hexnat% "8000020000000000f000000", hexnat% "4008100020400000000000000000", hexnat% "24000020020000000", hexnat% "10000040000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c3 c1
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c4 c0
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record024_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00004.record024

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00004.record031
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record031
def vertexColumn : Fields := ⟨10, hexnat% "3929ab86d1ac6c9aa69991e2785e0fb919a785d16c5c96a59951d2745d0f743b0f23a8f13a4e4b8ad1b26c5b0ef07a1e4751cc789d2729c570dd0f23d941b382989921a986199162584e0b81ee06616446961465454951342d07703a0d8390e2318d1324c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "249b6d249249b6d2492492492492492492491249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fe0fe1061e800000000000", hexnat% "10010001800000000000000", 16140901064495857664, hexnat% "1e0000000000000000", hexnat% "1e0000000000000000000", 420013441810432, 135107988821114880]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fe0fe0861d800000000000", hexnat% "10010001800000000000000", hexnat% "16000000000000000", hexnat% "1e0000000000000000", hexnat% "1e0000000000000000000", 701488418521088, 135107988821114880]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fe0fe0461cc00000000000", hexnat% "10010001800000000000000", hexnat% "1a000000000000000", hexnat% "1e0000000000000000", hexnat% "1e0000000000000000000", 912594651054080, 135107988821114880]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fe0fe0261ca00000000000", hexnat% "10010001800000000000000", hexnat% "1c000000000000000", hexnat% "1e0000000000000000", hexnat% "1e0000000000000000000", 947779023142912, 135107988821114880]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "1fffffffffffe0000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record031_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record031_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00004.record031

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00004.record040
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record040
def vertexColumn : Fields := ⟨10, hexnat% "6707cd2b2a9a99a5693a1eac6a9a66658d62d8766386e4789e1783ee4751b4731ac671d27299a599565391e6c5a9665654d52d4756346d4749dd0ec3c8ea398d9354cd34ccb31cf0b62e4b52e2b4ac6b46c9b16c3ba1d8791cc789ca719d1725c570dd0f23c1f1703ce084e0bb816451916439254550d44d0b41dc0e8360e4388d0b12c2b21c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1a6db6db6db6da6d24db6db6924db49269249249b6da4924934924924d2492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨108, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "38040f104082f5bb0000000", hexnat% "38020000000000000000", hexnat% "1000100000040800400000000000", 17293823256297472000, 6614663026442240]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "38040f504042cdbb0000000", hexnat% "1000100008000800400000000000", hexnat% "30020000000000000000", 17293824905564913664, 5488763119599616, 2252899325313024]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "38040f504012c7bb0000000", hexnat% "1000100008000800400000000000", hexnat% "30020000000000000000", 17293825317881774080, 6333188049731584, 2252899325313024]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8040f3a41ae303e0000000", hexnat% "380000000c0010000000", hexnat% "1000130000040000000000000000", 1065151889408, 6342475650221211648]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [17879232228827856896, hexnat% "8000800400010000000000", hexnat% "730000000010000000", hexnat% "78000000200000000000", hexnat% "1000130000040000000000000000", 4398046511104]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8040800408008380000000", hexnat% "730000000010000000", hexnat% "1000130000040000000000000000", 3677028876288, 17870564933821792256, hexnat% "380000002c0000000000", 6403556793909248]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record040_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record040_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record040_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record040_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record040_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record040_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record040_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record040_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record040_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00004.record040
