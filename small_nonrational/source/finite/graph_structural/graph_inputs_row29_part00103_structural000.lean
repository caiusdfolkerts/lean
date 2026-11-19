module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00103Data
public import GraphInputsRow29Part00103Frames
public import GraphInputsRow29Part00103Leaves
public import GraphInputsRow29Part00103Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00103.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003
def vertexColumn : Fields := ⟨10, hexnat% "3e0f43b0ba2d8762e4ad1b4b32ac9b0ec789d26c9ca9a8ea66a5a568da69a66399968d9362da4e33a2e2b86e8789e785d16c5c99a4e966659564d969665395958d5352d64d3362d2b46d8749d54d3352c6b46c5b49c6745c3713c2fb81e0b2298a9294a321c27162079610754348c6344c4b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "9b49a4d26d36db6db6db6db6db4936db6db6db6db6db492492492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [864691179994742784, hexnat% "400200000200000000000000", hexnat% "1b000000000000000000000", hexnat% "c0000000000000000000000", 4479516672, 11542724608, 1153433600]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00103.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00103.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005
def vertexColumn : Fields := ⟨10, hexnat% "3e0f43b0dc2f07c2e87a278b51d4ad2ac9723c74ab26c9caaa9aa8e9c6a9a966595635a362da8e33a2e2ba1e1783e786715c5c96a6695a4e9966391e5c5955558d64d3362d2b61d1743d70da354d8b52ccb4acab16c3b61d4731ca745c570dc8f13c2f07ec8aa2c49528c930cc689322a88e545311544d48d130cc2b05c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db69b4da4db4d26db6db6934db6d36db6db49a4db4da4db49a6db492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨61, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8880068000d890505e00000", 2305843559103725568, hexnat% "100000000000800000000", hexnat% "410200000000000000000000", 33554432]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000068200c89840fe00000", 38654705664, hexnat% "88000000001000000000000", hexnat% "10200000000000000000000", hexnat% "900000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88000680009890405e00000", hexnat% "300000000000000000000", hexnat% "800000000000800000000", hexnat% "410000000000000000000000", 4462739456, 2306969458876350464]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "98b00680000090d0b600000", hexnat% "400000002000000000000000", 422212473454592, 1126449729765376, 2251799813685248]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8900080000090d0b600000", 2306969458876350464, hexnat% "80000000009000000000000", hexnat% "200000800000800000", hexnat% "410200400000000000000000", 67108864]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9880068000d888105a00000", 2305843009347911680, hexnat% "400200000000000000000000", 34397487104, hexnat% "100000000010400000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "410b00680001898d07c00000", 136314880, hexnat% "88000000008000000000000", 2306968909120536576]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000682005888d0fe00000", hexnat% "400200000000000000000000", hexnat% "88000000008000000000000", hexnat% "900000000010000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000068000188890fe00000", 2306968909120536576, hexnat% "400200000000000000000000", hexnat% "900000000010000000000", hexnat% "88000000008000000000000", 17179869184]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000028200400890f600000", 431008566476800, hexnat% "400200400000000000000000", hexnat% "900000000010000000000", 17179869184, hexnat% "88000000008000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88000600009890503800000", 6291456, hexnat% "900000000000800000000", hexnat% "400000002000000000000000", 1126449863983104, hexnat% "10200080000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8880020000d880107a00000", 2305843559103725568, 51543801856, hexnat% "100000000010000000000", hexnat% "410200400000000000000000", hexnat% "80000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "900200000890903000000", hexnat% "88000000009000000000000", hexnat% "400000002000000000000000", hexnat% "10200480000000000000000", 14680064, 1126449863983104, 17179869184]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c22 c7
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c23 c4
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00103.record005
