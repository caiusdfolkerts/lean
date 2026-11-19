module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00001Data
public import GraphInputsRow16Part00001Frames
public import GraphInputsRow16Part00001Leaves
public import GraphInputsRow16Part00001Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00001.record062
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record062
def vertexColumn : Fields := ⟨10, hexnat% "3c2e89e2d4ad2a68da598e6338ae1783ef07a178751b469936565394cd2b45d0f783d0ec370f23a8da358ce3c4e9394d5334e8b32d2b86c9b16c3b51cc749ca719e170dc8f13caa1582e078a91542d07703a0d4330d2328e1314c8b0ac1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6da49b6db6db492492492492492492492492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000eeb3e2db800000", hexnat% "c0000000000000000", 351912977235968, 4449653227520, 4512395720392704, 4294967296]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c00620fafc7800000", hexnat% "100080001010000000", 123145973399552, 5770511900475392, 2533274790395904]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10009ff0737b000000", 3850438180864, hexnat% "80040000004800000", 13228499271680, hexnat% "40020000000000000", 17179869184]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800f6d5e7d1800000", hexnat% "140000000000000000", 11029543124992, 35253762654208, 2533274790395904, 33554432]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100097dcf771000000", 2288085844885504, 2233483657216, hexnat% "80040000000800000", 134217728, hexnat% "40020000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80040c02246800000", hexnat% "100080001111000000", hexnat% "40020000000000000", 2568461846839296, 4517103004549120, 1128665865781248, 581641785311232]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record062_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record062_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record062_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record062_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record062_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record062_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record062_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record062_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record062_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00001.record062

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00001.record074
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record074
def vertexColumn : Fields := ⟨10, hexnat% "1f3621eb86c9aa6599561d94e1b89e1783ed8479e1725a9565554755346d2745d0f783d0f23a8e6358e9354cd31cd4b8ac9b0ef07a1d8751e2749ca719d1715c3743c8f13c6a168960b81e1a4592542d07703a0d4388c6324c5312c2b06d0721c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6d36db6d249a6db6da492492492492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1400a805fffe000000", hexnat% "20010000080000000000", 193514046488576, 6262818231812096, hexnat% "280140000000000000", 283673999966208]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3401b7fffffe000000", 2251799813685248, hexnat% "80040000000000000", hexnat% "20010000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200117cab79e000000", hexnat% "20050020000000000000", 2291691469930496, hexnat% "100080010060000000", 17592186044416, hexnat% "80040000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28015faedffe000000", 89197880803328, hexnat% "100080000000000000", hexnat% "20050020000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28015fae5ffe000000", hexnat% "100080010000000000", 88098369175552, hexnat% "20050020008000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000800308fc000000", hexnat% "280140008002000000", 6262955670765568, hexnat% "20050020080000000000", 197912092999680, 2252152001003520, 281496451547136]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record074_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record074_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record074_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record074_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record074_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record074_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record074_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record074_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00001.record074_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00001.record074
