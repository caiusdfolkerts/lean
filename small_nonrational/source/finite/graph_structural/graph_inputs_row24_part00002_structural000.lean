module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00002Data
public import GraphInputsRow24Part00002Frames
public import GraphInputsRow24Part00002Leaves
public import GraphInputsRow24Part00002Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006
def vertexColumn : Fields := ⟨10, hexnat% "f0ba2d49d2aa9aa668da4ea664d8ce1783ef07a1d45d1aa5a9664d94e6654d4cd1743dd0dc3a8da398f1364e5354cd34ce8b62ccb8ad2b2ad1b26c5b0ee4731e2749c6745c3723c4fe0ac2c88560b81ee06c1c84550b41dc0e8360e4330e2348d1314c8b0ac1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "126db6db6d249b6db6db492492492492492492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3000c003daff0680000000", 962877980672, 10414681512476672, hexnat% "2000800000040000000", hexnat% "1000400000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3000c003c27fe630000000", 864691129528877056, hexnat% "3000000000000000000", 6896139076894720, 10414681512476672]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3000c003df83f8c0000000", 864691128723570688, hexnat% "3000000000000000000", 123145839181824, 9020423459045376]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3000d427fe9f0000000", hexnat% "2000800280000000000000", hexnat% "1000400010000000000000", 9007285154086912, 2392545891975168, 1407374883553280]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10004002d2020020000000", hexnat% "1000400802040000000", hexnat% "2000800100400000000000", hexnat% "2000800004090000000", 9020423459045376, 2570108429926400, 1143595172102144]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013
def vertexColumn : Fields := ⟨10, hexnat% "3c8e925c4f3a23cb8ab2a5ae1b26a99a695b0e9392e8785e0fbc13c789d26c972539e15a54d70d9352d4745d0f783b0da338cd32cc73c2e8b62e4b32d2b0ef07a1d8791d2729c5783d0f13c2fc32c29285a0da0e079a1165250d50d074c328c530cc4b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db49b6da4d24db6db6926924d24926da4d36da492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1380669a021f400000", 5531917877248, hexnat% "80001000000800000", 4538852718936064, hexnat% "c000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3806490021e400000", 844424955297792, hexnat% "100010000000000000", 16492674416640, hexnat% "c080000001000000000", 35218731827200]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9241404027952955392, hexnat% "8000000201800000000", 16492674416640, hexnat% "100010000003000000", 10836786607554560, hexnat% "40b0000000000800000", 281483633754112]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c3 c2
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020
def vertexColumn : Fields := ⟨10, hexnat% "f132c4f38ab2b2a6aa5a36b86b1b2695876c3a2e4ba1e0fbc1e26c96a4d94e785d16c5715351d70d4b51d0f783b0da334c73c2e8b62e4b32d2b2ac9b16f07a1d8791cc749c6783d0f0bc1fe22c2a283a918560d9894a439494550d4c314c3322c2b06c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6936db4d26db4d34d36da4d34d349a4d24936d249b489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30801a8c003cc00000", hexnat% "20800000200000000000", 197568495616, 720576009098756096, hexnat% "40002000018000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "108a1a85be0cc00000", hexnat% "40002000000000000000", 43981270417408, hexnat% "a00000000000000000", hexnat% "20000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [728036943031435264, hexnat% "40002000000000000000", hexnat% "20800000200000000000", 13194407968768, hexnat% "108000000000000000", hexnat% "200000000020000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10821a841c0cc00000", 2882304311272931328, 8942390345728, hexnat% "a00000000020000000", hexnat% "60000000010000000000", 35184372088832]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20b02000292834800000", 4423820509184, hexnat% "40000000009008000000", 721138890332700672, 6896136929411072, 9223372036854775808]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000a1aa09c0c800000", 2305844109262192640, hexnat% "108000040000400000", hexnat% "a00000000010000000", hexnat% "20000000002200000000", 8796093022208]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [721174177859502080, hexnat% "a00000000030000000", 6896137063628800, hexnat% "40002000018000000000", hexnat% "108000040000400000", hexnat% "20000000002200000000", 8813272891392]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00002.record020
