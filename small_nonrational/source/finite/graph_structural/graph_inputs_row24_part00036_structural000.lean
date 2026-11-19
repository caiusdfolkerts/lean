module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00036Data
public import GraphInputsRow24Part00036Frames
public import GraphInputsRow24Part00036Leaves
public import GraphInputsRow24Part00036Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000
def vertexColumn : Fields := ⟨10, hexnat% "3348f3324eb26c5a364d8ce1b89e0fb318e539c96a5c56558d5353362d1b61d2743dc8da3c4d538cd3332d2b1ad1b26c3bc1cc789d2719e1745c970dcac170aa168a61588e1382e07b21c44a916625296151548d1342d0752328d1314c8b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db69249b4924d2492492692492692492449249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7faffdded9ff800000000", 4609152743636992, 2449958197289549824, hexnat% "5000000000000000000", 562949953421312]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fafdffcd9ff800000000", hexnat% "20020000000000000", hexnat% "5000000000000000000", 668503069687808, 4503599627370496]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fafed9fddff800000000", 598134325510144, hexnat% "10600000000000000", hexnat% "5000000000000000000", 2305843009213693952]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff34fb5ffff800000000", hexnat% "30400000000000000", hexnat% "c00000000000000000", 45035996273704960, hexnat% "80000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fa34d95dfff800000000", hexnat% "480080000000000000", hexnat% "10600000000000000", hexnat% "5800000000000000000", 2306405959167115264, hexnat% "20020000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f8f5d5fd5ff800000000", hexnat% "a0000000000000000", 738871813865472, 3026418949592973312, hexnat% "7000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f9ffd7bc7ff800000000", 18436610974547968, 2882303761517117440, hexnat% "6000000000000000000", 562949953421312]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f9f7ff3c7ff800000000", hexnat% "80080000000000000", hexnat% "6000000000000000000", 985162418487296, 18014398509481984]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f9fbc7fd7ff800000000", 703687441776640, hexnat% "41800000000000000", hexnat% "6000000000000000000", 2305843009213693952]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff31ef5ffff800000000", hexnat% "c1000000000000000", hexnat% "c00000000000000000", 45035996273704960, hexnat% "20000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f973c73ceff800000000", 18313465672237056, hexnat% "41800000000000000", hexnat% "6800000000000000000", 2306405959167115264, hexnat% "80080000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f8ffd53c5af800000000", 54325770016784384, 3026418949592973312, hexnat% "7000000000000000000", 567347999932416, 175921860444160]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff5ff0c1ad800000000", 567347999932416, 13581305065242624, 54325770016784384, hexnat% "a0000000000000000", 175921860444160]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f8f0c1fff9b800000000", hexnat% "30400004000000000", hexnat% "c1000020000000000", hexnat% "7000000000000000000", 2305847407260205056, 720575940379279360]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff0c15ff9b800000000", 2305847407260205056, 45038470174867456, hexnat% "30400000000000000", hexnat% "c1000000000000000", 720575940379279360]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f8fed1bc7bf800000000", 18436610974547968, hexnat% "10600000000000000", hexnat% "4002002040000000000", hexnat% "3000000000000000000", 576460752303423488]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fafeffeddbb800000000", hexnat% "10000004000000000", 4538783999459328, hexnat% "5000000000000000000", 567347999932416]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f8fed9eddbb800000000", 4503874505277440, hexnat% "10600000000000000", hexnat% "7000000000000000000", 2306410357213626368, 35184372088832]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "7fffffffffff800000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c30 c23
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c32 c27
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fb7dffefffd800000000", 4503737066323968, hexnat% "20000000000000000", hexnat% "4800000000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f97dffedbbd800000000", hexnat% "20000002000000000", 4573968371548160, hexnat% "6800000000000000000", 567347999932416]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c36 c35
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffb9ff8ffcd800000000", 13510936321064960, 18017697044365312, hexnat% "40000000000000000", hexnat% "420000000000000000"]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f97bffbe79f800000000", hexnat% "40000020000000000", hexnat% "4000000040000000000", hexnat% "2800000000000000000", 18436610974547968]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f93fff8e3bd800000000", hexnat% "c00000000000000000", 13581305065242624, hexnat% "6000000000000000000", 4398046511104, 18436610974547968]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c41 c38
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c42 c37
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f87bc7bc5af800000000", 18437710486175744, hexnat% "41800000000000000", hexnat% "7800000000000000000", 2306410357213626368, 35184372088832]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fa38cb7ff9f800000000", hexnat% "41000020000000000", hexnat% "5800000000000000000", hexnat% "400080000000000000", 2305847407260205056, hexnat% "30400000000000000"]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f8f8c32c989800000000", 4609290182590464, 54327969040039936, hexnat% "30400004000000000", hexnat% "41800000000000000", hexnat% "7000000000000000000", 2306410357213626368]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c47 c44
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c48 c43
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c49 c31
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c50 c22
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c51 c21
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c52 c20
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c53 c19
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c54 c18
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c55 c9
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c56 c8
  c57
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007
def vertexColumn : Fields := ⟨10, hexnat% "cd23c2f3322e87ac99a6c5a364d8b63392e2b89e0fb318e4b91e725a95a5c56558d5352d4cd8b52d2b61d2743dc8da3c4e334ccb31cccb4ac6b26f0761d4731e2749ca785d1725c3743c2f170aa1683a1588e1381ec86312a4590e705854552344d0752328c530cc8b12c2b06d0721c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db49b6db4d249249b49369b49249a492492493492492249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c1 c2
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f3ff9ffffffffff00000000", hexnat% "6000000000000000000", hexnat% "c000000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f3fef7ffffff9fd00000000", 6605659701248, hexnat% "4000800000000000000000", hexnat% "8010000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f3f6bf7fffff9c500000000", hexnat% "4080000001000000000", hexnat% "90000000000200000000", hexnat% "c000000000000000000000", 6768868458496]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c9 c0
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f3ff973fbe121c700000000", hexnat% "c0400003000000000", hexnat% "6000018000000000000", hexnat% "4000800002400000000000", hexnat% "8000000004800000000000", 33019708571648]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c12 c0
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fbffc7fbfb931fd00000000", hexnat% "4000800002400000000000", 15401752723456, 4611686018427387904, 19281035904679936, hexnat% "3000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c0 c14
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fbf67ffffffe1ff00000000", hexnat% "4018000000000000000000", 32985348833280, hexnat% "80000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fff7bf7ffffe1e700000000", hexnat% "4080000001000000000", hexnat% "80000000020000000000", 30820685316096]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fbfe131fdffe3c700000000", hexnat% "2800000000000000000", hexnat% "4018000000000000000000", hexnat% "44a0000000000000000", 31026843746304, hexnat% "40200000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f7febf3ff7fefdf00000000", hexnat% "8010000000000000000000", hexnat% "c0000002000000000", hexnat% "4000080000000000000", 17592186044416]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f3fe8f3f96dafdf00000000", 40550126271332352, hexnat% "4000000002400000000000", hexnat% "c0400000000000000", hexnat% "6000000000000000000", hexnat% "8011000200000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fff79b5fffee9ef00000000", hexnat% "80000001020000000000", hexnat% "6020000000000000000", 22058952032256, hexnat% "480000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffff9f7ff65e1ef00000000", 33054068310016, hexnat% "4000098000000000000", hexnat% "80000000000000000", hexnat% "2000002000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fbff9b5ff65a36b00000000", hexnat% "4000000002400000000000", 31404800868352, hexnat% "4400080000000000000", hexnat% "a0000000000000000", hexnat% "2000018000400000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c28 c25
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffffff3bf7ee1c500000000", 36046526643961856, 4611969701017288704, hexnat% "c0000001000000000", 13228499271680]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffffa73fb21a3c700000000", hexnat% "c0400003000000000", hexnat% "1800000400000000000", hexnat% "4000098000000000000", 30820685316096, 19703248369745920]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c31 c30
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f3f6a77bffebfff00000000", hexnat% "80004001000000000000", hexnat% "4080000000000000000", hexnat% "1800000400000000000", hexnat% "c010000000000000000000"]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f3fe831fa21834700000000", hexnat% "c010000000200000000000", hexnat% "e0400002000000000", hexnat% "4400080000000000000", 31439160606720, 22025416927608832, hexnat% "3800110000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c35 c32
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c36 c29
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c37 c24
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c38 c21
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c39 c16
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c40 c13
  c41
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018
def vertexColumn : Fields := ⟨10, hexnat% "370da8eb26c58d68d8ce4b8ae1b83e36639c9715356353352d2b46d0f713a4e5334e3332e2b4acab1ae1b0ef0761d4731e2729c6785d170dd0f2705cc889a16926258562384e0b81ec849916525254552344d0b41dc0e2348e1324c5322c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "49a69a4924d34d2492492492492492492489249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100200021100000000000", hexnat% "3e000004000000000", hexnat% "1f000000000000000000", 2234913514105864192, 261134011596800, 61361544922923008, hexnat% "c40880000000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019
def vertexColumn : Fields := ⟨10, hexnat% "32c3723cca8da4eb26358b61db0e33a2e4b83eca4d98e539c94d58d4b51d70da364d3362d4b61d0f72334d332cc73c2d8b52ccb8ad2b46c3bc1cc789d2729c6783d0f0bc9c1709a16896158362384e07b21c249916625254550d60d2344d0752324c530cd0b22c4b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "34da6d24d36926d2492492692492492692692492449249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93a71ef6f177f800000000", 3940649673949184, hexnat% "200100000000000000", hexnat% "10000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93a71ef6b1563800000000", 3975834046038016, hexnat% "210000010000000000", 18015223143202816, 72057594037927936]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c2 c0
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93a71e36f777f800000000", 74309393851613184, hexnat% "1c000000000000000", hexnat% "200000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93a71632f7753800000000", 74311592874868736, hexnat% "1c400000000000000", hexnat% "8000000c000000000", hexnat% "200000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c6 c4
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93a51e22f117f800000000", 4046202790215680, hexnat% "2200100000000000000", hexnat% "1d400000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "92253ff68117f800000000", hexnat% "180000000000000000000", 4046202790215680, 31525197391593472, hexnat% "2000100000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "92273e33c957f800000000", hexnat% "180000000000000000000", 1724034232352768, 13510798882111488, hexnat% "1c400000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93251c22a116b800000000", 4046202790215680, hexnat% "1d400000000000000", hexnat% "80020010004000000000", hexnat% "2200100000000000000", 18015498021109760]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c15 c3
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2608f74f77f800000000", hexnat% "210000000000000000", 49539595901075456, hexnat% "160000000000000000", hexnat% "380000000000000000000", hexnat% "9001000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93a11e26f137f800000000", 4011018418126848, hexnat% "1d000000000000000", hexnat% "2200100000000000000", hexnat% "4000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "92a73b37df77f800000000", 13835058055282163712, hexnat% "100040020000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "922731378f74f800000000", 13835058055282163712, hexnat% "180000000000000000000", 31526296903221248, hexnat% "e0000020000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93a73f37b137d800000000", 18084767253659648, 13835058192721117184, 3940649673949184]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93a33f37f137d800000000", hexnat% "4000000400000000000", 13835058192721117184, 3940649673949184]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "92a339f7af77b800000000", hexnat% "104000000000000000000", 22518273014759424, hexnat% "60000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "92a33f37f977d800000000", hexnat% "104000000000000000000", 13835058192721117184, 1688849860263936]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93a33f37a9379800000000", 22518273014759424, 13835058192721117184, hexnat% "4000000400000000000", 1688849860263936]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c27 c24
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c28 c23
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c29 c22
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "92233e36f137c800000000", hexnat% "184000000000000000000", 74379762595790848, hexnat% "1c000003000000000", 1688849860263936]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93233c26a1348800000000", hexnat% "84000000000000000000", 4011087137603584, hexnat% "1d000002000000000", hexnat% "20010004000000000", 90075291082293248]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c33 c30
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c34 c21
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c35 c18
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "232f134807e800000000", hexnat% "384000000000000000000", 49592372459208704, 16429131509367046144, 2040693581152256, hexnat% "9000100000000000000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93a51e26f107f800000000", hexnat% "1d000000000000000", hexnat% "2200100000000000000", 1811995162574848, 2251799813685248]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93271436f7779800000000", 74309531290566656, hexnat% "1c000000000000000", hexnat% "280000000000000000", hexnat% "80020000004000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93a51027f177c800000000", hexnat% "e0000000000000000", 3940855832379392, hexnat% "2211000000000000000", 13835058055282163712]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93251426e1168800000000", hexnat% "80020010004000000000", hexnat% "1d000002000000000", 4046271509692416, hexnat% "2200100000000000000", hexnat% "80000010000000000"]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c42 c39
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c43 c38
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "802329017857d800000000", hexnat% "384000000000000000000", 2005646648016896, hexnat% "160600000000000000", hexnat% "1000002080000000000000", 14987979559889010688]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93a51e20f137f800000000", 4011018418126848, hexnat% "2200100000000000000", 15420325124116578304, hexnat% "10000000000000000"]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93a71ef7f177e800000000", hexnat% "210000001000000000", 3940649673949184]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93271ef6e177a800000000", hexnat% "200100000000000000", hexnat% "80000010004000000000", 3940718393425920, hexnat% "10000000000000000"]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c48 c47
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "92a73b33df77f800000000", hexnat% "100040020000000000000", 14123288431433875456]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "92273133f977c800000000", 1689056018694144, hexnat% "e0400000000000000", hexnat% "180000000000000000000", 13835058055282163712]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c51 c50
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93271422a1378800000000", hexnat% "80020010004000000000", 4011087137603584, 90071992547409920, hexnat% "281000000000000000", hexnat% "1c400002000000000"]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c53 c52
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c54 c49
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c55 c46
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9023200100030800000000", hexnat% "384000000000000000000", 4327746486403072, 67571586596601856, hexnat% "1f400002000000000", hexnat% "1e0200000000000000", 5222680231936]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c57 c56
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c58 c45
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c59 c44
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c60 c37
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c61 c36
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c62 c17
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c63 c16
  c64
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record019
