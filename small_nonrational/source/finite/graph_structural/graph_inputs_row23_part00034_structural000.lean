module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00034Data
public import GraphInputsRow23Part00034Frames
public import GraphInputsRow23Part00034Leaves
public import GraphInputsRow23Part00034Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002
def vertexColumn : Fields := ⟨10, hexnat% "3725635a36538ce4b85eac4f16a4e9364b9a56558d4b56354d4b4ad2745dc8e5334d332cc7352ccb8acab1ac5b0ef0791d4731e2749d1725c3783c8f0bc1f350cc8c92a858564384e346312c4c94a4a931615254554348d1362348e1314c3342c4b0ae0741c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "492492492492492492492492492492492492489249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "65c7c3fddfffc00000000", hexnat% "800800000000000000000", 9570149208162304, hexnat% "a0000000000000000000", hexnat% "10000c000000000000000", hexnat% "3020000000000000000", hexnat% "10000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e5df436c37ffc00000000", 652036783550234624, hexnat% "202c000000000000000", hexnat% "120080000000000000000", hexnat% "80010020000000000000", 4503599627370496]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41c3c14817ffc00000000", hexnat% "a0000020000000000000", hexnat% "10000c000000000000000", hexnat% "a40000000000000000000", 669488232106295296, hexnat% "32000000000000000", hexnat% "800210000000000000", hexnat% "3400004000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24c7c0fdca9d400000000", hexnat% "500000000000000000000", hexnat% "3000002000000000000", hexnat% "810803001000000000000", 94729798680576, hexnat% "a0000020000000000000", hexnat% "3c000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2d343fbbffffc00000000", hexnat% "800800000000000000000", 306244774661193728, hexnat% "1200c0000000000000000", hexnat% "400100000000000000000", hexnat% "c200000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "97c379fffffc00000000", hexnat% "a40000000000000000000", hexnat% "1200c8000000000000000", hexnat% "8200000000000000000", hexnat% "400100400000000000000", 144115188075855872]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9303d0a57ffc00000000", hexnat% "240000210000000000000", hexnat% "500000400000000000000", 669488232106295296, hexnat% "200c0000000000000000", hexnat% "302000000000000000", hexnat% "800c00000000000000000", hexnat% "c000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24343cbbeb8bc00000000", hexnat% "a0000000000000000000", 78340203479040, hexnat% "c000040000000000000", hexnat% "810803001000000000000", hexnat% "500000400000000000000", hexnat% "3c0000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c10f03ffffffc00000000", hexnat% "240000000000000000000", hexnat% "c040000000000000000", hexnat% "80010000000000000000", hexnat% "3024000000000000000", hexnat% "120088000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4c033fdfffffc00000000", hexnat% "1200c0000000000000000", hexnat% "200000200000000000000", hexnat% "3400000000000000000", hexnat% "c000000000000000000", hexnat% "810800000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400310dcffffc00000000", hexnat% "a0000020000000000000", hexnat% "80c0000000000000000", hexnat% "10000c000000000000000", hexnat% "3020000000000000000", hexnat% "240001210000000000000", hexnat% "4c02000000000000000", hexnat% "810000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6549416d539d400000000", hexnat% "8280000000000000000", hexnat% "800402000800000000000", 576537752477106176, hexnat% "3024000000000000000", hexnat% "80010020002000000000", 74872343805034496, hexnat% "120008000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "af09132b579bc00000000", hexnat% "500000400004000000000", hexnat% "3024000000000000000", hexnat% "c240000000000000000", hexnat% "400000800000000000", 669347494617939968, hexnat% "88000060000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80030beefffc00000000", hexnat% "200c000000000000000", hexnat% "1200c0000000000000000", hexnat% "240001010000000000000", hexnat% "400100400000000000000", hexnat% "c200000000000000000", hexnat% "1c02000000000000000", hexnat% "810000001000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a0018abfff7c00000000", hexnat% "3024000000000000000", hexnat% "a50001000000000000000", hexnat% "8000140000000000000", hexnat% "500000400000000000000", hexnat% "4242000008000000000", hexnat% "c00000000000000000", hexnat% "180000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2d18152b739bc00000000", hexnat% "2028000000000000000", 576537992995274752, hexnat% "800402000800000000000", hexnat% "c240000000000000000", hexnat% "400100400000000000000", 92323792361095168, hexnat% "120080000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c00102b4393000000000", 576538027355013120, hexnat% "600100000008000000000", hexnat% "200000a800000000000", hexnat% "c240000000000000000", hexnat% "1026000000000000000", hexnat% "120088000000000000000", hexnat% "810c01001000400000000", 378302368699121664]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c23 c20
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c24 c19
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c25 c18
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c26 c17
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c27 c16
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c28 c11
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c29 c10
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c30 c5
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c31 c4
  c32
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003
def vertexColumn : Fields := ⟨10, hexnat% "368d6538ce4b85eac4f1366394e4b91e725a95a5394d58d4b5534cd8b4ad1b45d0f69394e332cd4b32d2b86d1b26c3bc1e8761e4751e2749ca785c9715e0f23c2f07d2c3485a3190e138d18c4b14a4590e4c5895252950d1342d30e1324c5342c4b06e0741c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "492492492492492492492492492492492492492449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6500f87babe7f80000000", hexnat% "909005000000000000000", hexnat% "2800001400000000000", hexnat% "24000040000000000000", hexnat% "702800000000000000", hexnat% "80000004018000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "477ff3e20007880000000", 126874845752328192, hexnat% "908004008000200000000", hexnat% "280008000000100000000", 69836168232960, 5910974510923776]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2807df0747fd780000000", hexnat% "2800a00000000000000", hexnat% "35000000000000000000", 109071553475379200, hexnat% "908000008000800000000", hexnat% "440020400002000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6400787d2bf7f80000000", hexnat% "909005008000000000000", hexnat% "2000005400000000000", hexnat% "80000020008000000000", hexnat% "782800000000000000", hexnat% "34800000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "467773645417980000000", hexnat% "10880800000000000000", hexnat% "280008000000000000000", hexnat% "908004008800200000000", 68736656605184, 117656540265054208, 4503599627370496]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "477ffbe04407980000000", hexnat% "280000000000000000000", hexnat% "908004008800200000000", 69836168232960, 5348024557502464, 135107988821114880]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "dfd0fdfeec7fb80000000", hexnat% "2800001000000000000", hexnat% "702000000000000000", hexnat% "200000010000400000000", 61572651155456]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9bd8fdfeec7fb00000000", hexnat% "440000000000080000000", hexnat% "2000001000000000000", hexnat% "702000000000000000", hexnat% "200000010000400000000", 61572651155456]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d490fde68867b80000000", hexnat% "34800000000000000000", 109001184731201536, hexnat% "280000000000000000000", hexnat% "702000018000000000", 61589831024640, hexnat% "2000004000000000000", 4503599627370496]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a78343e7c1f100000000", hexnat% "18040000000000000000", hexnat% "783800000000000000", hexnat% "200008010020680000000", hexnat% "d40000008000800000000", 65970697666560, 288230376151711744]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fff8753efc7fb00000000", 61591978508288, 9516106012633858048, hexnat% "782800000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f590f5268867a00000000", 109001186878685184, hexnat% "80008004008100000000", 62689342652416, 292733975779082240, hexnat% "26800000000000000000", hexnat% "702800000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "540074648007880000000", hexnat% "280008000000100000000", hexnat% "783800000000000000", hexnat% "27800000400000000000", hexnat% "808000080800000000000", 5910974510923776, hexnat% "10000120000000000000", 69844758167552, 562949953421312]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c19 c4
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006
def vertexColumn : Fields := ⟨10, hexnat% "8f13a398d61d8ce8b92e2b86e8791e2785e0fb29c66394e66539655356351d68d3352d2b46d4749d1743d58ce354cd34cc7362ccb8acab1ae1b26c5b0ee2749ca785d1725c3783d0f13e2c8712a468c6198562382e07a294a619464c589465854558348d0b41d30d2318d1314d0b22c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "492492492492492492492492492492492492492492491249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fec7f9ffd337d1e000000000", 2308129993399468032, hexnat% "60000000a0000000000", hexnat% "3800000000000000000000", 54043195528445952, hexnat% "10000000000040000000000", 864691128455135232]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fecf7dffffffdfe000000000", hexnat% "2000000000000000000", hexnat% "80000000000000000000", hexnat% "3000000000000000000000", hexnat% "10000000000200000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fecf7dffdbffdbe000000000", 2305878193585782784, hexnat% "2000400000000000000", hexnat% "80000000000000000000", hexnat% "3000000000000000000000", hexnat% "10000000000040000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ee83fdffd337d9e000000000", 2308129993399468032, hexnat% "3c00000000000000000000", 54043195528445952, hexnat% "100002000400020000000000", hexnat% "14000000000000000000000", 576465150349934592]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a811fffd03058e000000000", hexnat% "e0000004800000000000", hexnat% "802200000000000000000000", 2524303875024879616, hexnat% "144c00000000000000000000", 54887620458577920, hexnat% "411000000000000000000000", 864697725524901888]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c84675edeb09ffe000000000", hexnat% "180000000000000000000", 59109745109237760, hexnat% "208008001000000000000000", hexnat% "140800000000000000000000", hexnat% "2000400000000000000", hexnat% "22000000024000000000000", hexnat% "11000120000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6451ffdc0697fa000000000", hexnat% "380000000000000000000000", hexnat% "e0020004800000000000", 4395513236313604096, 41095621477662720, hexnat% "ba00000000000000000000", hexnat% "c00000000200000000000000", hexnat% "10000000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4649fefc04d7fa000000000", hexnat% "380000000000000000000000", hexnat% "160100020800000000000", 4395513236313604096, 41095621477662720, hexnat% "38a00000000000000000000", hexnat% "c00000000200000000000000", hexnat% "1000000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fd4761fff7fbf1e000000000", hexnat% "1e000000000000000000", hexnat% "80000004000000000000", 576476145466212352, hexnat% "b800000000000000000000", hexnat% "20000000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d6d867fffffffe000000000", hexnat% "208008000000000000000000", hexnat% "11800000000000000000", hexnat% "820200000000000000000000", hexnat% "401000000000000000000000", hexnat% "60000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3d45003db7fbf16000000000", 576476145466212352, hexnat% "e0024004000000000000", hexnat% "800001400000008000000000", hexnat% "1e800000000000000000", hexnat% "ba00000000000000000000", hexnat% "400000000000000000000000", hexnat% "20000000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "de2e7fedcf4bffe000000000", 50665495807918080, 3458764513820540928, hexnat% "180000000000000000000", hexnat% "20c000000000000000000000", hexnat% "11000120000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "dd1e67ffcfcbffe000000000", hexnat% "18000000000000000000", 3463268113447911424, hexnat% "180000000000000000000", hexnat% "20c000000000000000000000", hexnat% "22000000024000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f58d1fbdfcffffe000000000", hexnat% "3000020000000000000000", hexnat% "24200000000000000000000", hexnat% "40400000000000000000", hexnat% "a0000000000000000000", hexnat% "80000000300000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fc4e67adcfffffe000000000", 3458764513820540928, hexnat% "520000000000000000", hexnat% "18000000000000000000", hexnat% "180000000000000000000", hexnat% "b000000000000000000000", hexnat% "30000000000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "df1df67fcc7fffe000000000", 180143985094819840, 3530822107858468864, hexnat% "a200000000000000000000", hexnat% "204000000000000000000000", hexnat% "1800000000000000000", hexnat% "8000000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "df2de63fecffffe000000000", hexnat% "1400000000000000000", hexnat% "18800000000000000000", hexnat% "9200000000000000000000", hexnat% "204000000000000000000000", 216172782113783808, 1152921504606846976]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "dc0e77fdcfffffe000000000", 3458764513820540928, hexnat% "180000000000000000000", hexnat% "208008000000000000000000", hexnat% "34000000000000000000000", hexnat% "3000020000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "dc0c477fcc7b7fe000000000", hexnat% "18800000000000000000", hexnat% "20000280800000000000", 3530822107858468864, hexnat% "20c000000000000000000000", hexnat% "180000000000000000000", hexnat% "3000000004000000000000", hexnat% "30200000000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c26 c21
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c27 c20
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c28 c19
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c29 c18
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c30 c17
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fe77e19fcbbfcfe000000000", hexnat% "600000000000000000", hexnat% "1e000000000000000000", 1459166279268040704, 2305895785771827200, hexnat% "18800000000000000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e75eaffc8ffdfe000000000", hexnat% "15000000000000000000", hexnat% "300000000000000000000000", 3819052484010180608, hexnat% "18a00000000000000000000", hexnat% "c00000000200000000000000", 35184372088832]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ef1f83ff8ffffe000000000", hexnat% "800001400000000000000000", hexnat% "6800000000000000000", hexnat% "100c00000000000000000000", 360287970189639680, hexnat% "410200000000000000000000", 144115188075855872]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a31e03fc8bfdfc000000000", hexnat% "800001400000000000000000", 2522050975699566592, hexnat% "1e800000000000000000", 1459166416706994176, hexnat% "410200000000000000000000", hexnat% "344400000000000000000000", hexnat% "8800000000000000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c36 c33
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c37 c32
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fd77e5dfc33fafe000000000", 54043195528445952, 4323455642275676160, hexnat% "a200000000000000000", hexnat% "10000000500000000000", hexnat% "28800000000000000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "931e45fc03fafc000000000", 3098476543630901248, hexnat% "400000000080000000000000", hexnat% "11800000400000000000", hexnat% "820200000000000000000000", hexnat% "100802000400002000000000", hexnat% "44400200040000000000000", hexnat% "208008001000100000000000"]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e983e99ffbffb7e000000000", hexnat% "600000000000000000", hexnat% "16000000000000000000", hexnat% "3c00000000000000000000", hexnat% "100000000400000000000000", hexnat% "20000000000480000000000", hexnat% "44000000000000000000000"]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ecc279fffbddffe000000000", hexnat% "6000000000000000000", hexnat% "180000000000000000000", hexnat% "3c00000000000000000000", hexnat% "100000000402000000000000", hexnat% "30000000020000000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d81be39fefffb7e000000000", hexnat% "600000000000000000", hexnat% "208008001000000000000000", hexnat% "14000000000000000000", hexnat% "34000000000000000000000", hexnat% "2000000000480000000000", hexnat% "40400000000000000000000"]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c803e18eeb9fb74000000000", hexnat% "510000008000000000", hexnat% "1e000000000000000000", 1459166416706994176, hexnat% "19800000000000000000000", hexnat% "22000000020480000000000", hexnat% "344400000000000000000000", hexnat% "200000000000000000"]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c45 c44
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c46 c43
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c47 c42
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "454802ebfdfff6000000000", hexnat% "160104020000000000000", hexnat% "380000000000000000000000", hexnat% "410000008000000000", hexnat% "1e800000000000000000", hexnat% "38a00000000000000000000", hexnat% "c00001000000000000000000", hexnat% "2000000000000000000000"]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17fe1f9fe62f7fe000000000", hexnat% "600000000000000000", hexnat% "200000001010000000000000", 648659083829706752, hexnat% "1e0000000000000000000", 54043195528445952, hexnat% "c80000000000000000000000"]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37c1fbfef2fffe000000000", 58546795155816448, hexnat% "208000001000000000000000", hexnat% "800040400000000000000000", hexnat% "1a0000000000000000000", hexnat% "1c0000000000000000000000", hexnat% "400200000000000000000000"]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2681f9fe22d7fa000000000", 2089670227099910144, hexnat% "600000000000000000", hexnat% "1e0000000800000000000", 59110019987144704, hexnat% "19200000000000000000000", hexnat% "3c0400000000000000000000", hexnat% "c00000000000000000000000"]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c52 c51
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c53 c50
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "27fff85fd23ff7e000000000", 54043195528445952, 3242591731706757120, hexnat% "2a00000000000000000", hexnat% "5000000080000000000", hexnat% "180000000000000000000000", hexnat% "c00000000000000000000000"]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fe0a1f961f53e000000000", 2315026130328879104, 54043195528445952, hexnat% "604000000000000000", hexnat% "15800000000000000000", hexnat% "1e0000000000000000000", 576473946442956800, hexnat% "c80000000100000000000000"]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c56 c55
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17fff25fc63fe7e000000000", 54043195528445952, 4107282860161892352, hexnat% "8200000100000000000", hexnat% "5800000080000000000", hexnat% "280000000000000000000000", hexnat% "c00000000000000000000000"]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17fe027fc60f43e000000000", hexnat% "1e0000000800000000000", hexnat% "200008001010100000000000", 54043195528445952, 576473946442956800, hexnat% "15800000000000000000", 2314885392840523776, hexnat% "c80000000100000000000000"]
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c59 c58
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ecca7deef3ffffe000000000", 864691128455135232, hexnat% "180000000000000000000", hexnat% "3400000000000000000000", hexnat% "100002010000000000000000", hexnat% "30000100000000000000000"]
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c88bf5cec30ddb8000000000", 4323455642275676160, hexnat% "22000000020000000000000", 59110157426098176, hexnat% "a200000000000000000", hexnat% "344400000000000000000000", hexnat% "11000100000240000000000", hexnat% "10000000000000000"]
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c62 c61
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3a9e11fe2bfebc000000000", 936753120539574272, hexnat% "800000400000000000000000", hexnat% "401200000000000000000000", hexnat% "1e800000000000000000", 1170953632741326848, hexnat% "3c4400000000000000000000", hexnat% "200000000000000000"]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "eeea79eef3ffffe000000000", 864691128455135232, hexnat% "6010000000000000000", hexnat% "180000000000000000000", hexnat% "1400000000000000000000", hexnat% "10000100000000000000000", hexnat% "100000000000000000000000"]
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "edda79aeffffffe000000000", hexnat% "510000000000000000", hexnat% "6000000000000000000", hexnat% "180000000000000000000", hexnat% "2400000000000000000000", hexnat% "20000000000000000000000", hexnat% "100000000000000000000000"]
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e4c8192eb2ffffe000000000", 936748722493063168, hexnat% "514000000000000000", hexnat% "6800000000000000000", hexnat% "3600000000000000000000", hexnat% "30000000000000000000000", hexnat% "1e0000000000000000000", hexnat% "180000000000000000000000"]
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c67 c66
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c68 c65
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88010ebf2d530000000000", hexnat% "1e800000000000000000", hexnat% "1e0004000800000000000", 59110157426098176, hexnat% "610000008000000000", hexnat% "22000000000080000000000", hexnat% "3c4400000000000000000000", hexnat% "11000100000240000000000", hexnat% "c00200000000000000000000"]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c70 c69
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c71 c64
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c72 c63
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c73 c60
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c74 c57
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c75 c54
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c76 c49
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c77 c48
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c78 c41
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c79 c38
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c80 c31
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c81 c16
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c82 c11
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c83 c10
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c84 c9
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c85 c8
  c86
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012
def vertexColumn : Fields := ⟨10, hexnat% "3d0f2398d6c3a2e47a394e4b91e6a5994d52d475c352d2b46d4743d38d9354cb31cf0b8ae1b26c5b0ef07a1d8791d4789ca719d1725c5723c4f0bc1f3c0e48b0d2468c68390e384d12c4718a5190e4c5894a51960d4342d30d1324c5382d0b06e0741c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "12492492492492492492492492492492492489249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28000040000400000000", hexnat% "7801002000000000000", 440226863575465984, hexnat% "61c000000800000000", hexnat% "1900009a00e0000000000", hexnat% "2401c200001c000000000", 545563925807104, hexnat% "20000000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record012
