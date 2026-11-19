module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00075Data
public import GraphInputsRow24Part00075Frames
public import GraphInputsRow24Part00075Leaves
public import GraphInputsRow24Part00075Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record005
def vertexColumn : Fields := ⟨10, hexnat% "2e4b529c6729a2e87aa9a66c5a9695956a392e2b86e8791e2785eb44f1664b91e6c53969565655554d56352d1b51d2745da4e5354cb31cd2b2ac6b26c5b0ee8791d4749ca785d1725c5723c4f07cac9491a918664382e2a519264a51950d2342d18d1314d0b0ac1b41c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db69b4da49a6db49b4db6d249369349249349269a491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fb66fbfd9fdf3f6000000", hexnat% "40000000000c00000000", 4621256167769767936, hexnat% "1100000000000000000", hexnat% "800000020000000000", hexnat% "8000004000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "7ffffffffffffffe000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c2 c3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c2 c4
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffeff7cfffffbe000000", hexnat% "100000000040000000", 13510798882111488, 576460752303423488]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff6eff7ffbff3be000000", 576460752303423488, 18253611008, hexnat% "8000000400800000000", hexnat% "1100000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fb66f3fd99ff3b6000000", 105553116266496, hexnat% "1800000000008000000", hexnat% "40000000000c00000000", 13844628204490326016, hexnat% "8100004000040000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff6af7fdbbffffe000000", hexnat% "8000000400000000000", hexnat% "1400000000000000000", 9233505136016359424, hexnat% "100000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffe2f37c1fb5ffe000000", 583216151744479232, hexnat% "1c00000000000000000", 13835058742476931072, hexnat% "100004040000000000", 9570149208162304]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fbe2ff7c1fffcbe000000", 15199648742375424, 578712565002010624, hexnat% "40400000000000000000", hexnat% "1800000000000000000", hexnat% "100000000040000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fb62f3fd99177a0000000", 114349477724160, hexnat% "40400000000804000000", 13844628204490326016, hexnat% "1100000040002000000", hexnat% "800000028008000000", hexnat% "8000004000040000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record015
def vertexColumn : Fields := ⟨10, hexnat% "2f2e23c99a2e9564d8b61da4e2b91e2785e0fae1b44f1a6599964b9555352d64d2b49d1743db0ea398ce364d5334d332cc73c2d8b92cab46c9b16c3b91d4749ca745c9715c3783c8f13c2f07c744728a1990e2c471a251926465454550d50d0768390ca318e0b42c8b41c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db4da6db6926924da49249b6d249249b4924d2492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [10647407759705767936, hexnat% "340000040000000000", hexnat% "410400000000000000", hexnat% "20800000a08000000", hexnat% "90000000080000000000", 211106232532992]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "341000041000000000", 252236763504836608, hexnat% "400043000100000000", hexnat% "90000000080a08000000", hexnat% "38c00000000000000", 965025464320, 228699492319232]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record015_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record016
def vertexColumn : Fields := ⟨10, hexnat% "3d0bc1f2e23caaa9a93a2e87ab18e665956358b61da8e938ae1b91e2785e0fae1b44f1aa669a66594e4b91e6c539595554d52d475a364d2b46d2745d0f6c3a8e6338d9354cd34ccb31cf0ba2e4b8ad2b2ac6b46c9b16c3ba1d8791d4731ca719d1725c570de0f23c4f0bc1f4710e2c47146439454951550d0768390ca318e0b42c2b41c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6db6db69b6da6db49369249b6d24924db692492493692492492692489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000000006024070400000", hexnat% "10e000800000000000000", hexnat% "7c3000000000000000", 545357842874368, 540431963874394112, 257748369408, 13200581984256]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record016_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record020
def vertexColumn : Fields := ⟨10, hexnat% "b92d43d19c2f07cb8ad23c99a2e87ab1aa6998e6a599695956358b61da8e6392e2b86e4789e1783e2e479a9665a5655554b51d68d4b4ad1b49d1743da8e63a4e5354cb31ce8b4acab1ac9b16c3bc1e8791d4789d2729c6785d1725c570de0f43c8f13c2f07cac4709c2a91a2691991465454554342d0764318d1314d0b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6936da4db6db6db6db4d26db69a4d349249a6934d24926d36da69a6d3691249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b05a216882152600000", 576495936675512320, hexnat% "4100000000000000000000000", 36030996042219520, 360309960422195200, hexnat% "2080000000040010000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "410000b000e40392152600000", 72061992084439040, 6335385999245312, hexnat% "5a080000000000000", hexnat% "2080000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6180003008dc0150100600000", 35184405643264, hexnat% "52200000000000000", hexnat% "8000000002050000000", 5781232138846208, 562949953421312]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2180000002f42bf0102600000", hexnat% "4000003000000000000000000", 5629637241602048, 9259400834947481600, hexnat% "8000000000000000000", hexnat% "50000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6180003000542370100600000", 576460752336977920, 5779033115590656, hexnat% "8000000002050000000", hexnat% "52280000000000000", 9223372036854775808]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [72124668546383872, 1026820715040473088, hexnat% "4100003000000000000200000", 6335386267680768, hexnat% "5a080000000000000", hexnat% "2080008000000000000000000", 138546249728]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record030
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record030
def vertexColumn : Fields := ⟨10, hexnat% "15c4f07caa95a4e8ba1eac665956359362d8765392e1b91e1783eb46a9a6659565392e479b1595554d54d4755352d1b51d1743db0ea364d5334d332cc73c2e8b52e2b4acab1ad1b26c5b0ee8761e4751cc749c6745c9715c3743c4f0bc1f2d24a298b1925191643929515254550d68390ca382d0b12c2b41c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6d36db6db69249a4926da4926db4d249249a492492492493249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7400800010000000000", hexnat% "20000000080480f0000000", 216454531968401408, hexnat% "800000100000000000", hexnat% "1f1400000000000000", 270650048512, 818036818837504]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record030_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record030_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record030_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record030_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record030_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record030_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record030_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record030_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record030_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record030

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "bc1f2e2b4a9a66a565592e2b86e4789e17ae1b44f1a65992e479955552d4754b4ad1b49d1743db0ea398ce3c4e9364e5354cd3a2d8b4ac6b86d1b26c5b91d4749ca785d1725c5723c4f07d1c2a8664382ea46512a51926465454554342d0768390ca318d0b22c2b41c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6924db4d24d269249249269a6d249a4d249a692449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 65), (facetIndex 71)]))
 (.leaf ([(facetIndex 76), (facetIndex 77), (facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 56), (facetIndex 57), (facetIndex 62), (facetIndex 64)]))
 (.branch 4
 (.leaf ([(facetIndex 39), (facetIndex 58), (facetIndex 67), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 27), (facetIndex 30), (facetIndex 32), (facetIndex 40), (facetIndex 50), (facetIndex 75)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 28), (facetIndex 36), (facetIndex 37), (facetIndex 53)]))
 (.leaf ([(facetIndex 45), (facetIndex 52), (facetIndex 54), (facetIndex 55)])))
 (.branch 8
 (.leaf ([(facetIndex 59), (facetIndex 60), (facetIndex 61)]))
 (.branch 9
 (.leaf ([(facetIndex 29), (facetIndex 42), (facetIndex 43), (facetIndex 44)]))
 (.leaf ([(facetIndex 34), (facetIndex 35)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "1114000003330020277732266560400006888043055990404854z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 70), (facetIndex 72)]))
 (.branch 2
 (.leaf ([(facetIndex 83), (facetIndex 84)]))
 (.leaf ([(facetIndex 63), (facetIndex 66)]))))
 (.branch 4
 (.leaf ([(facetIndex 85), (facetIndex 86)]))
 (.branch 5
 (.leaf ([(facetIndex 31), (facetIndex 33), (facetIndex 38), (facetIndex 41), (facetIndex 47), (facetIndex 49), (facetIndex 51)]))
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 79), (facetIndex 80), (facetIndex 81), (facetIndex 82)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "d936da001680000804000000008208000201000208z17;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [7, 8, 9]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1, 2]
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [1, 2]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [3]
def grouped3_0022 : List Nat := [3, 4, 5]
def grouped3_0023 : List Nat := [4]
def grouped3_0024 : List Nat := [4, 5]
def grouped3_0025 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record006" 63

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record006" "{\"ridges\":[[9,578],[17,152],[20,592],[21,656],[33,534],[37,578],[39,152],[48,592],[50,656],[51,786],[53,577],[53,578],[55,577],[55,578],[58,152],[65,592],[67,152],[68,152],[69,656],[70,240],[71,592],[71,656],[72,736],[80,534],[80,592],[83,210],[84,736],[86,180]],\"owners\":[[53,577,[20,65,71],[9,37,55,72]],[55,577,[20,65],[9,37,53,71,72]],[9,578,[80,83,84],[37,48,53,55]],[37,578,[83,84],[9,48,53,55,80]],[53,578,[80,83],[9,37,48,55,84]],[55,578,[80],[9,37,48,53,83,84]],[17,152,[74,81,82,86],[39,58,67,68,69]],[39,152,[86],[17,58,67,68,69,74,81,82]],[58,152,[81,82],[17,39,67,68,69,74,86]],[67,152,[74,81,82],[17,39,58,68,69,86]],[68,152,[74,82,86],[17,39,58,67,69,81]],[20,592,[80,83],[48,65,71]],[48,592,[],[20,65,71,80,83]],[65,592,[83],[20,48,71,80]],[71,592,[80],[20,48,65,83]],[80,592,[20,71],[48,65,83]],[21,656,[82,83],[50,69,71]],[50,656,[],[21,69,71,82,83]],[69,656,[83],[21,50,71,82]],[71,656,[82],[21,50,69,83]],[33,534,[80],[]],[80,534,[33],[]],[83,210,[46],[]],[51,786,[],[]],[86,180,[63],[]],[70,240,[],[]],[72,736,[84],[]],[84,736,[72],[]]],\"edges\":[[32,[17,21,31,39,46,49,50,58,63,67,68,69,70,71,74,81,82,83,86]],[34,[20,21,33,41,48,50,51,65,69,71,80,82,83]],[41,[9,20,37,48,53,55,65,71,72,80,83,84]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-15,-14],[-22,-15],[-26,-15],[-35,-7],[-35,-17],[-35,-33],[-36,-35],[-37,-35],[-38,-5],[-38,-6],[-38,-8],[-38,-12],[-38,-20],[-38,-34],[-21,3,26,31],[-23,3,26],[-1,35,38,39],[-10,38,39],[-21,35,38],[-23,35],[-2,33,36,37,40],[-11,40],[-24,36,37],[-27,33,36,37],[-28,33,37,40],[-3,35,38],[-16],[-26,38],[-31,35],[-35,3,31],[-4,37,38],[-18],[-29,38],[-31,37],[-9,35],[-35,9],[-38,15],[-19],[-40,25],[-30],[-32,39],[-39,32],[-41,16,26,31],[-42,5,6,8,12,18,34],[-43,14,20,22,23],[-44,41],[-45,42],[-46,45],[-47,44,46],[-48,43],[-49,48],[-50,47,49],[50],[-15,51],[-32,51],[-38,52],[-39,52],[-25,53],[-9,54],[-13,54],[-35,55],[-37,55],[-53,56],[-52,56],[-56,57],[-51,57],[-51,-56,58],[-55,59],[-54,59],[-54,-55,60],[-59,61],[-60,62],[-57,-62,63],[-58,-61,63],[-63],[2,4,7,11,15,17,18,24,25,27,28,29,30,31,33,36,37,38,40],[3,4,9,13,16,18,19,26,29,31,35,37,38],[1,3,10,16,21,23,26,31,32,35,38,39]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":54,\"b\":46},{\"tag\":\"incompatible\",\"a\":65,\"b\":46},{\"tag\":\"incompatible\",\"a\":80,\"b\":31},{\"tag\":\"incompatible\",\"a\":80,\"b\":49},{\"tag\":\"incompatible\",\"a\":80,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":80},{\"tag\":\"incompatible\",\"a\":83,\"b\":27},{\"tag\":\"incompatible\",\"a\":83,\"b\":30},{\"tag\":\"incompatible\",\"a\":83,\"b\":32},{\"tag\":\"incompatible\",\"a\":83,\"b\":40},{\"tag\":\"incompatible\",\"a\":83,\"b\":52},{\"tag\":\"incompatible\",\"a\":83,\"b\":75},{\"tag\":\"mate\",\"ridge\":577,\"a\":53,\"owners\":[20,65,71]},{\"tag\":\"mate\",\"ridge\":577,\"a\":55,\"owners\":[20,65]},{\"tag\":\"mate\",\"ridge\":578,\"a\":9,\"owners\":[80,83,84]},{\"tag\":\"mate\",\"ridge\":578,\"a\":37,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":578,\"a\":53,\"owners\":[80,83]},{\"tag\":\"mate\",\"ridge\":578,\"a\":55,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":152,\"a\":17,\"owners\":[74,81,82,86]},{\"tag\":\"mate\",\"ridge\":152,\"a\":39,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":152,\"a\":58,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":152,\"a\":67,\"owners\":[74,81,82]},{\"tag\":\"mate\",\"ridge\":152,\"a\":68,\"owners\":[74,82,86]},{\"tag\":\"mate\",\"ridge\":592,\"a\":20,\"owners\":[80,83]},{\"tag\":\"mate\",\"ridge\":592,\"a\":48,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":592,\"a\":65,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":592,\"a\":71,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":592,\"a\":80,\"owners\":[20,71]},{\"tag\":\"mate\",\"ridge\":656,\"a\":21,\"owners\":[82,83]},{\"tag\":\"mate\",\"ridge\":656,\"a\":50,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":656,\"a\":69,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":656,\"a\":71,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":534,\"a\":33,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":534,\"a\":80,\"owners\":[33]},{\"tag\":\"mate\",\"ridge\":210,\"a\":83,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":786,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":180,\"a\":86,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":240,\"a\":70,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":72,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":736,\"a\":84,\"owners\":[72]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[48,65,71],\"full_literals\":[-41,16,26,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[27,30,32,40,50,75],\"full_literals\":[-42,5,6,8,12,18,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[45,52,54,55],\"full_literals\":[-43,14,20,22,23]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-47,44,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-49,48,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-50,47,49],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":46,\"full_literals\":[-15,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":72,\"full_literals\":[-32,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-38,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":84,\"full_literals\":[-39,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":63,\"full_literals\":[-25,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":33,\"full_literals\":[-9,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":41,\"full_literals\":[-13,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":80,\"full_literals\":[-35,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-37,55]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-56,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-55,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-57,-62,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":32,\"owners\":[17,21,31,39,46,49,50,58,63,67,68,69,70,71,74,81,82,83,86]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[20,21,33,41,48,50,51,65,69,71,80,82,83]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[9,20,37,48,53,55,65,71,72,80,83,84]}]}"
  "p cnf 63 78\n-15 -14 0\n-22 -15 0\n-26 -15 0\n-35 -7 0\n-35 -17 0\n-35 -33 0\n-36 -35 0\n-37 -35 0\n-38 -5 0\n-38 -6 0\n-38 -8 0\n-38 -12 0\n-38 -20 0\n-38 -34 0\n-21 3 26 31 0\n-23 3 26 0\n-1 35 38 39 0\n-10 38 39 0\n-21 35 38 0\n-23 35 0\n-2 33 36 37 40 0\n-11 40 0\n-24 36 37 0\n-27 33 36 37 0\n-28 33 37 40 0\n-3 35 38 0\n-16 0\n-26 38 0\n-31 35 0\n-35 3 31 0\n-4 37 38 0\n-18 0\n-29 38 0\n-31 37 0\n-9 35 0\n-35 9 0\n-38 15 0\n-19 0\n-40 25 0\n-30 0\n-32 39 0\n-39 32 0\n-41 16 26 31 0\n-42 5 6 8 12 18 34 0\n-43 14 20 22 23 0\n-44 41 0\n-45 42 0\n-46 45 0\n-47 44 46 0\n-48 43 0\n-49 48 0\n-50 47 49 0\n50 0\n-15 51 0\n-32 51 0\n-38 52 0\n-39 52 0\n-25 53 0\n-9 54 0\n-13 54 0\n-35 55 0\n-37 55 0\n-53 56 0\n-52 56 0\n-56 57 0\n-51 57 0\n-51 -56 58 0\n-55 59 0\n-54 59 0\n-54 -55 60 0\n-59 61 0\n-60 62 0\n-57 -62 63 0\n-58 -61 63 0\n-63 0\n2 4 7 11 15 17 18 24 25 27 28 29 30 31 33 36 37 38 40 0\n3 4 9 13 16 18 19 26 29 31 35 37 38 0\n1 3 10 16 21 23 26 31 32 35 38 39 0\n"
  "79 -41 26 31 0 27 43 0\n80 -42 5 6 8 12 34 0 32 44 0\n81 2 4 7 11 15 17 24 25 27 28 29 31 33 36 37 38 40 0 32 40 76 0\n82 3 4 9 13 26 29 31 35 37 38 0 27 32 38 77 0\n83 1 3 10 21 23 26 31 32 35 38 39 0 27 78 0\n84 3 1 31 57 0 65 64 56 28 57 18 66 55 15 16 30 83 0\n85 35 57 0 65 64 57 56 29 17 26 84 0\n86 57 0 65 66 63 64 54 58 56 39 33 22 85 4 5 6 7 8 23 21 24 34 31 25 81 0\n87 -62 0 86 75 73 0\n88 -60 0 87 72 0\n89 -35 0 88 36 61 59 70 0\n90 -23 0 89 20 0\n91 -31 0 89 29 0\n92 -9 0 89 35 0\n93 39 38 0 89 91 90 26 19 28 41 18 17 83 0\n94 38 0 75 89 91 92 28 33 26 93 42 57 55 64 67 74 71 68 69 62 60 31 82 0\n95 -5 0 94 9 0\n96 -6 0 94 10 0\n97 -8 0 94 11 0\n98 -12 0 94 12 0\n99 -20 0 94 13 0\n100 -34 0 94 14 0\n101 15 0 94 37 0\n102 -42 0 100 95 96 97 98 80 0\n103 -14 0 101 1 0\n104 -22 0 101 2 0\n105 -26 0 101 3 0\n106 -45 0 102 47 0\n107 -43 0 103 104 99 90 45 0\n108 -41 0 105 91 79 0\n109 -46 0 106 48 0\n110 -48 0 107 50 0\n111 -44 0 108 46 0\n112 -47 0 109 111 49 0\n113 -49 0 110 51 0\n114 0 112 113 53 52 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record032
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2d45713c2f07cb495a4e8ba1eac6a9a9665a56558d64d8b61da4e5392e2b86e4789e1783e565392e479b16a565555355352d4759354d4b4ad1b51d2745d0f6c3a8d9354cd34ccb31ce4b52d2b2ac6b46c9b16c3bc1e8761e4751cc789d2729c6745c9715c3783d0f23c4f0bc1f2d11c1703c2c91a1683aa16452950d1342da0e4328d0b12c2b"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "d249a4936db6da6db6d349b6d26db4d24926924db69a4924d269a6db4db6da693249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 52), (facetIndex 101)]))
 (.leaf ([(facetIndex 69), (facetIndex 90), (facetIndex 106)])))
 (.branch 3
 (.leaf ([(facetIndex 20), (facetIndex 42), (facetIndex 49), (facetIndex 51), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 26), (facetIndex 59), (facetIndex 66), (facetIndex 68), (facetIndex 70), (facetIndex 71)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 27), (facetIndex 74), (facetIndex 75), (facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 23), (facetIndex 25), (facetIndex 28), (facetIndex 30), (facetIndex 32), (facetIndex 33), (facetIndex 35), (facetIndex 37), (facetIndex 39), (facetIndex 92), (facetIndex 96)])))
 (.branch 7
 (.leaf ([(facetIndex 29), (facetIndex 80), (facetIndex 82), (facetIndex 84), (facetIndex 85), (facetIndex 86), (facetIndex 93), (facetIndex 94), (facetIndex 95)]))
 (.leaf ([(facetIndex 83), (facetIndex 87), (facetIndex 89), (facetIndex 91)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "40000005db5e78fb6f860249006cb0c0000600090410000080a28a2d1758e8a02000000000000000"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record032" "{\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record032" 71

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record032" "{\"ridges\":[[2,259],[4,578],[10,580],[14,266],[14,274],[18,276],[24,259],[24,261],[29,23],[36,580],[39,774],[43,259],[43,274],[46,259],[47,259],[48,578],[51,305],[53,337],[54,401],[56,578],[60,276],[65,580],[71,401],[73,580],[76,305],[77,337],[81,274],[81,276],[86,526],[89,294],[91,326],[92,534],[93,390],[96,198],[99,274],[100,266],[100,274],[104,276],[105,276]],\"owners\":[[2,259,[29,32,35,37,39,51,53,54],[24,43,46,47]],[24,259,[51,53,54],[2,29,32,35,37,39,43,46,47]],[43,259,[32,35,37,39],[2,24,29,46,47,51,53,54]],[46,259,[29,35,37,39,53,54],[2,24,32,43,47,51]],[47,259,[29,32,37,39,51,54],[2,24,35,43,46,53]],[14,266,[2,24,46,47,84,85],[81,99,100]],[100,266,[2,24,46,84],[14,47,81,85,99]],[4,578,[86,92,96,101],[36,48,56]],[48,578,[92,96,101],[4,36,56,86]],[56,578,[86,92],[4,36,48,96,101]],[24,261,[68,70,71],[8,29,32,35,37,39,60,63,64]],[10,580,[86,92,96,106],[36,65,73]],[36,580,[106],[10,65,73,86,92,96]],[65,580,[92,96,106],[10,36,73,86]],[73,580,[86,92],[10,36,65,96,106]],[14,274,[29,51,53,54,89,91,93],[43,81,99,100]],[43,274,[89,91,93],[14,29,51,53,54,81,99,100]],[81,274,[51,53,54],[14,29,43,89,91,93,99,100]],[99,274,[29,53,54,91,93],[14,43,51,81,89,100]],[100,274,[29,51,54,89,93],[14,43,53,81,91,99]],[18,276,[29,68,70,71,89,91,93],[60,81,104,105]],[60,276,[89,91,93],[18,29,68,70,71,81,104,105]],[81,276,[68,70,71],[18,29,60,89,91,93,104,105]],[104,276,[29,70,71,91,93],[18,60,68,81,89,105]],[105,276,[29,68,71,89,93],[18,60,70,81,91,104]],[29,23,[20,26,27,28],[]],[86,526,[25],[]],[89,294,[32,84],[]],[96,198,[34,90],[]],[91,326,[35,85],[]],[93,390,[37],[]],[39,774,[],[]],[51,305,[68,76],[]],[76,305,[51,68],[]],[53,337,[70,77],[]],[77,337,[53,70],[]],[54,401,[71],[]],[71,401,[54],[]],[92,534,[94],[]]],\"edges\":[[15,[2,14,24,29,32,35,37,39,43,46,47,51,53,54,81,84,85,89,91,93,99,100]],[33,[14,18,29,43,51,53,54,60,68,70,71,76,77,81,89,91,93,99,100,104,105]],[41,[4,10,36,48,56,65,73,86,92,96,101,106]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record032" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record032\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-38,-12],[-38,-13],[-38,-15],[-38,-17],[-38,-36],[-38,-37],[-39,-38],[-41,-38],[-42,-12],[-42,-13],[-42,-15],[-42,-17],[-42,-36],[-42,-37],[-42,-39],[-42,-41],[-43,-38],[-43,-42],[-1,12,13,15,17,18,23,24,25],[-7,23,24,25],[-19,13,15,17,18],[-20,12,15,17,18,24,25],[-21,12,13,17,18,23,25],[-4,1,7,20,21,36,37],[-47,1,7,20,36],[-2,38,42,45,48],[-22,42,45,48],[-26,38,42],[-7,29,30,31],[-3,38,42,45,51],[-16,51],[-28,42,45,51],[-32,38,42],[-4,12,23,24,25,39,41,43],[-19,39,41,43],[-35,23,24,25],[-46,12,24,25,41,43],[-47,12,23,25,39,43],[-5,12,29,30,31,39,41,43],[-27,39,41,43],[-35,29,30,31],[-49,12,30,31,41,43],[-50,12,29,31,39,43],[-12,6,9,10,11],[-38,8],[-39,13,36],[-45,14,40],[-41,15,37],[-43,17],[-18],[-23,29,33],[-33,23,29],[-24,30,34],[-34,24,30],[-25,31],[-31,25],[-42,44],[-14,52],[-48,52],[-40,53],[-51,53],[-6,54],[-23,54],[-24,54],[-25,54],[-9,55],[-29,55],[-30,55],[-31,55],[-10,56],[-33,56],[-34,56],[-8,57],[-11,57],[-13,57],[-15,57],[-17,57],[-42,57],[-12,58],[-36,58],[-37,58],[-38,58],[-43,58],[-44,58],[-39,59],[-41,59],[-53,60],[-52,60],[-55,61],[-54,61],[-54,-55,62],[-61,63],[-60,63],[-60,-61,64],[-60,-62,65],[-57,66],[-56,66],[-59,67],[-58,67],[-58,-59,68],[-67,69],[-68,70],[-66,69],[-66,-67,70],[-63,-70,71],[-64,-69,71],[-65,71],[-71],[1,4,7,12,13,15,17,18,19,20,21,23,24,25,35,36,37,39,41,43,46,47],[4,5,12,19,23,24,25,27,29,30,31,33,34,35,39,41,43,46,47,49,50],[2,3,16,22,26,28,32,38,42,45,48,51]],\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":86,\"b\":29},{\"tag\":\"incompatible\",\"a\":86,\"b\":32},{\"tag\":\"incompatible\",\"a\":86,\"b\":35},{\"tag\":\"incompatible\",\"a\":86,\"b\":37},{\"tag\":\"incompatible\",\"a\":86,\"b\":84},{\"tag\":\"incompatible\",\"a\":86,\"b\":85},{\"tag\":\"incompatible\",\"a\":89,\"b\":86},{\"tag\":\"incompatible\",\"a\":91,\"b\":86},{\"tag\":\"incompatible\",\"a\":92,\"b\":29},{\"tag\":\"incompatible\",\"a\":92,\"b\":32},{\"tag\":\"incompatible\",\"a\":92,\"b\":35},{\"tag\":\"incompatible\",\"a\":92,\"b\":37},{\"tag\":\"incompatible\",\"a\":92,\"b\":84},{\"tag\":\"incompatible\",\"a\":92,\"b\":85},{\"tag\":\"incompatible\",\"a\":92,\"b\":89},{\"tag\":\"incompatible\",\"a\":92,\"b\":91},{\"tag\":\"incompatible\",\"a\":93,\"b\":86},{\"tag\":\"incompatible\",\"a\":93,\"b\":92},{\"tag\":\"mate\",\"ridge\":259,\"a\":2,\"owners\":[29,32,35,37,39,51,53,54]},{\"tag\":\"mate\",\"ridge\":259,\"a\":24,\"owners\":[51,53,54]},{\"tag\":\"mate\",\"ridge\":259,\"a\":43,\"owners\":[32,35,37,39]},{\"tag\":\"mate\",\"ridge\":259,\"a\":46,\"owners\":[29,35,37,39,53,54]},{\"tag\":\"mate\",\"ridge\":259,\"a\":47,\"owners\":[29,32,37,39,51,54]},{\"tag\":\"mate\",\"ridge\":266,\"a\":14,\"owners\":[2,24,46,47,84,85]},{\"tag\":\"mate\",\"ridge\":266,\"a\":100,\"owners\":[2,24,46,84]},{\"tag\":\"mate\",\"ridge\":578,\"a\":4,\"owners\":[86,92,96,101]},{\"tag\":\"mate\",\"ridge\":578,\"a\":48,\"owners\":[92,96,101]},{\"tag\":\"mate\",\"ridge\":578,\"a\":56,\"owners\":[86,92]},{\"tag\":\"mate\",\"ridge\":261,\"a\":24,\"owners\":[68,70,71]},{\"tag\":\"mate\",\"ridge\":580,\"a\":10,\"owners\":[86,92,96,106]},{\"tag\":\"mate\",\"ridge\":580,\"a\":36,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":580,\"a\":65,\"owners\":[92,96,106]},{\"tag\":\"mate\",\"ridge\":580,\"a\":73,\"owners\":[86,92]},{\"tag\":\"mate\",\"ridge\":274,\"a\":14,\"owners\":[29,51,53,54,89,91,93]},{\"tag\":\"mate\",\"ridge\":274,\"a\":43,\"owners\":[89,91,93]},{\"tag\":\"mate\",\"ridge\":274,\"a\":81,\"owners\":[51,53,54]},{\"tag\":\"mate\",\"ridge\":274,\"a\":99,\"owners\":[29,53,54,91,93]},{\"tag\":\"mate\",\"ridge\":274,\"a\":100,\"owners\":[29,51,54,89,93]},{\"tag\":\"mate\",\"ridge\":276,\"a\":18,\"owners\":[29,68,70,71,89,91,93]},{\"tag\":\"mate\",\"ridge\":276,\"a\":60,\"owners\":[89,91,93]},{\"tag\":\"mate\",\"ridge\":276,\"a\":81,\"owners\":[68,70,71]},{\"tag\":\"mate\",\"ridge\":276,\"a\":104,\"owners\":[29,70,71,91,93]},{\"tag\":\"mate\",\"ridge\":276,\"a\":105,\"owners\":[29,68,71,89,93]},{\"tag\":\"mate\",\"ridge\":23,\"a\":29,\"owners\":[20,26,27,28]},{\"tag\":\"mate\",\"ridge\":526,\"a\":86,\"owners\":[25]},{\"tag\":\"mate\",\"ridge\":294,\"a\":89,\"owners\":[32,84]},{\"tag\":\"mate\",\"ridge\":198,\"a\":96,\"owners\":[34,90]},{\"tag\":\"mate\",\"ridge\":326,\"a\":91,\"owners\":[35,85]},{\"tag\":\"mate\",\"ridge\":390,\"a\":93,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":774,\"a\":39,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":305,\"a\":51,\"owners\":[68,76]},{\"tag\":\"mate\",\"ridge\":305,\"a\":76,\"owners\":[51,68]},{\"tag\":\"mate\",\"ridge\":337,\"a\":53,\"owners\":[70,77]},{\"tag\":\"mate\",\"ridge\":337,\"a\":77,\"owners\":[53,70]},{\"tag\":\"mate\",\"ridge\":401,\"a\":54,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":401,\"a\":71,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":534,\"a\":92,\"owners\":[94]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":34,\"full_literals\":[-14,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":101,\"full_literals\":[-48,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":90,\"full_literals\":[-40,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":106,\"full_literals\":[-51,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":20,\"full_literals\":[-6,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":51,\"full_literals\":[-23,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":53,\"full_literals\":[-24,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":54,\"full_literals\":[-25,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":26,\"full_literals\":[-9,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":68,\"full_literals\":[-29,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":70,\"full_literals\":[-30,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-31,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":27,\"full_literals\":[-10,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-33,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":77,\"full_literals\":[-34,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":25,\"full_literals\":[-8,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":28,\"full_literals\":[-11,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":32,\"full_literals\":[-13,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":35,\"full_literals\":[-15,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":37,\"full_literals\":[-17,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":92,\"full_literals\":[-42,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":29,\"full_literals\":[-12,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-36,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":85,\"full_literals\":[-37,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-38,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":93,\"full_literals\":[-43,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":94,\"full_literals\":[-44,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":89,\"full_literals\":[-39,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":91,\"full_literals\":[-41,59]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-55,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-61,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-60,-62,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-59,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-68,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-67,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-63,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":15,\"owners\":[2,14,24,29,32,35,37,39,43,46,47,51,53,54,81,84,85,89,91,93,99,100]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[14,18,29,43,51,53,54,60,68,70,71,76,77,81,89,91,93,99,100,104,105]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[4,10,36,48,56,65,73,86,92,96,101,106]}]}"
  "p cnf 71 111\n-38 -12 0\n-38 -13 0\n-38 -15 0\n-38 -17 0\n-38 -36 0\n-38 -37 0\n-39 -38 0\n-41 -38 0\n-42 -12 0\n-42 -13 0\n-42 -15 0\n-42 -17 0\n-42 -36 0\n-42 -37 0\n-42 -39 0\n-42 -41 0\n-43 -38 0\n-43 -42 0\n-1 12 13 15 17 18 23 24 25 0\n-7 23 24 25 0\n-19 13 15 17 18 0\n-20 12 15 17 18 24 25 0\n-21 12 13 17 18 23 25 0\n-4 1 7 20 21 36 37 0\n-47 1 7 20 36 0\n-2 38 42 45 48 0\n-22 42 45 48 0\n-26 38 42 0\n-7 29 30 31 0\n-3 38 42 45 51 0\n-16 51 0\n-28 42 45 51 0\n-32 38 42 0\n-4 12 23 24 25 39 41 43 0\n-19 39 41 43 0\n-35 23 24 25 0\n-46 12 24 25 41 43 0\n-47 12 23 25 39 43 0\n-5 12 29 30 31 39 41 43 0\n-27 39 41 43 0\n-35 29 30 31 0\n-49 12 30 31 41 43 0\n-50 12 29 31 39 43 0\n-12 6 9 10 11 0\n-38 8 0\n-39 13 36 0\n-45 14 40 0\n-41 15 37 0\n-43 17 0\n-18 0\n-23 29 33 0\n-33 23 29 0\n-24 30 34 0\n-34 24 30 0\n-25 31 0\n-31 25 0\n-42 44 0\n-14 52 0\n-48 52 0\n-40 53 0\n-51 53 0\n-6 54 0\n-23 54 0\n-24 54 0\n-25 54 0\n-9 55 0\n-29 55 0\n-30 55 0\n-31 55 0\n-10 56 0\n-33 56 0\n-34 56 0\n-8 57 0\n-11 57 0\n-13 57 0\n-15 57 0\n-17 57 0\n-42 57 0\n-12 58 0\n-36 58 0\n-37 58 0\n-38 58 0\n-43 58 0\n-44 58 0\n-39 59 0\n-41 59 0\n-53 60 0\n-52 60 0\n-55 61 0\n-54 61 0\n-54 -55 62 0\n-61 63 0\n-60 63 0\n-60 -61 64 0\n-60 -62 65 0\n-57 66 0\n-56 66 0\n-59 67 0\n-58 67 0\n-58 -59 68 0\n-67 69 0\n-68 70 0\n-66 69 0\n-66 -67 70 0\n-63 -70 71 0\n-64 -69 71 0\n-65 71 0\n-71 0\n1 4 7 12 13 15 17 18 19 20 21 23 24 25 35 36 37 39 41 43 46 47 0\n4 5 12 19 23 24 25 27 29 30 31 33 34 35 39 41 43 46 47 49 50 0\n2 3 16 22 26 28 32 38 42 45 48 51 0\n"
  "112 -65 0 108 107 0\n113 1 4 7 12 13 15 17 19 20 21 23 24 25 35 36 37 39 41 43 46 47 0 50 109 0\n114 57 60 0 87 61 31 88 58 60 47 59 73 78 45 27 32 26 28 30 33 111 0\n115 38 42 60 0 87 61 88 58 60 47 32 59 27 31 26 28 30 33 111 0\n116 -38 61 0 50 89 69 68 67 41 29 90 65 64 63 1 2 3 4 5 6 7 8 17 37 19 23 22 21 24 25 113 0\n117 63 0 50 92 93 89 90 67 68 69 63 64 65 29 41 116 115 9 10 11 12 13 14 15 16 18 37 19 23 22 21 24 25 113 0\n118 -70 0 117 108 105 0\n119 -68 0 118 102 0\n120 60 0 118 114 96 104 99 82 84 115 57 0\n121 -62 0 120 112 95 0\n122 23 24 25 35 46 47 69 0 50 103 96 77 76 101 99 79 22 83 98 86 85 35 75 81 80 20 23 34 19 113 0\n123 -23 33 0 121 51 63 67 91 0\n124 -24 34 0 121 53 64 68 91 0\n125 -25 0 121 55 65 69 91 0\n126 -31 0 125 56 0\n127 69 0 125 101 103 98 99 97 85 86 79 83 71 72 123 124 36 37 38 122 0\n128 -64 0 127 108 106 0\n129 -61 0 128 120 94 0\n130 -55 0 129 89 0\n131 -54 0 129 90 0\n132 -9 0 130 66 0\n133 -29 0 130 67 0\n134 -30 0 130 68 0\n135 -6 0 131 62 0\n136 -23 0 131 63 0\n137 -24 0 131 64 0\n138 -33 0 133 136 52 0\n139 -35 0 133 134 126 41 0\n140 -34 0 137 134 54 0\n141 -12 10 0 118 132 135 44 79 74 99 96 104 0\n142 39 41 43 46 47 12 0 139 140 138 126 134 133 125 137 136 42 35 40 43 39 34 110 0\n143 -39 0 119 118 85 98 100 104 80 96 46 75 0\n144 -41 0 119 118 86 98 100 104 81 96 48 76 0\n145 -43 0 118 49 83 77 99 96 104 0\n146 46 12 0 143 136 125 145 144 142 38 0\n147 12 0 145 144 125 137 37 146 0\n148 10 0 147 141 0\n149 58 0 147 79 0\n150 56 0 148 70 0\n151 67 0 149 99 0\n152 66 0 150 97 0\n153 0 152 151 118 104 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record032

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record038
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1e85e1cc6b15c4f332aa95a4e9564d94e4b8ae4785e0fad1ac5713c6a95a4e9565391e695554d54d4b55352d2b51d1743da8d534ce8b52e2b4acab46c5b0ee8751d2729e1745c570dd0f23c4f0bc1f5514c332324c92a4590ea8631324a9314552344d88e130cc2b05c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "369a69b4924d36d369a6db49b4d34d34da49b4db692492489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 25), (facetIndex 38), (facetIndex 49), (facetIndex 60)]))
 (.leaf ([(facetIndex 40), (facetIndex 45), (facetIndex 62), (facetIndex 65)])))
 (.branch 3
 (.leaf ([(facetIndex 43), (facetIndex 73), (facetIndex 75), (facetIndex 78)]))
 (.leaf ([(facetIndex 24), (facetIndex 51), (facetIndex 72), (facetIndex 82)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 22), (facetIndex 27), (facetIndex 28), (facetIndex 29), (facetIndex 30)]))
 (.leaf ([(facetIndex 69), (facetIndex 74), (facetIndex 80)])))
 (.branch 7
 (.leaf ([(facetIndex 23), (facetIndex 26), (facetIndex 39), (facetIndex 71)]))
 (.branch 8
 (.leaf ([(facetIndex 47), (facetIndex 54), (facetIndex 55)]))
 (.leaf ([(facetIndex 35)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3050200252360500010010000007700300070102001600080000444460364z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 31), (facetIndex 34), (facetIndex 42)]))
 (.leaf ([(facetIndex 52), (facetIndex 56), (facetIndex 63), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 70), (facetIndex 77)]))
 (.branch 4
 (.leaf ([(facetIndex 81), (facetIndex 84)]))
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 37), (facetIndex 61)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 41), (facetIndex 48), (facetIndex 50), (facetIndex 64)]))
 (.leaf ([(facetIndex 36), (facetIndex 44), (facetIndex 58)])))
 (.branch 8
 (.leaf ([(facetIndex 46), (facetIndex 57), (facetIndex 59), (facetIndex 68)]))
 (.branch 9
 (.leaf ([(facetIndex 67), (facetIndex 76), (facetIndex 83)]))
 (.leaf ([(facetIndex 53), (facetIndex 79)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "38030902800000207810510407671009105050706005000460044z20;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7, 8]
def grouped2_0008 : List Nat := [7]
def grouped2_0009 : List Nat := [7, 8]
def grouped2_0010 : List Nat := [8]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3, 4]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [3, 4]
def grouped3_0020 : List Nat := [4]
def grouped3_0021 : List Nat := [5]
def grouped3_0022 : List Nat := [5, 6]
def grouped3_0023 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0024 : List Nat := [6]
def grouped3_0025 : List Nat := [7]
def grouped3_0026 : List Nat := [7, 8, 9]
def grouped3_0027 : List Nat := [8]
def grouped3_0028 : List Nat := [8, 9]
def grouped3_0029 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record038" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record038" 92

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record038" "{\"ridges\":[[8,81],[10,168],[11,193],[13,672],[16,296],[17,304],[19,196],[21,84],[21,336],[28,81],[31,166],[32,293],[34,646],[36,90],[38,168],[39,296],[41,323],[43,304],[44,323],[45,672],[47,81],[49,168],[51,328],[52,180],[54,81],[54,84],[54,193],[55,81],[55,336],[56,660],[60,73],[60,193],[61,353],[62,672],[63,240],[64,353],[65,672],[66,720],[71,296],[73,304],[74,336],[75,296],[76,90],[78,304],[80,336],[81,420],[83,120],[84,480]],\"owners\":[[60,73,[6,24,36,41,47,51,59],[11,57,61]],[8,81,[36,44,57,59,63,64,66],[28,47,54,55]],[28,81,[57,59,63,64,66],[8,36,44,47,54,55]],[47,81,[44,63,64,66],[8,28,36,54,55,57,59]],[54,81,[36,44,57,59,64],[8,28,47,55,63,66]],[55,81,[36,57,63,66],[8,28,44,47,54,59,64]],[21,84,[8,28,47,54,68],[74,80]],[54,84,[21,68,74,80],[8,28,47]],[11,193,[9,54,63,66],[60]],[54,193,[11,60],[9,63,66]],[60,193,[9,54,66],[11,63]],[19,196,[9,54],[82]],[10,168,[70,77,81,84],[38,49,60,62]],[38,168,[81,84],[10,49,60,62,70,77]],[49,168,[77,84],[10,38,60,62,70,81]],[13,672,[77],[45,62,65]],[45,672,[],[13,62,65,77]],[62,672,[],[13,45,65,77]],[65,672,[77],[13,45,62]],[16,296,[50,58,61,79,81,83,84],[39,71,75]],[39,296,[79,81,83,84],[16,50,58,61,71,75]],[71,296,[58,61,83,84],[16,39,50,75,79,81]],[75,296,[50,61,81,84],[16,39,58,71,79,83]],[17,304,[53,58,64,79,83],[43,73,75,78]],[43,304,[79,83],[17,53,58,64,73,75,78]],[73,304,[58,64,83],[17,43,53,75,78,79]],[78,304,[53,58,64,79,83],[17,43,73,75]],[51,328,[76,83,84],[20,41,59,61,72,80,82]],[21,336,[44,59,64,76,83],[55,74,80]],[55,336,[76,83],[21,44,59,64,74,80]],[74,336,[59,64,83],[21,44,55,76,80]],[80,336,[44,64],[21,55,59,74,76,83]],[31,166,[70],[]],[32,293,[50,53],[]],[41,323,[33,44],[]],[44,323,[33,41],[]],[34,646,[],[]],[36,90,[68,76],[]],[76,90,[36,68],[]],[52,180,[],[]],[56,660,[],[]],[83,120,[57],[]],[61,353,[64],[]],[64,353,[61],[]],[63,240,[],[]],[66,720,[],[]],[81,420,[],[]],[84,480,[],[]]],\"edges\":[[31,[8,21,28,36,44,47,54,55,57,59,63,64,66,68,74,76,80,83]],[36,[10,13,31,38,45,49,52,60,62,63,65,70,77,81,84]],[37,[16,17,32,39,43,50,53,58,61,64,71,73,75,78,79,81,83,84]],[39,[9,11,19,54,60,63,66,82,84]],[43,[13,34,42,45,56,62,65,66,77]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record038" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record038\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-26,-3],[-27,-5],[-32,-1],[-32,-11],[-32,-15],[-32,-26],[-42,-38],[-43,-32],[-46,-17],[-56,-15],[-58,-26],[-38,1,11,18,21,26,29,37],[-2,18,24,35,37,41,42,44],[-12,35,37,41,42,44],[-26,24,41,42,44],[-32,18,24,35,37,42],[-33,18,35,41,44],[-10,2,12,26,32,45],[-32,10,45,50,56],[-5,3,32,41,44],[-32,5,38],[-38,3,32,44],[-9,3,32],[-4,47,53,57,60],[-19,57,60],[-27,53,60],[-6,53],[-25],[-40],[-43,53],[-7,28,36,39,55,57,59,60],[-20,55,57,59,60],[-48,36,39,59,60],[-51,28,39,57,60],[-8,31,36,42,55,59],[-23,55,59],[-49,36,42,59],[-54,31,36,42,55,59],[-29,52,59,60],[-10,24,37,42,52,59],[-33,52,59],[-50,37,42,59],[-56,24,42],[-13,47],[-14,28,31],[-21,15,24],[-24,15,21],[-16],[-18,45,52],[-52,18,45],[-30],[-34],[-59,35],[-39,42],[-42,39],[-41],[-44],[-57],[-60],[-61,46,50,56],[-62,26,32,33],[-63,17],[-64,61],[-65,62,63],[-66,62],[-67,65],[-68,66],[-69,64,68],[-69,67],[-70,69],[70],[-22,71],[-47,72],[-53,72],[-39,73],[-21,74],[-28,74],[-42,74],[-18,75],[-24,75],[-36,75],[-35,76],[-37,76],[-45,76],[-52,77],[-59,77],[-31,78],[-55,78],[-71,79],[-73,80],[-72,81],[-72,-80,82],[-81,83],[-82,84],[-79,83],[-75,85],[-74,85],[-74,-75,86],[-78,87],[-77,87],[-87,88],[-76,88],[-76,-87,89],[-89,91],[-85,90],[-85,-88,91],[-86,91],[-83,-91,92],[-84,-90,92],[-92],[2,10,12,18,24,26,32,33,35,37,41,42,44,45,50,52,56,59],[4,6,13,19,25,27,30,38,40,41,43,47,53,57,60],[7,8,14,20,23,28,31,36,39,42,48,49,51,54,55,57,59,60],[3,5,9,32,38,41,44,58,60],[6,16,22,25,34,40,43,44,53]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":47,\"b\":9},{\"tag\":\"incompatible\",\"a\":49,\"b\":11},{\"tag\":\"incompatible\",\"a\":54,\"b\":6},{\"tag\":\"incompatible\",\"a\":54,\"b\":24},{\"tag\":\"incompatible\",\"a\":54,\"b\":33},{\"tag\":\"incompatible\",\"a\":54,\"b\":47},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":65,\"b\":54},{\"tag\":\"incompatible\",\"a\":69,\"b\":35},{\"tag\":\"incompatible\",\"a\":80,\"b\":33},{\"tag\":\"incompatible\",\"a\":82,\"b\":47},{\"tag\":\"mate\",\"ridge\":73,\"a\":60,\"owners\":[6,24,36,41,47,51,59]},{\"tag\":\"mate\",\"ridge\":81,\"a\":8,\"owners\":[36,44,57,59,63,64,66]},{\"tag\":\"mate\",\"ridge\":81,\"a\":28,\"owners\":[57,59,63,64,66]},{\"tag\":\"mate\",\"ridge\":81,\"a\":47,\"owners\":[44,63,64,66]},{\"tag\":\"mate\",\"ridge\":81,\"a\":54,\"owners\":[36,44,57,59,64]},{\"tag\":\"mate\",\"ridge\":81,\"a\":55,\"owners\":[36,57,63,66]},{\"tag\":\"mate\",\"ridge\":84,\"a\":21,\"owners\":[8,28,47,54,68]},{\"tag\":\"mate\",\"ridge\":84,\"a\":54,\"owners\":[21,68,74,80]},{\"tag\":\"mate\",\"ridge\":193,\"a\":11,\"owners\":[9,54,63,66]},{\"tag\":\"mate\",\"ridge\":193,\"a\":54,\"owners\":[11,60]},{\"tag\":\"mate\",\"ridge\":193,\"a\":60,\"owners\":[9,54,66]},{\"tag\":\"mate\",\"ridge\":196,\"a\":19,\"owners\":[9,54]},{\"tag\":\"mate\",\"ridge\":168,\"a\":10,\"owners\":[70,77,81,84]},{\"tag\":\"mate\",\"ridge\":168,\"a\":38,\"owners\":[81,84]},{\"tag\":\"mate\",\"ridge\":168,\"a\":49,\"owners\":[77,84]},{\"tag\":\"mate\",\"ridge\":672,\"a\":13,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":672,\"a\":45,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":672,\"a\":62,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":672,\"a\":65,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":296,\"a\":16,\"owners\":[50,58,61,79,81,83,84]},{\"tag\":\"mate\",\"ridge\":296,\"a\":39,\"owners\":[79,81,83,84]},{\"tag\":\"mate\",\"ridge\":296,\"a\":71,\"owners\":[58,61,83,84]},{\"tag\":\"mate\",\"ridge\":296,\"a\":75,\"owners\":[50,61,81,84]},{\"tag\":\"mate\",\"ridge\":304,\"a\":17,\"owners\":[53,58,64,79,83]},{\"tag\":\"mate\",\"ridge\":304,\"a\":43,\"owners\":[79,83]},{\"tag\":\"mate\",\"ridge\":304,\"a\":73,\"owners\":[58,64,83]},{\"tag\":\"mate\",\"ridge\":304,\"a\":78,\"owners\":[53,58,64,79,83]},{\"tag\":\"mate\",\"ridge\":328,\"a\":51,\"owners\":[76,83,84]},{\"tag\":\"mate\",\"ridge\":336,\"a\":21,\"owners\":[44,59,64,76,83]},{\"tag\":\"mate\",\"ridge\":336,\"a\":55,\"owners\":[76,83]},{\"tag\":\"mate\",\"ridge\":336,\"a\":74,\"owners\":[59,64,83]},{\"tag\":\"mate\",\"ridge\":336,\"a\":80,\"owners\":[44,64]},{\"tag\":\"mate\",\"ridge\":166,\"a\":31,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":293,\"a\":32,\"owners\":[50,53]},{\"tag\":\"mate\",\"ridge\":323,\"a\":41,\"owners\":[33,44]},{\"tag\":\"mate\",\"ridge\":323,\"a\":44,\"owners\":[33,41]},{\"tag\":\"mate\",\"ridge\":646,\"a\":34,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":90,\"a\":36,\"owners\":[68,76]},{\"tag\":\"mate\",\"ridge\":90,\"a\":76,\"owners\":[36,68]},{\"tag\":\"mate\",\"ridge\":180,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":660,\"a\":56,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":120,\"a\":83,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":353,\"a\":61,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":353,\"a\":64,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":240,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":720,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":420,\"a\":81,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":480,\"a\":84,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[69,74,80],\"full_literals\":[-61,46,50,56]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[47,54,55],\"full_literals\":[-62,26,32,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[35],\"full_literals\":[-63,17]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,62,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-69,64,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-70,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":42,\"full_literals\":[-22,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":70,\"full_literals\":[-47,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":77,\"full_literals\":[-53,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":61,\"full_literals\":[-39,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":41,\"full_literals\":[-21,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":50,\"full_literals\":[-28,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":64,\"full_literals\":[-42,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":36,\"full_literals\":[-18,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":44,\"full_literals\":[-24,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":58,\"full_literals\":[-36,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":57,\"full_literals\":[-35,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":59,\"full_literals\":[-37,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":68,\"full_literals\":[-45,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":76,\"full_literals\":[-52,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":83,\"full_literals\":[-59,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":53,\"full_literals\":[-31,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":79,\"full_literals\":[-55,78]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-73,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-72,-80,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-81,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-82,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-79,false,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-74,-75,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-77,false,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-87,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-89,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-85,-88,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-86,false,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-83,-91,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-84,-90,92],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":31,\"owners\":[8,21,28,36,44,47,54,55,57,59,63,64,66,68,74,76,80,83]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[10,13,31,38,45,49,52,60,62,63,65,70,77,81,84]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[16,17,32,39,43,50,53,58,61,64,71,73,75,78,79,81,83,84]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[9,11,19,54,60,63,66,82,84]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[13,34,42,45,56,62,65,66,77]}]}"
  "p cnf 92 115\n-26 -3 0\n-27 -5 0\n-32 -1 0\n-32 -11 0\n-32 -15 0\n-32 -26 0\n-42 -38 0\n-43 -32 0\n-46 -17 0\n-56 -15 0\n-58 -26 0\n-38 1 11 18 21 26 29 37 0\n-2 18 24 35 37 41 42 44 0\n-12 35 37 41 42 44 0\n-26 24 41 42 44 0\n-32 18 24 35 37 42 0\n-33 18 35 41 44 0\n-10 2 12 26 32 45 0\n-32 10 45 50 56 0\n-5 3 32 41 44 0\n-32 5 38 0\n-38 3 32 44 0\n-9 3 32 0\n-4 47 53 57 60 0\n-19 57 60 0\n-27 53 60 0\n-6 53 0\n-25 0\n-40 0\n-43 53 0\n-7 28 36 39 55 57 59 60 0\n-20 55 57 59 60 0\n-48 36 39 59 60 0\n-51 28 39 57 60 0\n-8 31 36 42 55 59 0\n-23 55 59 0\n-49 36 42 59 0\n-54 31 36 42 55 59 0\n-29 52 59 60 0\n-10 24 37 42 52 59 0\n-33 52 59 0\n-50 37 42 59 0\n-56 24 42 0\n-13 47 0\n-14 28 31 0\n-21 15 24 0\n-24 15 21 0\n-16 0\n-18 45 52 0\n-52 18 45 0\n-30 0\n-34 0\n-59 35 0\n-39 42 0\n-42 39 0\n-41 0\n-44 0\n-57 0\n-60 0\n-61 46 50 56 0\n-62 26 32 33 0\n-63 17 0\n-64 61 0\n-65 62 63 0\n-66 62 0\n-67 65 0\n-68 66 0\n-69 64 68 0\n-69 67 0\n-70 69 0\n70 0\n-22 71 0\n-47 72 0\n-53 72 0\n-39 73 0\n-21 74 0\n-28 74 0\n-42 74 0\n-18 75 0\n-24 75 0\n-36 75 0\n-35 76 0\n-37 76 0\n-45 76 0\n-52 77 0\n-59 77 0\n-31 78 0\n-55 78 0\n-71 79 0\n-73 80 0\n-72 81 0\n-72 -80 82 0\n-81 83 0\n-82 84 0\n-79 83 0\n-75 85 0\n-74 85 0\n-74 -75 86 0\n-78 87 0\n-77 87 0\n-87 88 0\n-76 88 0\n-76 -87 89 0\n-89 91 0\n-85 90 0\n-85 -88 91 0\n-86 91 0\n-83 -91 92 0\n-84 -90 92 0\n-92 0\n2 10 12 18 24 26 32 33 35 37 41 42 44 45 50 52 56 59 0\n4 6 13 19 25 27 30 38 40 41 43 47 53 57 60 0\n7 8 14 20 23 28 31 36 39 42 48 49 51 54 55 57 59 60 0\n3 5 9 32 38 41 44 58 60 0\n6 16 22 25 34 40 43 44 53 0\n"
  "116 -19 0 59 58 25 0\n117 69 0 71 70 0\n118 67 0 117 69 0\n119 65 0 118 66 0\n120 2 10 12 18 24 26 32 33 35 37 42 45 50 52 56 59 0 56 57 111 0\n121 4 6 13 27 38 43 47 53 0 116 28 51 29 56 58 59 112 0\n122 7 8 14 20 23 28 31 36 39 42 48 49 51 54 55 59 0 58 59 113 0\n123 3 5 9 32 38 58 0 56 57 59 114 0\n124 6 22 43 53 0 48 28 52 29 57 115 0\n125 83 0 93 95 91 89 74 72 27 30 124 0\n126 -91 0 125 110 108 0\n127 -89 0 126 104 0\n128 -86 0 126 107 0\n129 76 85 0 57 56 97 78 96 80 43 15 79 82 83 84 14 53 17 13 16 42 50 18 120 0\n130 85 0 127 58 59 96 97 81 77 78 54 34 129 103 99 100 87 88 86 35 38 45 32 36 31 37 33 122 0\n131 -88 0 130 126 106 0\n132 -87 0 131 101 0\n133 -76 0 131 102 0\n134 -77 0 132 100 0\n135 -37 0 133 83 0\n136 -45 0 133 84 0\n137 -52 0 134 85 0\n138 -59 0 134 86 0\n139 -18 0 136 137 49 0\n140 -29 0 137 138 59 39 0\n141 -33 0 137 138 41 0\n142 62 50 56 0 119 117 64 65 62 67 9 68 60 63 0\n143 -62 32 0 57 56 141 61 1 11 20 22 23 123 0\n144 -24 15 0 128 47 80 76 98 0\n145 50 56 82 0 136 138 137 135 140 139 59 58 142 143 3 4 5 6 8 19 144 46 40 12 55 21 75 2 90 92 73 74 44 27 24 121 0\n146 -42 82 0 59 58 7 55 75 90 92 73 74 44 26 27 30 24 121 0\n147 82 0 138 135 146 42 145 10 43 144 0\n148 90 0 130 105 0\n149 84 0 147 94 0\n150 0 149 148 110 109 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00075.record038
