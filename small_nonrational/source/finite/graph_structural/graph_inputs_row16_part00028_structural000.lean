module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00028Data
public import GraphInputsRow16Part00028Frames
public import GraphInputsRow16Part00028Leaves
public import GraphInputsRow16Part00028Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00028.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record018
def vertexColumn : Fields := ⟨10, hexnat% "6b0dc9a8da658d68d98e3392e2785eb45a99a4d96959535635634cd4b4ad2745d70f2398d9334e3362e4b32e2b4ac6b26c5b61cc789e1745c9715c3743c8f13c1f949260ba51344c9615252548d0b64388d2384c5312c2b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6da6d36924d249369349a492693492492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [233633654763421696, hexnat% "10000002080000000", 2630102182384369664, 18387828736, 40956808134656, 70368744177664]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [233633586043944960, hexnat% "10000002080000000", 2630102182384369664, 18387828736, 105896713650176, 5497558138880]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2630110987084103680, hexnat% "10028002002000000", 110228188168192, 217861631974047744, 1735175176192, 4503599761588224, 1950351360]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00028.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00028.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record022
def vertexColumn : Fields := ⟨10, hexnat% "971d26a99a3693a99936938ce8b85e0f9d1b25a96665936539996554d64d3361d1743d70da398d9354cd34cd8b92ccb8ad2b2ad1b26c5b0ee4731e2749c6745c3783c8f13e2c1582e07a29916251560d0b41d60cc348d1314c8b0ac1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db4936db6d269a49269249a492492492492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4004b7d3e8d800000", 220676381741154304, hexnat% "a0004000002000000", 826244333568, 4563402752]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200076dfe2f800000", hexnat% "40048000000000000", hexnat% "80000000140000000", 220676381741154304, 17594601963520]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a001605ffd7800000", hexnat% "40048000000000000", 123145436528640, 216172782113783808, 290271606603776]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [982955535106048, 72057600748814336, hexnat% "60000000004000000", hexnat% "80004000040000000", 166633186212708352, 2251799813685248]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a0004010a03000000", 238690780250636288, hexnat% "4000800040c800000", 962609545216, 584942333460480, 395892905476096, 5637144576]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00028.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00028.record056
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record056
def vertexColumn : Fields := ⟨10, hexnat% "26c9723c669a699a568d98e4b86e2785e0fa69666598e5a599695956356364d8b52d1b61d2745d0f5a398d9394e3362d4b1ad1b26c5b0ed8791cc789d2729c6785c570dd0f23d2a2584e0b81e4a645896152544d0b41d60d2324d0b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db4924db6d249a49249269b492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "783dfe02fffe000000", hexnat% "800000000000000000", 361739325538304, 4398046511104]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3019ff4ff9be000000", hexnat% "80400000000000000", hexnat% "c00000000000000000", 26843545600, 2305843009213693952]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7819fe00c83e000000", 2594073393955340288, 295768627871744, 70456791007232, hexnat% "800000022100000000", 1073741824]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000c54bb7de000000", 4672924418048, hexnat% "780000000000000000", 2386907836866101248, 1448470230689906688, 576460752303423488]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "815ff4ff7be000000", hexnat% "700000000000000000", 2305843044647174144, hexnat% "800000000000000000", 576460752303423488]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "815fe402ffe000000", 2882303761517117440, hexnat% "700000000000000000", hexnat% "800000001000000000", 295768627871744, 3023656976384]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c8 c0
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2050593480769536, hexnat% "800040001004000000", 2024368033039908864, 7559175995392, hexnat% "780000000000000000", 2422936600599068672, 62679678976]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c11 c5
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c12 c4
  c13
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record056_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record056_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record056_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record056_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record056_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record056_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record056_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record056_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00028.record056_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00028.record056
