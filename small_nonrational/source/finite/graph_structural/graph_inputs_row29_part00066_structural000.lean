module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00066Data
public import GraphInputsRow29Part00066Frames
public import GraphInputsRow29Part00066Leaves
public import GraphInputsRow29Part00066Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00066.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record001
def vertexColumn : Fields := ⟨10, hexnat% "3b0ce3349b23ce89e2e4b2a9a8eac68dac9a6639b1635a4e8b86e179e1cc5b1ca4e9c64d98e5392e72539715356354d4b58b61d1743d70f2368d6338f1334f0b32e2b4acab1ae1b46c9b16f0731e2749ca719e1745c9715e0f0be2c1b21cc499286a168384e079a1385911a4651342d0758330d1324c4b06c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db49b4db4db69a49269a6db6d36db4924d34934db4924d36d2492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨65, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩, ⟨87, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c001e4000b28080218000000", hexnat% "11020000000000000000", 289360678400032768, hexnat% "88400000000000000000000", 36732621899694080, 3852048793600]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c001e0000f02048138000000", hexnat% "88400000004000000000000", hexnat% "140000a0000000000000", 3301756108800, 2401479423950848, hexnat% "1020000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "740000a0000000000000", hexnat% "c00180000000000000000000", hexnat% "88400000004000000000000", hexnat% "1020008080200000000", 1080863910971572224, 704375173414912, 7704097587200]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00066.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00066.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record002
def vertexColumn : Fields := ⟨10, hexnat% "ea338cd2743b23c1f3a2789d2e2b2aaa9aa3ab1a668dac9a6639b16958ce8b8ae1b85e785d1cc571ca5a93a719664d98e5391e725397158d5351d4cd8b4ad1b61d1743d70f2368d6338f1364d5334f0b62ccb8ad2b2ac6b86d1b26c5bc1cc789d2729c6785d1783c8f13c2f8b21cc4a1a858568381e684e12a4651542d0758330d1314c8b06c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da6db6db69b6da4d36936da4db6db4db4d24924d34924d26d349269b692492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨94, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22180839abb2f45f000000", hexnat% "100000000008000000000000000", hexnat% "410000000004000020000000", hexnat% "8400000000000000000000", 432345564227567616]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40808bb8bb2f45f000000", hexnat% "100002000000400000000000000", hexnat% "210000020000000000000", hexnat% "418000000000000020000000", 1125899906842624]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000200008bcabb2f45f000000", 216172782113783808, hexnat% "410000000004000020000000", hexnat% "218000000000000000000", hexnat% "8400000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000089883b2f45f000000", hexnat% "418000000000000020000000", hexnat% "100000000002500000000000000", 1125899906842624, hexnat% "218000028000000000000", hexnat% "400000200000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10001a618088fa8b2b47b000000", hexnat% "400000000004004000000000", 1152921504673955840, 844424930131968, 2305843009213693952]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41a618000eae32f07b000000", 422229644935168, hexnat% "100000000002100000000000000", hexnat% "88000000000000000", 1152921504673955840]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "418418000eafb2f43e000000", hexnat% "200081000000000000000", 9223372037928517632, hexnat% "100002000002000000000000000", 72057594054705152]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1a618089ea832b47f000000", hexnat% "400000000004004000000000", hexnat% "100000000002100000000000000", 985162418487296]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "418408000e2c32f03a000000", hexnat% "100002000002000000000000000", 37013959437451264, hexnat% "88000000440000000", hexnat% "210001000000000000000", 72057594121814016]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "418408008b0090347f000000", hexnat% "100002000002400000000000000", hexnat% "210081000000000000000", 1970599714881536, 549755813888, 47325179482734592]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "26180811a8b22447000000", hexnat% "100000000008000000000000000", hexnat% "418000000000000020000000", 1970668702793728, 720575940379279360, 2594073935255437312]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41840008358f32f43f000000", 140738562097152, hexnat% "100002000000000000000000000", hexnat% "218000020000000000000", 9943947977234055168]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40008118fb2f41f000000", hexnat% "100000000008000000000000000", hexnat% "218000020000000000000", hexnat% "418000000000000020000000", hexnat% "2000002400000000000000", 720575941453021184]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000240808bf0810304f000000", 36204736059277312, hexnat% "418000000000000020000000", hexnat% "210000020020000000000", 1970599983316992, 549755813888]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "26180898a8322447000000", hexnat% "418000000000000020000000", hexnat% "100000000002500000008000000", 985506284306432, 144115188075855872, 1126449662656512]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "418408008f08123077000000", hexnat% "100002000002000000008000000", hexnat% "81000000400000000", 36767668832829440, hexnat% "210000020000000000000", 1408199517274112]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2618081aaa322447000000", hexnat% "100000000008100000000000000", hexnat% "418000000000000020000000", 422556330885120, 2595199835162279936]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "418400000a28022026000000", hexnat% "88000000440000000", hexnat% "218001000000000000000", hexnat% "100002000002400000008000000", 72057594054705152, 36785261018873856, 1408268505186304]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c27 c22
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c28 c21
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c29 c20
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c30 c17
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c31 c16
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c32 c15
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c33 c6
  c34
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00066.record002
