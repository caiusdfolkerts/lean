module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00009Data
public import GraphInputsRow24Part00009Frames
public import GraphInputsRow24Part00009Leaves
public import GraphInputsRow24Part00009Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00009.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020
def vertexColumn : Fields := ⟨10, hexnat% "f2334ab15c3caaa56aa655a8e53a2e2b91e17bc1cc4f1e2749b25c9aa559c96a5c55558d535a354d8b4ad4745da8ce354cd32cc73a2d4b8acab46c5ba1d4789ca745c5783d0f23c4f0bc1fc30ca0daa154709a254932705895150d60d434c328c530cc8b12c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6db6d24924924924d349249269a6d2492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3bffa2203fe000000", 4611687186658492416, 4398063288320, 220177203462144, 17592186044416]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fd3833517f000000", 219902325555200, 54043204118380544, 4400193994752, 144678138029277184]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ad28ca413c000000", 5769112222173233152, 198158385751785472, 8640266240, 57244397862912, 562949953421312]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2641511007075172352, 92427696209920, 739153288842182656, hexnat% "2c000020000000000", 1225014283016863744, hexnat% "10010010000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11b723410f3000000", 326510981574295552, hexnat% "2c000020000000000", 1099712954368, 2305984021579956224, 79169132167168]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [12441996902096961536, hexnat% "20010000020000000", 39652211818496, hexnat% "15000010000000000", 234187182770749440, 285212672]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5850795286728802304, hexnat% "38000000000000000", 83567178678272, 198158385751785472, 2594214122853761024, 578712560707043328]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5774456206491910144, 234187182770749440, hexnat% "38000000000000000", 4503600432676864, 2305845208236949504, 902971725287784448]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "23fea3552f7000000", hexnat% "14010000000000000", 219906620522496, 9223374236012249088]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22eaae25236000000", 90071995768635392, 30786325577728, hexnat% "1c000010000000000", 4445962240, 1157425104234217472]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffba83537e000000", 18014400673742848, 101155069755392, 35184372088832]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3573a355076000000", 630503956421804032, 11529217245091725312, 4445962240, 2147483648, 219902325555200]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [340862156557778944, 576460752840294400, hexnat% "2a000020000000000", 234187182770749440, hexnat% "15000010000000000", 268435456]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d37a31519e000000", hexnat% "22000020000000000", 83562883710976, 1090519040, 900719934064033792, 140738025226240]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2acfa8b5327000000", 70368878395392, 144115190491774976, 57175678386176, hexnat% "15000000000000000", 72057594037927936]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1517a3d53c7000000", 213305255788544, 756604737398243328, 939524096, 2594073385365405696, hexnat% "28000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [16428160887291904, 900719925474099200, 1225014283016863744, 2305985945725304832, hexnat% "3c000000000000000", 162129588732821504, 956301312]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c22 c17
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c23 c16
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c24 c15
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c25 c12
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c26 c9
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c27 c8
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c28 c7
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c29 c6
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c30 c5
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c31 c4
  c32
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00009.record020
