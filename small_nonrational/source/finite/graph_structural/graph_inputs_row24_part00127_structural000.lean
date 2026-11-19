module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00127Data
public import GraphInputsRow24Part00127Frames
public import GraphInputsRow24Part00127Leaves
public import GraphInputsRow24Part00127Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000
def vertexColumn : Fields := ⟨10, hexnat% "dc2745d26c3b25cd8b52cca725caaa9aa5a56a6659a5655a364d87693a2e2b86e8789e17a715c6693a65956565395554d475334ad1b49d68e6358e5354e334cc7392d4b8acab1ae1b46c9b16d4749c6745c9715c3713c2f9605c868a62381e58551164a5194552344d0752328d1322c1b21c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da6db6da6db6db6d34934da4926924934d34db69a493492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [1, 2, 3, 4]
def candidates : List (Fin raw.n) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efffffb6edbffffffffffff", 10133099161583616, 9295429630892703744, hexnat% "10000001000000000000000", hexnat% "40000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3effffd366fff7abdfffffff", hexnat% "200000004000000000", 9223380832947798016, hexnat% "10000001800000000000000", 72057594574798848, hexnat% "c0000001400000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffffffdcd77b7fbffffff", 8830519869440, 4503874505277440, 153122387330596864, 703687441776640]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efeffd7fffd77a7ffffffff", hexnat% "200000004000000000", hexnat% "10100080000000000000000", 103079215104, 712483534798848]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffdffdcd77a3e8ffffff", 712483534798848, 157625986974744576, hexnat% "200000004010000000", 120259084288, 100663296]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efeffd1e7c3dfa9ffffffff", 16888498602639360, hexnat% "200000004000000000", 576495945265446912, hexnat% "c0000001400000000", hexnat% "10100021000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efefff56197dfedffffffff", 173388585653764096, hexnat% "1000a0000001200000000", 9511602413006487552, hexnat% "10000001800000000000000", 35184372088832]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffd3fd83ffa3deffffff", 120795955200, 173388585653764096, hexnat% "200010004001000000", hexnat% "c0000000000000000", 1125899906842624]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .size 1
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨8, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨12, by decide⟩ c12 c13
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c11 c14
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c11 c15
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffff7fdbfffffffffffff", hexnat% "80000000000000000", 162129586585337856]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffff7dbdffbfffffffff", 563224831328256, 162129586585337856, 9223372036854775808]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efeffd775bfffffffffffff", 162129586585337856, hexnat% "200000000000000000", 9799832789158199296, hexnat% "10100080000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efeffd7effdffa7ffffffff", hexnat% "200000004000000000", hexnat% "80000001800000000", 562949953421312, hexnat% "10100001000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efefff7e1bdd7e77fffffff", 571748193927168, 450359962737049600, hexnat% "100001000001000000000", 576495971035250688, hexnat% "10000080000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c11 c27
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c11 c28
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffff77ffdffbfffffffff", 9223372036854775808, hexnat% "80000000000000000", 563224831328256]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3effffd777fdffbfffffffff", 563224831328256, 9799832789158199296, hexnat% "10000080000000000000000", hexnat% "200000000000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffdf79fdffbf7fffffff", 9511602413006487552, hexnat% "200000004000000000", 562952100904960, 144115188075855872]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efffff761fdf7ef7fffffff", hexnat% "80000001000000000", 432345566375051264, 571746046443520, hexnat% "10000001800000000000000", 9223372036854775808]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c36 c33
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffdfffcdf7bfffffffff", 571746046443520, 13510798882111488, hexnat% "200000004000000000"]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffdf7dcdf7bf7fffffff", 9223380832947798016, 157625986957967360, hexnat% "200000004000000000", 562952100904960]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3effffff69ddf7ff7fffffff", 153122387330596864, hexnat% "10000001000000000000000", 571748193927168, 9511602413006487552]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffffb79cdf7ab7fffffff", 157625986957967360, 9223380832947798016, hexnat% "40000001400000000", 563226978811904, 288230376151711744]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c42 c41
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c43 c40
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efeffdd6187dfffffffffff", hexnat% "200018000000000000", 171136785840078848, hexnat% "10100021000000000000000", 9799867973530288128, 288230376151711744]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efeffd16187d7e5dfffffff", 159877786771652608, 9529616811515969536, hexnat% "240000000000000000", hexnat% "10000001800000200000000", 44015361720320, hexnat% "1000a0000001000000000"]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c47 c44
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c48 c37
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c49 c26
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c50 c10
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c51 c9
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c52 c8
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c53 c7
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c54 c2
  c55
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record000
