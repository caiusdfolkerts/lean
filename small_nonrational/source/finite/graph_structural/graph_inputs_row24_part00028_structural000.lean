module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00028Data
public import GraphInputsRow24Part00028Frames
public import GraphInputsRow24Part00028Leaves
public import GraphInputsRow24Part00028Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005
def vertexColumn : Fields := ⟨10, hexnat% "1f352d295a4e87a958b61d8ce1b91e1783ed4749565391e6552d4753346d4745d0f74354e334ccb31cf0b62e4b52ccb4ac6b46c5b0ee4731c6785d1725d0f07cacc4a522a8a6158362384e0bb11944a9294550d48d1342dc0e4328e1344c530cd0b22c4b0ac8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1a6db4924d24db69249a492492492492492492449249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1003801fbbf8d800000000", 1133596488237056, hexnat% "10008000000000000000", hexnat% "40020040002000000000", hexnat% "80040000000000000000", hexnat% "28014000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10eb85563ffdf800000000", 126100789566373888, hexnat% "20800000000000000", hexnat% "10008000020000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "eb03482261e800000000", hexnat% "10008001021000000000", hexnat% "1000800700000000000000", hexnat% "41000140000000000", 54192729109823488, 7881299347898368]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bb851bf03ff800000000", hexnat% "40020000000000000000", 13835058055282163712, hexnat% "1000000402000000000000", 3870280929771520]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6b03dbf07bf800000000", hexnat% "10000001000000000000", hexnat% "80040000040000000000", 4081387162304512, hexnat% "1000800400000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "620343f03bf800000000", hexnat% "80040000040000000000", 10952754293765046272, hexnat% "1000800402000000000000", hexnat% "19000000000000000000", 3870280929771520]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6907582061e800000000", hexnat% "10008001021000000000", hexnat% "1000800700000000000000", hexnat% "82000000140000000000", 54192729109823488, 8444249301319680]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a3051ffffff800000000", hexnat% "1000800000000000000000", hexnat% "10008000000000000000", hexnat% "40020000000000000000", hexnat% "8004000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "33019ffffff800000000", hexnat% "24000000000000000", hexnat% "80040000000000000000", hexnat% "48000000000000000000", hexnat% "1000800000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "63031bebfff800000000", 293859875685924864, hexnat% "10008000000000000000", hexnat% "80040000000000000000", hexnat% "8004000000000000000", hexnat% "1000800000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7b034820695800000000", 10376295740484878336, 8866461766385664, hexnat% "80040200148000000000", 126100927005327360, hexnat% "1000800400000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3a0193fffff800000000", hexnat% "80040000000000000000", hexnat% "41000000000000000000", hexnat% "1000800400000000000000", hexnat% "24800000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "aa07dffffff800000000", hexnat% "1000800000000000000000", hexnat% "11000000000000000000", hexnat% "40000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6903dbf0fff800000000", hexnat% "80040000000000000000", 4222124650659840, hexnat% "12000000000000000000", hexnat% "1000800400000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fb035bf0bfe800000000", hexnat% "840000000000000000", 9223653580550963200, hexnat% "1000000402000000000000", 3448068464705536]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6a0343f0bbe800000000", hexnat% "80040000040000000000", hexnat% "1000800402000000000000", hexnat% "10008001001000000000", 3448068464705536, hexnat% "1001800000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c22 c19
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c23 c16
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "680300c0296000000000", hexnat% "1000800700008000000000", hexnat% "10008001021800000000", hexnat% "80040020140000000000", hexnat% "3001800000000000000", 8655355533852672, 4611686018427387904]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c26 c15
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c27 c14
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c28 c9
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c29 c8
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c30 c3
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c31 c0
  c32
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012
def vertexColumn : Fields := ⟨10, hexnat% "2f07cd4b4a6695a3693a2e87ac5a562d876c3a4e2b86e4789e1783ed474966559365392e479c56552d475c364d2b46d4749d1743dd0f1364e5354cd34cc73c2d8b92d4b32d2b1ad1b26c5b0ef0789ca719e1745c9783d0f23c1f2c8aa918560d84e0b8b12a645154351342dc0e4328d1324c530cd0b22c4b0ae0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6d36926926d26db6d36926926d2492492492492492492492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "552000002000000000", hexnat% "55200000000000000000000", 576462478880276480, hexnat% "22000220000024480000000", hexnat% "2001020010001c0040000000", 4468419550248960, 571957187035791360]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019
def vertexColumn : Fields := ⟨10, hexnat% "bc9cb4a6693a2ea562d876338ae4789e0fa71d25994e4b9954b51d4cd2b51d2743dd0e63a4d9394e334ccb31cf0b62e4b52ccb4acab46c9b0ee4731ca785d1715d0f07c6cc486a198960d88e1382ec4469194950d48d1342dc0e4318e1344c930cd0b22c4b0ac8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db4926936db6924d2492492492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20010000408600000000", hexnat% "40020088000800000000", 865114440431828992, 1750422511419392, hexnat% "4b000004000000000", hexnat% "96000000000000000000", 247704782733574144]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record019
