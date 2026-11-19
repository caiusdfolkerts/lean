module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00005Data
public import GraphInputsRow23Part00005Frames
public import GraphInputsRow23Part00005Leaves
public import GraphInputsRow23Part00005Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014
def vertexColumn : Fields := ⟨10, hexnat% "2f34a2eb46719a665a4e538ae1b89e17b492e745715a56564d534ad1b49d1778370da364f0b52e2b2ac6b86c9b16f0791cc749c6745c5783d0f23cb40f3422ca4a0e986518a6258361382e07b412c6490e585514a5254351342d0770360e4350ca324c3382c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "12492492492492492492492492492492492449249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "390391e21ff80000000000", hexnat% "28048040040000000000000", 2134706223373615104, hexnat% "6a0000000000000000", hexnat% "4404000000000000000000", hexnat% "2a0000000000000000000", hexnat% "10010000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "380381fbff80000000000", hexnat% "1e000000000000000", hexnat% "20020000000000000000", hexnat% "10010000000000000000000", hexnat% "3800000000000000000", hexnat% "28048040040000000000000", hexnat% "3800000000000000000000", hexnat% "4404400000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3dfec55fffbb80000000000", hexnat% "10200000000000000000", hexnat% "a0000000000000000", hexnat% "2002000004000000000000", 70368744177664, hexnat% "1800000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3dfec551ffb380000000000", hexnat% "2a0000000000000000", hexnat% "10000000000000000000", hexnat% "1004004000000000000", 211106232532992, hexnat% "802000000000000000", hexnat% "2002008000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "147b460193b300000000000", 486397555849035776, hexnat% "1e000000000000000", hexnat% "1e0000000000000000", hexnat% "3800000004000000000000", hexnat% "3800000000000000000", hexnat% "28048000000000000000000", 211106232532992]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "146146a193b300000000000", 486397555849035776, hexnat% "1e000000000000000", hexnat% "1e0000000000000000000", hexnat% "3800004000000000000", hexnat% "3800000000000000000000", hexnat% "40000c00000000000", hexnat% "28008100000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7e0241e017900000000000", hexnat% "1940000080000000000", hexnat% "14200808000000000000", hexnat% "10000001000000000000000", hexnat% "80080100200000000000", hexnat% "20020020400000000000", 486388759756013568, hexnat% "28148000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "26e06e097ff80000000000", hexnat% "10010001000000000000000", hexnat% "4004008000000000000000", 468374361246531584, hexnat% "16000000000000000", hexnat% "3800000000000000000", hexnat% "1900000000000000000000", hexnat% "28008100000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24a04a1feb780000000000", hexnat% "10210200000000000000000", hexnat% "1e010000000000000", hexnat% "4004000000000000000000", hexnat% "28148140000000000000000", hexnat% "1001000004000000000000", hexnat% "800800000800000000000", hexnat% "2000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2bde87e0343d80000000000", hexnat% "3800004000000000000", 2062683813707776000, hexnat% "1e010000000000000", hexnat% "10210000008000000000000", hexnat% "4004000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3c43c5e15ff80000000000", hexnat% "80080000000000000000", hexnat% "4004000800000000000000", 1486187877032263680, hexnat% "20020000000000000000", hexnat% "28108100200000000000000", hexnat% "10210200000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3d40400103c80000000000", hexnat% "1e010000000000000", hexnat% "80080000300000000000", hexnat% "3800004000000000000", hexnat% "28008140240000000000000", hexnat% "10210201808000000000000", hexnat% "20020020000000000000", hexnat% "4004000000000000000000", 324259173170675712]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c17 c8
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c18 c7
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record014
