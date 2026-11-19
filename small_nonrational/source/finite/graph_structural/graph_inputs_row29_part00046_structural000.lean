module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00046Data
public import GraphInputsRow29Part00046Frames
public import GraphInputsRow29Part00046Leaves
public import GraphInputsRow29Part00046Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000
def vertexColumn : Fields := ⟨10, hexnat% "ec3a8e51ac5b0ec6715c37332aca72caaaac5a964b8ae1b91e2785ee8791cc6b16c6715c4f1e2729aa5a95a4e966559367856956539715a5595554d56354d3352d2b46d4749d17723a8e63c4e9394e334ccb31cf0ba2e2b4acab46c9b16f07a1d2729c6785d1725d0f23c2f07c6a1584ec86a1c46914a4a91a515254554348d1362318e1314c4b0ac4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6db6d369249b6da4926db6da4924924924924926d36926d36da492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3c1f004fff907005e000000", hexnat% "240000000000002100000000", 598136472993792, hexnat% "180004000020000000", hexnat% "30000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3c1f004fff507003e000000", hexnat% "240000000000002100000000", 598136472993792, hexnat% "180008000040000000", hexnat% "30000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "27004004ffe000211e000000", hexnat% "1b00000000e0000000", hexnat% "1b0000000070000000000", hexnat% "c000000001200000000000", 5066549580791808, 3377699720527872]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24007000ff9007211e000000", 879611449704448, hexnat% "20180000060000000000000", hexnat% "1f0000000060000000", hexnat% "1c00000000c000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24000007ff820021fe000000", 4824657022681088, hexnat% "1000018000c000000000000", hexnat% "1f0000000030000000000", hexnat% "2c000000060000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24017000ff8003211e000000", hexnat% "20080000060040000000000", 5383208929591296, hexnat% "1f00000000e0000000", hexnat% "1c00000000c000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2400f000ff8003211e000000", hexnat% "20100000060040000000000", 5383208929591296, hexnat% "1f00000000e0000000", hexnat% "1c00000000c000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24000017ff8000217e000000", hexnat% "1000008000c000080000000", 5383208929591296, hexnat% "1f0000000070000000000", hexnat% "2c000000060000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24007000ff8003211e000000", hexnat% "20180000060040000000000", 5383208929591296, hexnat% "1f00000000e0000000", hexnat% "1c00000000c000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "26c180009e79062156000000", 598136472993792, hexnat% "70000000010000000000", 7025615418832191488, hexnat% "10000180004000000000000", hexnat% "70000000020000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "240000009e40002106000000", 7025615419100626944, 5383208929591296, hexnat% "1f0000000070000000000", hexnat% "2c000000020000000000000", hexnat% "1f00000000e0000000", hexnat% "1000000000c000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c16 c7
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c19 c4
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002
def vertexColumn : Fields := ⟨10, hexnat% "2785d0ec1f3a2ccab29c972caaaa9a8ea96a3a1eb86c5a9655b0ea38ce8785ee8731ac571ca6a93a6391e5a5594e5555352d4753352d2b46d1743de0f23a8da358ce3c4e9354e334ccb31cf0ba2ccb8ad2b2ac6b86c5b0ed8751cc725d0f07f30aa312a29161588e139311c4a91a5151548d1351314c8b12d0721c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db4db69b6db4d349a69a6934db49a4d24db6db4d34d349b49a692491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7bfffbb7af7ff5fffe000000", hexnat% "4400000000000000000", hexnat% "81080020000000000", 4611694814520410112, hexnat% "840000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7bf7eab72f7f55fffe000000", hexnat% "40000400000000000000000", hexnat% "10080080000000000000", hexnat% "800800000000880000000000", hexnat% "5004000000000000000", 10376330924856967168]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffbff3fdffdfffff7b2000000", 1275068416, hexnat% "200200000800000000", hexnat% "40080000000000000000000", hexnat% "40000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffff5faffbfffdfffb6000000", 1207959552, hexnat% "5004000000000000000", hexnat% "a00000000200000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffff5badfbdffdffffe000000", hexnat% "200200000000000000", hexnat% "5004000000000000000", hexnat% "40000000000000000000", hexnat% "a00000000200000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7ff53a9fbdffd77ffe000000", hexnat% "600200000000000000", hexnat% "c0000000008000000000", hexnat% "800800000000080000000000", hexnat% "201000000200000000000", hexnat% "4004000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "1ffffffffffffffffffe000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffffbfbfffff7ffe000000", 4611686018427387904, hexnat% "400000008000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c11 c15
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c11 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffffbfeffffffefe000000", hexnat% "400000000000000000", 1152921508901814272]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffffbfafffff7efe000000", 1152921508901814272, hexnat% "400000008000000000", 4611686018427387904]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffbff7bb7affff57efe000000", hexnat% "40080000000008000000000", hexnat% "81000020100000000", hexnat% "4004000080000000000", hexnat% "400000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7bff3b97acfff572fe000000", hexnat% "c0000000008000000000", hexnat% "4004000080000000000", hexnat% "81100000100000000", hexnat% "600200000800000000", hexnat% "840000000000020400000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c11 c10
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffff7ffffffffffffb6000000", hexnat% "800000000000000000000", 1207959552]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffffff7dfffff7b6000000", 1207959552, 144115222435594240, 9223372036854775808]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffbf77fdff5fffff7ba000000", hexnat% "880000000000000000000", 1140850688, hexnat% "40000000000000800000000", hexnat% "200a00000000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffbedf35ffffffb2000000", 1275068416, hexnat% "100c000000000000000", hexnat% "200a00000000000000", hexnat% "40000000000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7ff73e9f35ff7777fe000000", hexnat% "100c000080000000000", hexnat% "880000000000000000000", hexnat% "800000000000800000000000", hexnat% "40200800000000000000", hexnat% "400200008800000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c36 c33
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7bfffbb7fcfffff3fe000000", hexnat% "80100000400000000", hexnat% "4400000000000000000", 144115222435594240, hexnat% "840000000000000000000000"]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffff7bbffdffff7fba000000", hexnat% "80000000008000000000", 1140850688, hexnat% "400200000000000000", hexnat% "4000000000000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7bff6b97f4ffff77fe000000", hexnat% "10080000000000000000", hexnat% "800004000000000000000000", hexnat% "40080000000008800000000", hexnat% "200b00000000000000", hexnat% "400000000000000000"]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c41 c38
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffaaf72effffff80000000", hexnat% "81100000000000000", hexnat% "5004000000000000000", hexnat% "50000000000012000000", 1811939328, 9223372036854775808]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7bf77f9ff4ff7f7bb2000000", hexnat% "800800000000800000000000", 1275068416, hexnat% "200900000400000000", hexnat% "40080000000008000000000", hexnat% "400200000000000000"]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c11 c10
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffffbfffcfffffffe000000", hexnat% "4000000000000000000", 216172782113783808]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffffbf7fcff7ffffe000000", hexnat% "4000000800000000000", 216172782113783808, hexnat% "80000000000000000"]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c48 c47
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7ff7fbb7fcff7ffbfe000000", 216172782113783808, hexnat% "80000000400000000", hexnat% "800800000000800000000000", hexnat% "4400000000000000000"]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c50 c49
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7bf7fbb7acff75fbfe000000", hexnat% "800800000000880000000000", hexnat% "400200000000000000", hexnat% "81100000000000000", hexnat% "4004000000000000000", hexnat% "40000000000020400000000"]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c52 c51
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffef9724ffffff80000000", hexnat% "600200000000000000", 14987979559889010688, hexnat% "10080000000002000000", 2080374784, 648518346341351424]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffbf77bbf3fff777f82000000", hexnat% "880000000000000000000", 2080374784, 13835066851375185920, hexnat% "40000400000008000000000", hexnat% "4000000800000000000"]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffbffef9ff7fffd7b80000000", hexnat% "40000000000020400000000", hexnat% "400000008000000000", hexnat% "10000000000032000000", hexnat% "200800000000000000", 1275068416]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffef9fe4ffffff80000000", 1369094286720630784, hexnat% "600000000000000000", hexnat% "10000000000032000000", 1275068416, 576460752303423488]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffbf76fff7ffffdfb80000000", hexnat% "40000000000020400000000", hexnat% "880000000000000000000", hexnat% "10000000000032000000", 9223372036988993536, 1140850688]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffbffeb9f66ff7d7b80000000", 10376295740484878336, hexnat% "4400000808000000000", hexnat% "10000000000032000000", hexnat% "200900000400000000", 1275068416, hexnat% "40000000000000000000000"]
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c59 c58
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c60 c57
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c61 c56
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c62 c55
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c63 c54
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c64 c53
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c65 c44
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c66 c43
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c67 c42
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c68 c37
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c69 c26
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c70 c9
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c71 c2
  c72
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007
def vertexColumn : Fields := ⟨10, hexnat% "5e2b43b13c2f07ce8b329c972e29aa5a8eac695a4e87aa98e68d9361d8ce4b8ae1b91e1783ee8731ac6715c789c6699566a5396958d5352d4753351d27783c8ea368e6358ce3c4e5354e334cc73c2e8b62d4b32e1b46c5ba1cc789d2729c6785d1715c3743c1fcc07417322a88a61988e13b11464591548d1341dc0e8342c8b12c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da49b6db6db49b49a4d369b6d34db6da49249b6d36db4924d249b49b4d2249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [1, 2, 3, 4]
def candidates : List (Fin raw.n) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c1 c2
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f7fffb7ffffdffffffffffffff", 144115188075855872, hexnat% "8000000000000000000000000", hexnat% "480000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c4 c2
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c5 c3
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e7ffbb7fdfef7ff7ffbfffffff", hexnat% "200000080000000000", hexnat% "8000000000080000000000000", hexnat% "10000000001000000000000000", hexnat% "4480000000000040000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e7ff7ffffffefff7ffffffffff", hexnat% "10000000000000000000000000", 72066390130950144, hexnat% "8008000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e7ff7fffdfee3ff7ffffffffff", hexnat% "200000080000000000", hexnat% "10000000001000000000000000", hexnat% "8008000000040000000000000", 108086391056891904]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e7ff3a7ffffefff3ffffffffff", 72070788177461248, hexnat% "8008000000000000000000000", hexnat% "10000180000000000000000000", hexnat% "4400000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e7ff7effdffefff3ffffffffff", hexnat% "10000100000000000000000000", hexnat% "2000000c0000000000", hexnat% "8008000000000000000000000", 72057594037927936]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e7ff3a7fdfee3ff3ff7fffffff", hexnat% "2000000c0000000000", hexnat% "10000000001000000000000000", hexnat% "4580000000000000000000", hexnat% "80000000001c0000000000000", hexnat% "8000000000000080000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c17 c8
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "3ffffffffffffffffffffffffff"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c1 c19
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c1 c20
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .size 1
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c1 c22
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c1 c23
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c1 c24
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c1 c25
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c26 c21
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efff7fffffefbffcffffffffff", 3298534883328, hexnat% "8000000040000000000000", hexnat% "10000000001000000000000000"]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3effffffff7e8fff4ffffffffff", hexnat% "10000000001000000000000000", hexnat% "80600000000000000", 12094627905536, 72057594037927936]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e7ff77dbdfee3df4dfffffffff", hexnat% "8008000000040000000000000", hexnat% "10000820001000000000000000", 12232066859008, hexnat% "4200002000000000000", 108086391056891904]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f7ff3efbdffe3ff0777dffffff", hexnat% "4200000000000000000", hexnat% "c100000000000080000000", hexnat% "80000000001c0000000000000", 17042463784960, 34359738368]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f3ffffffd7f0fdf45ffcffffff", hexnat% "8000000000100020000000000", 1008806316581322752, hexnat% "280000002000000000", hexnat% "4000000000002000000000000", 10445360463872]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e7ff3a7bffee3ffbf7bfffffff", 90076424953659392, hexnat% "10000000001000000000000000", hexnat% "4000080000040000000", hexnat% "8008000000000000000000000", hexnat% "4580000000000000000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c1 c22
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c1 c37
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c1 c38
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c1 c39
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fbfffffbf7fffffeffbfffffff", hexnat% "4000000000040000000", hexnat% "80000010000000000", hexnat% "4000000000000000000000000"]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c1 c0
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c1 c43
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c1 c44
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fbfffffbf7effffeffffffffff", hexnat% "80000010000000000", hexnat% "4001000000000000000", hexnat% "4000000000000000000000000"]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fbff76fbdfefffffffbfffffff", hexnat% "8100000000000000000000", hexnat% "4200000000000000000", hexnat% "4000800000000000000000000", 1152921505680588800]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c48 c47
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c49 c42
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efff767ffffffff8f7ffffffff", hexnat% "10000880000000000000000000", hexnat% "8100000000000800000000", 7696581394432]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e3ff767fffefbffff7bfffffff", hexnat% "c000000000000000000000000", 1170935904190070784, hexnat% "8100000000000800000000", hexnat% "10000880000000000000000000"]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e3ff767bffeffdffffbfffffff", hexnat% "8008000000000000000000000", hexnat% "4000004000002000000000000", hexnat% "10000180000000000000000000", hexnat% "800001000000040000000"]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffff7ff7fffdf6ffffffffff", 571746046443520, hexnat% "80000010000000000", hexnat% "80000000000000000000"]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fbff7e7ffffffdf5f7ffffffff", hexnat% "180000000000000000000", hexnat% "4000000000002000000000000", hexnat% "8000000000000800000000", 10995116277760]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c55 c54
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3effff77bf7fffdf6ffbfffffff", hexnat% "80000010000000000", 571746046443520, hexnat% "4000000000040000000", hexnat% "10000880000000000000000000"]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ebff767bffffbdf5f7bfffffff", 10995116277760, hexnat% "8000000040000800000000", hexnat% "4000004000002000000000000", hexnat% "10000180000000000000000000", hexnat% "800000000000040000000"]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c58 c57
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c59 c56
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c60 c53
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c61 c52
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c62 c51
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c63 c50
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ebffb27fdffffdf47ff5ffffff", hexnat% "200002080000000000", hexnat% "10000180000000000000000000", hexnat% "4000800000000000008000000", 3848324251648, hexnat% "4400000000000000000000"]
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c1 c19
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c1 c66
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c1 c67
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffff7ffff7f8ffffffffffffff", 72057594037927936, hexnat% "8000000000000000000000", hexnat% "80600000000000000"]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c69 c68
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffff7ffff7e9ffffffffffffff", 1152921504606846976, hexnat% "8000000000000000000000", hexnat% "80600000000000000"]
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c71 c44
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffff7effd7e9ffffffbfffffff", 1152921505680588800, hexnat% "8100000000000000000000", hexnat% "80600000000000000", hexnat% "200000000000000000"]
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c73 c72
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c74 c70
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efff3e7fd7efffffffbfffffff", hexnat% "280000000000000000", 1152921505680588800, hexnat% "c100000000000000000000", hexnat% "10000080000000000000000000"]
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffff7fffffeffffcf7ffffffff", 1152921504606846976, 3298534883328, hexnat% "8000000000000800000000"]
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c77 c44
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffffffffeefffcffbfffffff", 1152921505680588800, 3298534883328, 72057594037927936]
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c1 c24
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffbfffffffffcffffffffff", hexnat% "400000000000000000000", 3298534883328]
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c81 c80
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c1 c20
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c83 c83
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3effffbfffffffffcffbfffffff", hexnat% "10000000000000000000000000", hexnat% "400000000000040000000", 3298534883328]
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c85 c84
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c86 c82
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efffbbffffeefffcf7bfffffff", 3298534883328, hexnat% "10000000001000000000000000", 72057628397666304, hexnat% "4400000000000040000000"]
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c88 c87
  let c90 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c89 c79
  let c91 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c90 c78
  let c92 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efff3a7fffeefff0f7bfffffff", hexnat% "10000000001000000000000000", hexnat% "8100000000000800000000", hexnat% "4480000000000040000000", 16492674416640, 72057594037927936]
  let c93 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c92 c91
  let c94 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c93 c76
  let c95 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c94 c75
  let c96 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f7fffffbd7f87df0f7fcffffff", 72064225467432960, hexnat% "8000000000080000000000000", hexnat% "80600000001000000", hexnat% "4200002000000000000", 9895638204416]
  let c97 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e7ff727bdfee7dfff7b7ffffff", hexnat% "8100000000000800000000", hexnat% "4200002000000000000", hexnat% "480000000000040000000", hexnat% "8000000000180000000000000", hexnat% "10000800001000000008000000"]
  let c98 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3effff37bd7e9ffff7fb4ffffff", hexnat% "400000000008003000000", hexnat% "4200000000000000000", hexnat% "80600000000000000", hexnat% "10000800001000000008000000", hexnat% "80000000000040000000"]
  let c99 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e7ff7a7ff7f9fff977fdffffff", hexnat% "80600000000000000", hexnat% "8008000000000000000000000", hexnat% "10000180000000000000000000", 7181185318912, hexnat% "400000000000002000000"]
  let c100 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3effff37bd7e97fffffb7ffffff", hexnat% "80600000000000000", hexnat% "4001080000040000000", hexnat% "200000000000000000", hexnat% "480000000000000000000", hexnat% "10000800000000000008000000"]
  let c101 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e7ff767bffef7ffff7b7ffffff", hexnat% "8100000000000800000000", hexnat% "8000000000080000000000000", hexnat% "4001000000040000000", hexnat% "10000880000000000008000000"]
  let c102 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3effffeffd7f9fff377feffffff", hexnat% "10000100000000000000000000", 13743895347200, hexnat% "80600000001000000", 34359738368, hexnat% "200000000000000000"]
  let c103 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3effff27bd7e97ff377f6ffffff", hexnat% "80600000001000000", hexnat% "4001080000000000000", 4982162063360, hexnat% "200000080000000000", hexnat% "580000000000000000000", hexnat% "10000800000000000008000000"]
  let c104 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c103 c102
  let c105 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c104 c101
  let c106 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c105 c100
  let c107 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c106 c99
  let c108 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c107 c98
  let c109 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c108 c97
  let c110 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c109 c96
  let c111 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c110 c95
  let c112 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c111 c65
  let c113 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c112 c64
  let c114 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c113 c36
  let c115 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c114 c35
  let c116 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c115 c34
  let c117 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c116 c33
  let c118 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c117 c18
  c118
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record007
