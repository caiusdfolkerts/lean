module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00026Data
public import GraphInputsRow16Part00026Frames
public import GraphInputsRow16Part00026Leaves
public import GraphInputsRow16Part00026Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001
def vertexColumn : Fields := ⟨10, hexnat% "ab2aa4eaa655936a38ce8b8ae1b89e1783eaa539c96a555535a364d3362d2b46d8749d1743da8d534ce8b32e2b4acab1ad1b26c3ba1d8751cc789ca719c970de0f23c4f0bc1f1692645856a262916685895254545548d1314c8b12c2b06d0721c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db49b6db4d34924da6db4da492492492492493492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ac9080c3fef000000", 3458764513820540928, hexnat% "c000000000000000000", 423586854600704, 125894081380352]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a49087fc10f000000", 9223372048129064960, hexnat% "4001000801800000000", 155692564480, hexnat% "8002001000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "808290905bfef000000", 10376293541461622784, hexnat% "4000000804000000000", hexnat% "24000000000000000", 63771674411008, 70368744177664]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2c9007effef000000", 423311976693760, hexnat% "4001000000000000000", 2308094809027379200, hexnat% "8080000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "808b9094e3fef000000", hexnat% "24000000000000000", hexnat% "4000000804000000000", 36833639530496, 17592186044416]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ac9004e3fef000000", hexnat% "8002001000000000000", 37108517437440, 2251799813685248, hexnat% "4001000800000000000", 17592186044416]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2c1007ee3c2000000", 423312530341888, 120460410880, hexnat% "80808000000000000", hexnat% "4001000000000000000", hexnat% "8002000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [13907173098517430272, hexnat% "8002001000000000000", hexnat% "20800400000000000", hexnat% "4001000804000000000", 12644383719424, hexnat% "80008000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "249001405c0000000", 10376293550588428288, hexnat% "8002001000801000000", hexnat% "4000000801000000000", 70506317348864, 48103633715200, hexnat% "80008000006000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015
def vertexColumn : Fields := ⟨10, hexnat% "730bc72a5a719a68d98e538ce2b83eb85c9964b9715a58d4b56354d334ad2743dd0dc368e6338e5362e4b52ccb2ae1b16c3b61d4731e2749ca785d1743c8f13c2f8c836079c18c4c9614a50d48d0764350e2384c3312c1b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db4db69a6d249349249a69a49a492692492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "810a2008f7fc00000", 23158463660032, 211381110439936, 219550481834311680, 18295873486192640, 4611686018427387904]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1381549843129827328, 18858823439613952, hexnat% "84000000408000000", 164376988352512, 36028798092705792, 103087603712]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [164781986152448, hexnat% "84000000000000000", 1297107061426880512, 4898947072, 54324670773592064, 85005442966618112]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [139400802052603904, 1297036692682702848, hexnat% "84000000408000000", 142391050764288, 22058952032256]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1381692263645577216, 18858823443808256, 1811939328, hexnat% "80080000400000000", 22058952032256, 4611686018427387904]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "843e7000e7b400000", 1155173579298439168, 4370464768, 23158463660032, 211655988346880]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "802c0000e5b000000", 85005442966618112, 1152992697984745472, 4911529984, 23158463660032, 4611967493404098560, 140737488355328]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c9 c3
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c10 c2
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c11 c1
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c12 c0
  c13
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record015
