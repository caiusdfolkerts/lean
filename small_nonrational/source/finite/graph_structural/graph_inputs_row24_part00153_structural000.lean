module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00153Data
public import GraphInputsRow24Part00153Frames
public import GraphInputsRow24Part00153Leaves
public import GraphInputsRow24Part00153Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00153.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002
def vertexColumn : Fields := ⟨10, hexnat% "6e2744f0bc6c9aa5a8ea6693a2ea564d8b61da4e4b8ae1b91e2783e6c6716a5693a5994e4b9996558d5352d4759352d2b51d2743d68d6338f13a4d9394d332cc7362e4b52ccb4acab1ad1b26c3b49ca719d1725c570de0f43c8f0bc1f1b2468584e4c4b14a4a91a645196150d44d0b64384d1324d0b22c4b81c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6da6da6d36d349349249249369b6924934924924db492492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11000044000ff857c000000", hexnat% "318000000800000000", hexnat% "ec02400000000000000", hexnat% "200000006000080000000", 33777005795213312, hexnat% "200a0000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11000022000ff837c000000", hexnat% "318000000800000000", hexnat% "ec04400000000000000", hexnat% "200000006000080000000", 33777014385147904, hexnat% "200c0000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2eff6404098134000000", hexnat% "11000000000000040000000", 200111250472960, 32088175262302208, hexnat% "200008000000800000000", 2322168557862912]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ecf647e8f87fc000000", 123145302310912, hexnat% "1200008000000800000000", hexnat% "10000100000000000000000", hexnat% "200000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ecf647e8f87fc000000", hexnat% "10000100000000000000000", 123145302310912, hexnat% "208000000800000000", hexnat% "1200000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ecc647eff87fc000000", hexnat% "20030000000000000000", hexnat% "1200008000000800000000", hexnat% "10000100000000000000000", hexnat% "200000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1120c9de07e0f8ffc000000", 263882790666240, hexnat% "200400000000000000", hexnat% "2400000000000000000", hexnat% "20020000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1120c8c607e0187f4000000", hexnat% "20420400000000000000", hexnat% "318000000800000000", 266081813921792, hexnat% "20000000c0008000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ec06410ff847c000000", hexnat% "11000000000000100000000", hexnat% "200008000000800000000", 29273406167842816, hexnat% "390000000000000000", hexnat% "60006000080000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ec66402bf843c000000", hexnat% "390000000100000000", hexnat% "11000000000000040000000", 32651108035854336, hexnat% "200008000000800000000", 2322168557862912]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ecf647e8f87fc000000", 123145302310912, hexnat% "10000100000000000000000", hexnat% "208000000800000000", hexnat% "1200000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1208cae07eff8ffc000000", hexnat% "10000110000000000000000", hexnat% "20040400000000000000", hexnat% "200000000000000000", hexnat% "6000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "228cf647e8187f4000000", hexnat% "11000000000000000000000", hexnat% "308000000800000000", 125344325566464, hexnat% "60000000c0008000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c17 c3
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c18 c14
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1002eff6408818ffc000000", 68169720922112, 33214047251857408, hexnat% "1200008000000000000000", 70368744177664]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ec06400ff867c000000", hexnat% "11000000000000100000000", hexnat% "318000000800000000", hexnat% "200000006000080000000", 33776997205278720, hexnat% "200e0000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11200f1840eee0ffc000000", 19241453486080, hexnat% "200e0000000000000000", hexnat% "e006000000000000000", 31525197391593472]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28cf047ea18fb4000000", hexnat% "308000000000000000", hexnat% "11000000000000040000000", 90159953477632, hexnat% "2000000000c0008000000", hexnat% "6006000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ec06410ff8e7c000000", hexnat% "1200008000000000000000", hexnat% "390000000100000000", hexnat% "10000000008000000000000", 28710449771970560, hexnat% "20060000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f90410b00f30000000", 27023247098773504, hexnat% "1000008000400040000000", hexnat% "10000000008000000000000", hexnat% "20060006000080000000", hexnat% "e0060000e0008000000", hexnat% "200000000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c27 c22
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c28 c21
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c29 c20
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c30 c19
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c31 c13
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c32 c12
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c33 c11
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c34 c2
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c35 c1
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c36 c0
  c37
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00153.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00153.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004
def vertexColumn : Fields := ⟨10, hexnat% "2781f1723aa5a1e9a64d8b61d92e2b86e8785e0fa715c6693a6598e479694b51d52d1b61d1743d68d6338f1354d332cc73a2ccb4acab1ae1b16c3b61d2729c6785c9715c3783d0f13c2f07d342b2529291623a514c471924a91a525295150d48d0b64384d1314e0b22c4b41c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36da6d36d36da49269249369b6926926924d24d2492491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffffffbdefffe0000000", 580542139465728, 18014398509481984]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c3 c4
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1efdfffffedefffe0000000", 580542139465728, hexnat% "20000010000000000000", hexnat% "1000000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1eddffe9bec9fffe0000000", hexnat% "1000000400000000000000", hexnat% "16000000000000000", 949978046398464, hexnat% "220000010000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1efdfffffbfafffe0000000", hexnat% "20000000400000000000", 18031990695526400, hexnat% "1000000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c11 c5
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c12 c2
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1eddfcf9ffc9fffe0000000", hexnat% "206000000000000000", hexnat% "220000000600000000000", hexnat% "1000100000000000000000", 844424930131968]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1eddf8bff8887ffe0000000", 870813209198592, 32651097298436096, hexnat% "220000000600000000000", hexnat% "1000140000000000000000", hexnat% "600000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fdde1c1f889e4020000000", hexnat% "3e000000000000000", hexnat% "600001200000000000", hexnat% "1800024000000000000", hexnat% "220000010418440000000", 562964985806848, 18014639027650560]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c19 c18
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00153.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00153.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005
def vertexColumn : Fields := ⟨10, hexnat% "5e2744f07c5c9aa5a8ea5693a1ea564d8b61da4e4b8ae1b91e1783e9c5716a5693a5594e479996558d5352d4759352d1b51d1743d68d6338f1354d332cc7362e4b52ccb4acab1ad1b16c3ba1e4749ca719d1725c570de0f43c4f0bc1f2b2528588e945311c5292a469296150d48d0b64384d1314d0b22c4b81c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6da6db69b6d249349a49269369b69269249249349a692492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffffbdfeffffffffffc000000", hexnat% "400000000000000000000", hexnat% "20100000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffeffdfefffffff3fbc000000", 825707462656, hexnat% "20100000000000000000", hexnat% "10000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffffddffffffeffffc000000", hexnat% "20000000000000000000", hexnat% "2000000100000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffffbddefffffeffffc000000", hexnat% "20100000000000000000", hexnat% "2000000100000000000", hexnat% "400000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c10 c4
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffefbd9effffbe7fffc000000", hexnat% "20100004000000000000", hexnat% "10000000000000000000000", hexnat% "6000000180000000000", hexnat% "400000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffefbc1e29ffbe76d74000000", hexnat% "10000112000000000000000", 629346926592, hexnat% "300c0000000000000000", hexnat% "400000004180000000000", hexnat% "e004000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffeffffe0ffffbf3f8c000000", 70370623225856, hexnat% "f0000000000000000", hexnat% "10000100000004000000000", 549755813888]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffeffffe0fffdff3f8c000000", 562951832469504, hexnat% "f0000000000000000", hexnat% "10000100000004000000000", 549755813888]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffefbffeffffd873f8c000000", hexnat% "10000100000004010000000", hexnat% "400000000380000000000", 551366426624, 633318697598976]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffefbff3b9bfd872f84000000", hexnat% "400000000381008000000", hexnat% "10000002000004010000000", 551366426624, hexnat% "c44400000000000000", 633318697598976]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c22 c17
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffffbc1309be8056900000000", hexnat% "400000014381088000000", hexnat% "300d0000000000000000", 577203339264, 1057730454355968, hexnat% "26400000000000000", hexnat% "ec00000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c25 c16
  c26
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00153.record005
