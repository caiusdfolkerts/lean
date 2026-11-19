module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00029Data
public import GraphInputsRow24Part00029Frames
public import GraphInputsRow24Part00029Leaves
public import GraphInputsRow24Part00029Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012
def vertexColumn : Fields := ⟨10, hexnat% "8e9c6c9b168d94e2b86e2785e8e5c5c97158d54d2b46d2745dd0dc3c8f1352e2b2ac6b86c9b16f0761e2749ca719e1745c9715d0f3303c8c8ca0e946318362384e0b81e8c4c90e545314352344d0b41dc0d4330e2384c3322c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "49b4924926d2492492492492492492489249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b82e0249640000000000", 648520545364606976, hexnat% "1f000004000000000", hexnat% "40100400888000000000", hexnat% "7c00000000000000000", 18691697672192, 51228445761339392]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b82e0149460000000000", 720611124751368192, hexnat% "1f000004000000000", hexnat% "40100400888000000000", hexnat% "7c00000000000000000", 18691697672192, 51228445761339392]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "ffffffffffc000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record031
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031
def vertexColumn : Fields := ⟨10, hexnat% "7515c4f34a3ab1a8e93a2e9c639b16659362d94e4b86e4783ed24e9c6559366392e4e5c55553554d1b51d1743dd0ce3c4e938ccb3c2e4b52ccb8acab1ae1b46c9b0ef0751c6785d1725c3743c4f0bc1fc60b4c294a518c6298b186439314a52543530ca382c4b0ac8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b69a6da4db49b6db4da49b4db69a6da4924926d349b49a4c9249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3aff3fffffe1ffffc00000", hexnat% "100800000100000000000", hexnat% "400400000020000000000", 13194139533312]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3aff3f77fbe16dffc00000", 577604252986245120, hexnat% "400400000020000000000", hexnat% "100008000081000000000", hexnat% "800000000000000000", 4947802324992]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ae77f67fff4ef7fc00000", 576461851815051264, hexnat% "18000000000080000000", 10376293610181099520, hexnat% "4000000000a0000000000", hexnat% "100800000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3eff7fe37aefadf3c00000", 324259173304893440, 1730508165407047680, 299342040662016, hexnat% "100800000001004000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fe7bfe7fafa1f7ec00000", 1730508156817113088, hexnat% "10400000000081000000", 6459630813184, hexnat% "8000001000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3be73f6ffbf7ef7ec00000", hexnat% "400000000080000000000", 1154047404513689600, hexnat% "10400000000081000000", 9223372105574252544, hexnat% "8800000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "3fffffffffffffffc00000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c8 c9
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c8 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c8 c12
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c8 c13
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c14
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c8 c15
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c8 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c17 c11
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3bffbf777bffff7fc00000", 36028797018963968, 577586652210266112, 9223372039002259456, hexnat% "400400000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3befbf67faf2df7ec00000", 282711944069120, 1730508156817113088, 9223380835095281664, hexnat% "10400000000000000000", hexnat% "400000000040000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3be7bf67fae24d7ac00000", hexnat% "400400000000000000000", 10376293610181099520, hexnat% "18000000000080000000", 577604253053353984, 282711944069120, 13743895347200]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c24 c6
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c25 c5
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c26 c4
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c27 c3
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c28 c2
  c29
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record031

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record038
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038
def vertexColumn : Fields := ⟨10, hexnat% "1f362d4a72ca96ac695a8e87a35a361d94e2b86e1783ed87519c7295a719566391e4d58d475534ad1b45d0f743c8e6358f13a4e5354cd38cc73c2d8b52e2b4acab1ae1b46c5b0ed4731e2729e170dd0f13c9c26866258562382e07899194951548d0b41dc0d4388c6384c9314d0b22c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6d34d249b6db6da69a492492492492492492492492449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840043ddfff9780000000", hexnat% "2000100000002000000000", hexnat% "200010000000800000000", 153122662208503808, hexnat% "18000c000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1727130343279951872, 578712620836585472, hexnat% "2000100000000200000000", hexnat% "200010000000800000000", hexnat% "4e000000000000000", hexnat% "9c0000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2bc005ff7ef9ff80000000", hexnat% "100000000000000000", 288072046477312, 36028797018963968]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bc0059f7ef9ff80000000", hexnat% "2000100000000000000000", 288072046477312, 36028797018963968, 6917529027641081856]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c4 c2
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "280014167689ff80000000", 411217348788224, hexnat% "1e000000000000000", hexnat% "3c0000000000000000000", 686798943174000640]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20001002010c980000000", hexnat% "2000100010002600000000", 704817739729993728, hexnat% "840042004000000000000", 1153944050420678656, hexnat% "18000c000090000000000", 432416001691222016]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c9 c1
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c10 c0
  c11
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record038
