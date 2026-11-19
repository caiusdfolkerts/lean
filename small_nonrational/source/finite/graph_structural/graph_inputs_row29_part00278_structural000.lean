module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00278Data
public import GraphInputsRow29Part00278Frames
public import GraphInputsRow29Part00278Leaves
public import GraphInputsRow29Part00278Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00278.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278.record003
def vertexColumn : Fields := ⟨10, hexnat% "3e0f4cb2ac6b0ec3723c4f0bc1f32aaa9aa8e93a2eb26a99a68d9362db0ea398e9394e33a2e4b8ae8791e2785e0f8f1ca4e9366394e4b91e725394d58d5352d475c364d534cd8b52d2b46d8751d2745d0f72334e334ccb3c2e4b52ccb8ad2b2ae1b46c9b0ef0791d4731e2749ca785d1725c3783d0f23c4f0bc1f360b8350b4348ca2685a3189615a294a4590e625494550d45382d0b12c1b81d0711c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "126db4da6db6d36db4db6d36db49b4d249269249b6d26db6934db49249a4924924d249269a249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨97, by decide⟩, ⟨103, by decide⟩, ⟨109, by decide⟩, ⟨116, by decide⟩, ⟨119, by decide⟩, ⟨124, by decide⟩, ⟨125, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "309000020c02043068e1fc3f50000000", hexnat% "2448000010020000000000", hexnat% "130000000018000000000", hexnat% "980000000c000000000000", hexnat% "2080000000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "309000020c9f3c306000200750000000", hexnat% "2040000810420800000000", hexnat% "208000000000000c018000000000", 30992484007936, 63472607248252928]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9000020c01303060e99db750000000", hexnat% "9800000004200000000000", hexnat% "30000000000204000000000000000000", hexnat% "2448000810420800000000", hexnat% "2080000000000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300020000c264c0028f1e20a10000000", hexnat% "900002000000304000000140000000", hexnat% "980000000c000000000000", hexnat% "80000000000000018400000000", 30992484007936, hexnat% "130000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20800099303020ede18710000000", hexnat% "30000000000204000000000000000000", 33192581005312, hexnat% "2448000810000800000000", hexnat% "9000020c0000004000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "309020800c244c0028145e3e10000000", hexnat% "2000000304000000140000000", hexnat% "130000000018000000000", 65759591434027008, hexnat% "9a00000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9000020c24483068f5debb50000000", hexnat% "30000000000204000000000000000000", hexnat% "130000000010400000000", hexnat% "9800000008200000000000", hexnat% "2080000000000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9000020cbd7830681c430b50000000", hexnat% "30000000000204000000000000000000", 63507791620341760, hexnat% "2080000000000000008400000000", 30992484007936]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3090208008be48202814620b10000000", hexnat% "2040000104000000040000000", 65724407061938176, hexnat% "134000000000400000000", 32641751449600]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2080009f3030200c7dbf10000000", 67976207949365248, hexnat% "30000000000004000000000000000000", hexnat% "2048000800020000000000", hexnat% "9000020c0000004000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20424482028f5dfbf50000000", hexnat% "30000000000204000000000000000000", hexnat% "9800000008200000000000", hexnat% "900000080000104000000000000000", hexnat% "130000000000000000000", hexnat% "2080000000000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20800005302020fdfdbf50000000", hexnat% "9800100000000000000000", hexnat% "1000000000004c000000000000000000", hexnat% "42000000800020000000000", hexnat% "20000000000200000000000000000000", hexnat% "900002080000004000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9000020cbd78306814438b50000000", hexnat% "20002000000000000000000000000000", hexnat% "10000000000204000000000000000000", 31009663877120, 65759591434027008, hexnat% "80000000000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "309020820c2448306814438b50000000", 31009663877120, 65759591434027008, hexnat% "134000000000000000000", hexnat% "9a00000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9000020c0400306814418b50000000", hexnat% "20002000002000000000000000000000", 33191507263488, 65759591434027008, hexnat% "13c000000000400000000", hexnat% "9a00000000000000000000", hexnat% "10000080000040000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨116, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c19 c8
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c20 c7
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c21 c6
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c22 c5
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c23 c4
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c24 c3
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c25 c2
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c26 c1
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c27 c0
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00278.record003
