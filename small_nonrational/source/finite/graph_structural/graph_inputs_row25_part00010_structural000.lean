module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow25Part00010Data
public import GraphInputsRow25Part00010Frames
public import GraphInputsRow25Part00010Leaves
public import GraphInputsRow25Part00010Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00010.record068
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068
def vertexColumn : Fields := ⟨10, hexnat% "370bc3687a0f8d5334d332c372d2acb2a368bac9a5635a36c3a4e33a2e4b89e1783ed85e1d47319c5713c5c96a5693a4d92e479d1725c5655554d58d5353352d2745d0f72394cd38cccb4ac9b16c3bc1e4731e2749e1725c570dd0f23c4f0bc1fd1254532322c8aa858d12c549325292a5451550d134a324c3322c2b05c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db4d36d369a69b6db6db6db4924934da49b49a6da49269b6da492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a0100004088d14005f000000", 90071992547409920, hexnat% "38000020000000000", hexnat% "20400000000080020000000", 6442450944, hexnat% "4000006000014000000000", hexnat% "80000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a0000005c8c904009c000000", hexnat% "82000110000000000", hexnat% "20004020002000000", hexnat% "24000000000084000000000", hexnat% "1000000100000140000000", hexnat% "400000000000020000000", 16777216]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a00000000888000004000000", hexnat% "20400000000080020000000", hexnat% "10004020010000000", hexnat% "68000040000000000", hexnat% "1000000100000140000000", hexnat% "80040100080000000", hexnat% "4000006001014001000000", 167772160]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00010.record068

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00010.record094
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094
def vertexColumn : Fields := ⟨10, hexnat% "dc3683e2b49d0f4d326c3b0dc2f07cd49723c9aa5a8ea368ba1eb46958d6538ce2785ed8751cc6b19c571d27296a6695a4b91e745a9665a56558d4b51d70d9354d8b4ad1b49d1743dd0da358f1394d534ccb31cd8b52d2b2ac6b26c5b0ef0791d4785c5743c4f07f609c1689514a258562384ec86312c5292a6152548d24d0b22c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "126d36db6db6d36db49249349369349b6d249b6da69b6db6da6924d36db492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨89, by decide⟩, ⟨101, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220000fee0c3c0400220d800000", hexnat% "100000000400000000000000000", 377990676480, hexnat% "200010000000000000", hexnat% "20000000000010000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220000c6e08180000200d000000", hexnat% "100000000400000000000000000", hexnat% "300000000000002000000", 2595200384783876096, hexnat% "20000000000001800000000", hexnat% "200010004000000000", hexnat% "80040000000200800000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "202e26c3414017a0f800000", hexnat% "500000000000000000000", hexnat% "c000800000000000000", hexnat% "20000800000000000000000000", hexnat% "300000000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000202ee6c1c14017a07800000", hexnat% "100000000000000000000000000", 2305843009347911680, hexnat% "500000000000000000000", hexnat% "20000800000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "202ea6c1414017a07800000", hexnat% "500000000000000000000", hexnat% "4002800000000000000", hexnat% "300000000000000000000000000", hexnat% "20000800000000000000000000", 134217728]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100020222481004007207000000", hexnat% "200000008000000000000000000", hexnat% "240010000800000000", hexnat% "5c0000000000000800000", hexnat% "20000800000000000000000000", hexnat% "4002400010000000000", 576460752437641216]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000fe22c1c14006a0f800000", hexnat% "200000008000000000000000000", hexnat% "400000001000000000", hexnat% "4002000010000000000", hexnat% "100020000000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000006242c14016a01000000", hexnat% "200000028000000000000000000", hexnat% "300000000000002000000", hexnat% "480000001000000000", hexnat% "4c0000000000004800000", hexnat% "800001000000008000000", hexnat% "100020000000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fe208301000200f800000", hexnat% "220000000000000000000000000", hexnat% "100000000400000000000000000", hexnat% "c000800000000000000", hexnat% "200000005800000000", hexnat% "40404010200000000", hexnat% "20000000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "203e62c1414017a07800000", 2882303761651335168, hexnat% "c00000000000000000000", hexnat% "8400000000000000000", hexnat% "220000000000000000000000000", hexnat% "100000000000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000000ee6c0414017a07800000", hexnat% "20200000000000000000000", hexnat% "220000000000000000000000000", 4035225266258182144, hexnat% "500000000000000000000", hexnat% "800000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c6640414017a07800000", 4035225266258182144, hexnat% "200000028000000000000000000", hexnat% "300000000000000000000", hexnat% "c00000000000000000000", hexnat% "100020000080000000000000000", hexnat% "20000000000000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e60c3c14016a0f800000", hexnat% "c00000000000000000000", hexnat% "200000008000000000000000000", hexnat% "20000000000000000000000000", hexnat% "600000001000000000", hexnat% "100020000000000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fe20c301000600f800000", hexnat% "600000001000000000", hexnat% "300000000000000000000000000", 1127042368143360, hexnat% "c000800000000000000", hexnat% "20000000000000000000000", hexnat% "20000000000400000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200008ee0c3c14016a0f800000", hexnat% "500000000000000000000", hexnat% "600000001000000000", hexnat% "20200000000000000000000", hexnat% "300000000000000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3c2041414016a07800000", hexnat% "4002800000000000000", hexnat% "680000001000000000", hexnat% "c00000000000008000000", hexnat% "220000000000000000000000000", hexnat% "100020000000000000000000000", hexnat% "28000000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ce042c14012a0d800000", hexnat% "500000000000000000000", 343630938112, hexnat% "20200000000000000000000", hexnat% "20000800001000000000000000", hexnat% "680000000000000000", hexnat% "300000020000000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000c4e043c1400220d000000", hexnat% "300000020000000000000000000", hexnat% "20000000000011800000000", hexnat% "180000000000000800000", hexnat% "200000000000002000000", hexnat% "200000004000000000", hexnat% "480000000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000202022c0814017a05000000", hexnat% "100000000000002800000", hexnat% "28400000000000000000", hexnat% "4002400000000000000", hexnat% "220000000000000000000000000", hexnat% "4c0000000000000000000", hexnat% "800001000000008000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20302040814002207000000", hexnat% "c000000000000000000", hexnat% "4c0000000000000800000", hexnat% "220000000000000000000000000", hexnat% "100000020480000000000000000", hexnat% "200000005800000000", 2594074484877033472, hexnat% "800001000000008000000"]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c29 c26
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c30 c25
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c31 c24
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c32 c21
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c33 c18
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c34 c13
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c35 c12
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c36 c9
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c37 c2
  c38
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00010.record094
