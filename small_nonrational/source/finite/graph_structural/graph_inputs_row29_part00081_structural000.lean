module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00081Data
public import GraphInputsRow29Part00081Frames
public import GraphInputsRow29Part00081Leaves
public import GraphInputsRow29Part00081Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00081.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record000
def vertexColumn : Fields := ⟨10, hexnat% "bc1e8d62e4b52b49d0f43b25c37362d4a723c96a3a95a36b26998e6958d68d8b61d8ce4b8ae1b89e17b61b85e1d46d1ac6713c749725a95a4e9c6659564d9c96a5a56352d70d4b4ad87743c8e6358ce3c4e5354cd38ccb31cd4b32d2b2ac6b46c9b16f0789d2729e1725c3743c8f0bf603609c5894a1681ec8499894a5854952341d48d0b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db49b69a4db6db6db6926db6db6db6da4924da4d34db6db69a6d24d2492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨94, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c58007000109a8053afe00000", 864691128723570688, 216172782113783808]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "448005000009a80533fe00000", 504403158265495552, hexnat% "8000000001000000000000000", hexnat% "100020000000000080000000", 576460752303423488]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c08006000009800030be00000", 216172782180892672, hexnat% "500000000000004000000000", 703756429688832, 864691128992006144, hexnat% "10001000000080000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000000079800102f600000", hexnat% "4000010000002800000000000", 576460752580247552, hexnat% "100000000000004280000000", hexnat% "8080060000000000100000000", 1152921504606846976]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8080060000010000100400000", hexnat% "500000000000004000000000", hexnat% "4000010000002800000000000", 254453379063873536, 77319897088, 864691129394659328, 1152921506754330624]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c7 c4
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00081.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00081.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record005
def vertexColumn : Fields := ⟨10, hexnat% "dc2f0da2e8b62b89e0f8d5334d332c970dc8f332ca8da8e8bac9b16558d68d936c394e33a2e4ba1e2785e0fb6178751cc6715c4f1d27299a5693a659366392e479d1725c5655554d58d535c364d534cd8b52d8749d1743d70da354cd34cd4b32d2b26c5b0ed4731d2745c9715c3743c8f13c2f07f449524c2c8aa344b1324a9514551352328c930cc8b0ad0705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6d34d36db69b6db6db6db6db6da6db4d34d36926da49b6d369a4d24d2692492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨72, by decide⟩, ⟨94, by decide⟩, ⟨101, by decide⟩, ⟨103, by decide⟩, ⟨105, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "204000010aa71c200b08a00000", hexnat% "280000000000000000000000000", 1236950581248, 5017666846720, 855638016]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10a8000200800000000", hexnat% "400000000000040200000000", hexnat% "2a0000000002410000000000000", 619620335616, 219550481834311680, 1241388154880, 857735168]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00081.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00081.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record006
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
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000fe0cd1740df000000", hexnat% "a00000000800000000000000", hexnat% "24000000000080000000000", 72057598332895232, hexnat% "400000000000020000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a010000c088d14005f000000", 90071992547409920, hexnat% "38000020000000000", hexnat% "20400000000080020000000", 6442450944, hexnat% "4000006000014000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000de0c91541ff000000", hexnat% "20004020000000000", hexnat% "20400000000080000000000", hexnat% "a00000000800000000000000", hexnat% "1000000100000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a0000005c8c904009d000000", hexnat% "82000110000000000", hexnat% "1000000100000140000000", hexnat% "20004020002000000", hexnat% "24000000000084000000000", hexnat% "400000000000020000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2440002000c0f403f000000", hexnat% "58000000000000000", hexnat% "a00000000880000000000000", hexnat% "1000000100000140000000", hexnat% "80040100080000000", 6917810502617792512]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a010000089c90f41df000000", hexnat% "20400000000000020000000", hexnat% "4000006000000000000000", hexnat% "80000100000000000", hexnat% "70004000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a0400004e9c90740df000000", hexnat% "30004000000000000", hexnat% "80000100000000000", hexnat% "20400000000080020000000", hexnat% "1000000000000100000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a000000089c907409f000000", hexnat% "70004000000000000", hexnat% "86000100000000000", hexnat% "24000000000080000000000", hexnat% "1000000000000140000000", hexnat% "400000000000020000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a0000000088800000e000000", hexnat% "10004020010000000", hexnat% "20400000000080020000000", hexnat% "68000040000000000", hexnat% "1000000100000140000000", hexnat% "80040100080000000", hexnat% "4000006001014001000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c15 c2
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00081.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00081.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record016
def vertexColumn : Fields := ⟨10, hexnat% "370da2d89e0f8d5174d316c970dc1f3325c8f2ca96a3a8da8e8ba1e9c659956359361d94e3392e1b89e1783ed8751b47319c5713c749b27299a5693a699964d98e4b91e74571565c5655554d54d475c364d534cd4b46d8749d1743dc8f138cd332cf0b8ad2b2ae1b26c3b61d2745c3743c2f07f609c268350cc2588ec86318a4952352324c3322c2b41c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "24d36db69b6db6db6db4db4da6d36936da4db6d36db6da6db69b69b4d24d24d2492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨52, by decide⟩, ⟨61, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨87, by decide⟩, ⟨102, by decide⟩, ⟨109, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40008900000000040000000000", hexnat% "22080010400000000000", hexnat% "1a000000000000000000000000000", 266338304, 37312528384, hexnat% "410200000a200000000", 73014444032]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record016_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00081.record016
