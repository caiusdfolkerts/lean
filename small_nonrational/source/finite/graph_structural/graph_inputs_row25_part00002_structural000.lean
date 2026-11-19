module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow25Part00002Data
public import GraphInputsRow25Part00002Frames
public import GraphInputsRow25Part00002Leaves
public import GraphInputsRow25Part00002Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00002.record040
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record040
def vertexColumn : Fields := ⟨10, hexnat% "ea278e5174e307ce8b92cca72aaa6a96a3a1eb86c5a96659361da8e3386e8785e0fba1e47315c789ca6a96a6391e565655554d475634cd4b46d1743de0f23a8da3c4e9364e334ce8b32e2b2ae1b16c3b61cc749c6745c970dc2f07f308c872a2a2a1a8562384e4c4711a585454552344d18c530cc8b12c2b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db4926936db49269b6936db4d24926936db6da4924d249a492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "420b4003f60122df8000000", hexnat% "20040000000048000000000", hexnat% "80000400000080000000000", hexnat% "208000001000000000", hexnat% "14000000000010000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d6094608c601bb538000000", hexnat% "20040000000040000000000", hexnat% "20000100000000000000", 3458764517041766400, 144115222435594240]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f60d4008c6017b538000000", hexnat% "600000080000000000", 216172816473522176, 3458764517041766400, hexnat% "20000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "76094000c4011b530000000", 2449958232723030016, hexnat% "208000080000000000", hexnat% "80000400000000000000000", 81064793426886656, hexnat% "60000000060000000000", 1152921506754330624]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "360f0400000179010000000", hexnat% "c0000000000080000000000", 2449958232723030016, hexnat% "201c00000020000000", 99079191802150912, hexnat% "4008000002108000000", 19327352832]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80080003f20090ce8000000", hexnat% "600000100000000000", hexnat% "20040000000048000000000", hexnat% "56000000000001000000000", 9241386577098178560, hexnat% "34000000000000000000", 2199291691008]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800022000108c0000000", hexnat% "20040000000048000000000", hexnat% "80000400000180000000000", hexnat% "201c00000020000000", hexnat% "56000000000001000000000", hexnat% "20000100020418000000", 9250393776352919552, hexnat% "14000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c11 c6
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record040_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record040_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record040_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record040_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record040_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record040_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record040_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record040_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record040_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00002.record040

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00002.record042
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record042
def vertexColumn : Fields := ⟨10, hexnat% "ea278ab23c1f392cca725cb8acaa6a96a3a1ea9665a364d876a38ce8b86e8785e0fba1e47315c789ca6a96a6391e5a565535334ad1743de0f2358f13a4d9354e334cc73c2e8b62ccb8ad2b1ae1b16c3b61cc749c6745c970dc2f07f301d06ce0b12a28562384e4c4711a465154352344d0b58344c5322c4b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db49369b6db6da49a69b6936db4da4924da69349a49b4d349a492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a00154001f84dc8df8000000", hexnat% "40080000000000000000000", hexnat% "400010000000000000", hexnat% "400000000000000000000000", 563087392374784, hexnat% "208000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a00154000f00c08938000000", hexnat% "40080000000180000000000", hexnat% "209000000000000000", hexnat% "400090000000000000", hexnat% "400000000004000040000000", 4552665333760, 562952100904960]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a00114209396dcadf8000000", 864691128455135232, hexnat% "400000000000000000", hexnat% "c0000000000000000000", hexnat% "440000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800114209f845cadd8000000", hexnat% "40080000000000000000000", 703687978647552, hexnat% "200000400010000000000000", hexnat% "40000000000000000000", hexnat% "400000000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800014209f0040a918000000", hexnat% "200100000000800020000000", hexnat% "400090100000000000", hexnat% "40080000000080000000000", 1688853081489408, hexnat% "40000000040400000000", hexnat% "400000000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200110209f02c085f8000000", hexnat% "800004000000002000000000", hexnat% "400090100000000000", hexnat% "400000000004000000000000", 13228499271680, hexnat% "c0000000000000000000", hexnat% "40000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800014008f0244a5b8000000", hexnat% "601000800000000000", hexnat% "200100000000000000000000", hexnat% "c0000000100000000000", 1134731433345024, hexnat% "440000000080000000000000", 4503599627370496]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200110009f84dcadf8000000", 5066549580791808, hexnat% "600000000000000000", hexnat% "c0000000000000000000", hexnat% "440000000000000000000000", hexnat% "800004000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400900090841cace8000000", hexnat% "600000000010000000000000", hexnat% "200002c00000000000", 1080863910837354496, hexnat% "400000000000000000", hexnat% "44000000000000000000", hexnat% "800100000000000100000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10008f00002838000000", hexnat% "40080000000180000000000", hexnat% "601000800000000000", hexnat% "400000000094000000000000", hexnat% "800104000000000100000000", 562953174646784, hexnat% "40000000040400000000", hexnat% "200000000000408000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c16 c7
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c17 c2
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record042_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record042_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record042_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record042_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record042_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record042_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record042_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record042_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record042_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00002.record042

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00002.record098
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record098
def vertexColumn : Fields := ⟨10, hexnat% "f41d85e364d52d45d32c5b15c3713c1f2e25c96a3a95a3693a1eac6998d61d8ce1b89e1783ef0761b8791d46d174571e2729aa5994e745b172599565c569595555355351d70da362d4b51d2743db0ea398d6338d5334d331cd2b2ad1b0ee8791cc789c6725c570dc8fd82643489a198560b81ec8529464998942d0749322c2b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b69b6db6db6db4db49349269b6db69a4da4db6db6da4926db6d36924db492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨87, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [32216449024, hexnat% "18000700000000000", hexnat% "4041000000000000000", hexnat% "40000800000800000000000000", hexnat% "8440000000002002000000", hexnat% "8000000000000c800000", 422212465065984, hexnat% "230000000000001000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record098_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record098_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record098_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record098_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record098_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record098_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record098_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record098_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record098_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00002.record098
