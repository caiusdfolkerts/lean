module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00015Data
public import GraphInputsRow29Part00015Frames
public import GraphInputsRow29Part00015Leaves
public import GraphInputsRow29Part00015Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001
def vertexColumn : Fields := ⟨10, hexnat% "e63349d2ac9b25ce8b92cc972e2aaa3ab1aa699ac9aa6c5a364d876a3a2e2b86e87ba1e47315c789aa4e9c669966725a97158d5351d68d8b4ad1b61d58ce364d534cc7362ccb2ac6b46c9b49ca745c3723c2fe821c171a2168661584e079a1164651544d0758348ca318d1314c8b12c1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da4db6db6db6da6da49b6db6db6db4db492492492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8001040008375bc0000000", hexnat% "10000080000400000000000", 9500467658752, hexnat% "100000800010000000", 536870912]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000040000010000000000", hexnat% "10000080000400000000000", hexnat% "1000008020040000000", hexnat% "100000803010000000", 13247826624512, 825170591744, 52789443035136]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002
def vertexColumn : Fields := ⟨10, hexnat% "398cd174c73a2e4b329caaa9a8eaa6a5ac99a6c5a364d8768b8ae1ba1ee8791cc571e26a93a719a659969565555351d58d2b46d47783c8ea368ce3c4e9364e334cc73a2ccb8acab1ae1b26d8749ca745c3723c2fe805ca8a8a8685a198561381e6845949465454551341d28c6314c8b12c1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db69b69b49b6da6d24db6db6d24936936926db6926924d2492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [1, 2, 3, 4]
def candidates : List (Fin raw.n) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffbeefff7dffbffffffffff", hexnat% "10000000040000000000", 585467951558164480, hexnat% "401000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 1
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c2 c3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c2 c4
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c2 c5
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffbfe7ffffefbffffffffff", hexnat% "800000000000000000", 285873023221760, hexnat% "401000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c2 c3
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffff7dfffffffffffff", 585467951558164480]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffe7dfffffffffffff", 585467951558164480, 1152921504606846976]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c2 c15
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c2 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffefff7dfffffffffffff", hexnat% "1000000000000000000", 585467951558164480]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffe7dcffffffffffff", 844424930131968, 585467951558164480, 1152921504606846976]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffbfeffe1defbffffffffff", hexnat% "401000000000000000000", 285873023221760, 1017813515785732096, 1152921504606846976]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c24 c9
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c25 c0
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7bffed7fe198fbfd7fffffff", hexnat% "12000000000000000000", hexnat% "40000800006000000000000", 285873023221760, 1017813517933215744, 1170935911706263552]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7bf3fe7fd7d9fdefffffffff", 585467951558164480, hexnat% "802002000000000000", hexnat% "c01000000001000000000", hexnat% "40000000004000000000000", 2199023255552]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fb3ec7ffffbf887ffffffff", hexnat% "10000000040000000000", hexnat% "800004021000000000", hexnat% "c01000000000800000000", hexnat% "4002000000006000000000", 1099511627776]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7bf3fe7fffd9fdef7fffffff", 9007201402224640, hexnat% "c01000000001000000000", hexnat% "800004020000000000", hexnat% "40000000002000000000000"]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7bf3eefff1dbfdef3fffffff", hexnat% "c01000000001000000000", hexnat% "10000600000040000000", 1128098930098176, hexnat% "40000000000000080000000", 585467951558164480]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "7fffffffffffffffffffffff"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c2 c34
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c35 c35
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7bfbfefff7bfffff7fffffff", 594475150812905472, hexnat% "401000000000000000000", hexnat% "40000000000000080000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7bffffffe79cfffe7fffffff", 844429225099264, 585467953705648128, 1170935903116328960, hexnat% "40000000000000000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7bfffdffc19cfbfe3fffffff", hexnat% "2000040000000000000", hexnat% "40000000002000080000000", 285878391930880, 3746994889972252672, 729583139634020352]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff3eeffc1dffbef3fffffff", 3746994889972252672, hexnat% "c01000000001000000000", hexnat% "10000200040040000000", 585467953705648128]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7bb3ec7ffff8fae7ffffffff", hexnat% "12000000000000000000", 286972534849536, hexnat% "40000800006000000000000", hexnat% "c01000000001800000000", hexnat% "4000000000000000000000"]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7bb3ecfff19fffe77fffffff", hexnat% "12000000000000000000", hexnat% "44000000000000000000000", hexnat% "c01000000001800000000", 1017813517933215744, 18014398509481984]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7bb3ec7fd199fbfe3fffffff", hexnat% "4002000040000000000000", 2306405963462082560, hexnat% "c01000000000000000000", 1017813519006957568, hexnat% "40000800004000000000000", hexnat% "10000000040000000000"]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c47 c44
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c48 c43
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c49 c42
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c50 c33
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c51 c30
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c52 c29
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c53 c28
  c54
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008
def vertexColumn : Fields := ⟨10, hexnat% "ea278e5174e307ce8b92cca72aaa6a96a3a1eb86c5a96659361da8e3386e8785e0fba1e47315c789ca6a96a6391e565655554d475634cd4b46d1743de0f23a8da3c4e9364e334ce8b32e2b2ae1b16c3b61cc749c6745c970dc2f07f308c872a2a2a1a8562384e4c4711a585454552344d18c530cc8b12c2b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db4926936db49269b6936db4d24926936db6da4924d249a492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff4bfbf9f7ffff26ff8000000", hexnat% "20040000000048000000000", hexnat% "80000400000080000000000", hexnat% "208000001000000000", hexnat% "14000000000010000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffdff9fffccfffbf738000000", hexnat% "20040000000040000000000", hexnat% "20000100000000000000", 3458764517041766400, 144115222435594240]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffffdf9fccfff7f738000000", hexnat% "600000080000000000", 216172816473522176, 3458764517041766400, hexnat% "20000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffcff9f9f7ffff87ff8000000", hexnat% "208000000000000000", hexnat% "400000050000000000", hexnat% "30000000000008000000000", hexnat% "60000000020000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff4ffbf9f7ffff27ff8000000", hexnat% "208000080000000000", hexnat% "80000400000000000000000", hexnat% "20040000000048000000000", hexnat% "10000000000010000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff4ff9f9fcdfff077b8000000", 2449958232723030016, hexnat% "30000000000018000000000", hexnat% "80000400000080000000000", hexnat% "201000000000000000", hexnat% "60000000060000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c9 c0
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff3ffffdf43bff7fff8000000", 4035225266123964416, hexnat% "c0000000000080000000000", 9529616811515969536, hexnat% "200000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c13 c14
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c13 c15
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c13 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffbffdbdffffffffff8000000", hexnat% "200000000000000000", hexnat% "40000000000000000000000", hexnat% "24000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff3ff9bfffffff7fff8000000", hexnat% "24000000000000000000", hexnat% "40000000000000000000", hexnat% "c0000000000080000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff3ff9bffddfffff7b0000000", hexnat% "60000000000000000000", hexnat% "4000000000008000000", hexnat% "c0000000000000000000000", 2449958232723030016]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c22 c19
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff3fffbdf40dff7d610000000", hexnat% "c0000000000080000000000", 216172816473522176, 3458764517041766400, hexnat% "200c00000020000000", hexnat% "4008020002108000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c25 c11
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff89ffb9f7fffeffff8000000", hexnat% "600000100000000000", hexnat% "34000000000000000000000", hexnat% "2004008000000000000000", hexnat% "40000000000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff99fbb9f7fffeffff8000000", hexnat% "20040000000000000000000", hexnat% "600000100000000000", hexnat% "6004008000000000000000", hexnat% "40000000000000000000000"]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff8ffbf9ffdffeb7ff8000000", 144115188075855872, hexnat% "600000100000000000", hexnat% "50000000000000000000000", hexnat% "20040000000048000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff8ff8fbfffffeb7ff8000000", hexnat% "400000140000000000", hexnat% "30000000000000000000", hexnat% "50000000000000000000000", hexnat% "20040000000008000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff89f8f9fffbfeb4ef8000000", hexnat% "600000100000000000", hexnat% "10000040002100000000", hexnat% "60000000040000000000", hexnat% "30000000000008000000000", hexnat% "46000000000001000000000"]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c31 c30
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c32 c29
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c33 c28
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c34 c27
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff1ffbfbffcffeb73f8000000", hexnat% "c0000000000100000000000", hexnat% "20040000000048000000000", 216172833653391360, hexnat% "400000000000000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff3bfff9fccdfe7e3b0000000", 2449958232723030016, 81064810606755840, hexnat% "201000000000000000", hexnat% "80000400000180000000000", hexnat% "44000000000001000000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff4ffbfbffefff97ff8000000", hexnat% "80000400000000000000000", hexnat% "30000000000008000000000", 72059793061183488, hexnat% "40000000040000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff0ffbf9fe2bfe17fe8000000", hexnat% "20040000000048000000000", hexnat% "50000000000000000000000", 90074191839100928, hexnat% "201c00000000000000", hexnat% "80000400000180000000000"]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff09f9f9f629fe14ac0000000", hexnat% "20040000000048000000000", hexnat% "80000400000180000000000", hexnat% "20000100020418000000", hexnat% "56000000000001000000000", hexnat% "201c00000020000000", 9250393776352919552]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c42 c41
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c43 c38
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c44 c35
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c45 c26
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c46 c10
  c47
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record008
