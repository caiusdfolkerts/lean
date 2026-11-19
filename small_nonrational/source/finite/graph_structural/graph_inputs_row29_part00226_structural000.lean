module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00226Data
public import GraphInputsRow29Part00226Frames
public import GraphInputsRow29Part00226Leaves
public import GraphInputsRow29Part00226Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000
def vertexColumn : Fields := ⟨10, hexnat% "31ca719c9715c3723c4f0bc1f31aa699a9695a36a3a4e8ba1eb16a59969595635a364d8b61db0ea398e9394e33a2e4b8ae1ba1e4789e1783ec669966659564d98e5392e479c569565655554d58d5352d475c368d6364d534cd8b52d2b46d8751d2745d0f70ba2e4b52ccb8ad2b2af07a1e4751cc789d2729e0f43c8f13c2f66078650746286a61866624696146560c6382d0b22c4b0ae0741c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "369b6db4da6db6d369b6db4da6db6d36db6d36db69b4db6da6d36db69b6da492492492492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨50, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨77, by decide⟩, ⟨85, by decide⟩, ⟨92, by decide⟩, ⟨95, by decide⟩, ⟨102, by decide⟩, ⟨105, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨122, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20481000000000000000", hexnat% "10240800000000000000000000000", 137422176256, 35046933135360, hexnat% "4080000102000000204000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001
def vertexColumn : Fields := ⟨10, hexnat% "316a59969595635a364d8b61db0ea398e9394e33a2e4b8ae1bb19a659996559366394e4b91e715a5655554d58d5352d70da358d9354d3362d4b4ad1b713a4d9394d5334e334ccb31cf0ba2e4b52ccb8ad2b2af07a1e4751cc789d2729e1745c9715c3783d0f23c4f0bd941d18a1a986199911c5891a58519615454951543560c6382d0b22c4b0ae0741c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "369b6db4da6db6d369b6db4924924da6db6d369b6db492492492492492492491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩, ⟨110, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40800000000000000000000", hexnat% "102000010200000003e0000000", hexnat% "4080000000004080007c00000000", 35888059530608640, hexnat% "7f8000000000000000000", 140187732541440]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002
def vertexColumn : Fields := ⟨10, hexnat% "c6a9a66a5a568da8e93a2e87ac5a9665a56558d68d9362d876c3a8e63a4e538ce8b92e2b86ec669966659564d98e5392e479c569565655554d58d5352d475c368d6364d534cd8b52d2b46dc4e9394d5334e334ccb3c2e8b92d4b32e2b4acab86d1b26c5b0ef07a1e4751cc789d2729e1745c9715c3783d0f23c4f0bd921c98a1a986199911c5891a5851958318e1344c9314c3382d0b22c4b0ae0741c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "6d36db69b4db6da6d36db69b4db6da6d36db69b4db6da492492492492492492492492492491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩, ⟨95, by decide⟩, ⟨98, by decide⟩, ⟨105, by decide⟩, ⟨108, by decide⟩, ⟨115, by decide⟩, ⟨118, by decide⟩, ⟨125, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040000081000000003e0000000", hexnat% "81000002040000000007c00000000", hexnat% "2040000081000000000f800000000000", 140187732541440, 1148417904979476480, hexnat% "ff000000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004
def vertexColumn : Fields := ⟨10, hexnat% "dc2f07c368d62e4b526c3b25c571e2749b25c8f25a8ea568e6558d6538ce8b8ae1ba1e4785ed86e178751b45d1cc6b16c6715c4f1d27299a5693a71996559b16a5994e5a5655554d59354d3362d2b46d8751d175a364e334ccb38acab86d1b89ca785d1783d0f23c2f07e685a2543524c4a8968a529854958352328d1324d0b0ac8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b69b49a6db6d36da6db6db6db6db6db6926db6db49a4da6d369349269a492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨84, by decide⟩, ⟨89, by decide⟩, ⟨96, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "45020000007005924353e00000", hexnat% "8001000000008000000000000", 137640280064, 51539607552]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d00100000300d92205fe00000", hexnat% "40020000004000000000000000", 287762808832, 51539607552]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d00100000300d920002600000", hexnat% "40020000004000000000000000", 8724152320, 21751660544, 35517366272, 412316860416]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4902100000700d826a45600000", hexnat% "4000000000000100010000000", 176160768, 21474836480]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000000001000826d55e00000", hexnat% "21000000000000000000000", 8757706752, hexnat% "44000000002000000000000000", hexnat% "800000000000d000000000000", 4611703610613432320]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000000000000906d55e00000", hexnat% "1000000000004020000000000", 8757706752, hexnat% "21000000000000000000000", hexnat% "40000000007000000000000000", hexnat% "8000000000009000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400000000400d926f5fe00000", hexnat% "9000000000000000000000000", hexnat% "40000000003000000000000000", hexnat% "21000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3802297500958720, hexnat% "8001000000000000000000000", hexnat% "5000000000000000000000000", 292057776128, 6917546619827126272, hexnat% "40020000001000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000000004000906f5fe00000", hexnat% "1000000000004020000000000", hexnat% "40020000001000000000000000", 2306124484190404608, hexnat% "8001000000008000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000000007008926f5fe00000", hexnat% "44000000000000000000000000", hexnat% "8000000000005000000000000", hexnat% "21000000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8070609168473522176, hexnat% "40020000000000000000000000", hexnat% "5000000000000000000000000", 171798691840, 3379898743783424, hexnat% "8001000000001000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2393015618371584, 19791242854400, hexnat% "21000000000000000000000", hexnat% "5000000000000000000000000", hexnat% "8000000000005000000000000", hexnat% "40000000007000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4802100000700d80025c400000", hexnat% "5000000000000000000000000", 463856467968, 19791242854400, 27262976, 4294967296]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4612108709208784896, 19791242854400, hexnat% "21000000000000000000000", hexnat% "40000000003000000000000000", hexnat% "5000000000000000000000000", hexnat% "800000000000c000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [422690754134016, hexnat% "21000000000000000000000", 60817408, hexnat% "4000000002000100000000000", hexnat% "800000000000c000000000000", hexnat% "40000000005000000000000000", hexnat% "1000000000000020000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c21 c16
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c22 c15
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c23 c12
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c24 c11
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c25 c8
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c26 c7
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c27 c4
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009
def vertexColumn : Fields := ⟨10, hexnat% "368d6338b92d4ad26c9723c789d25a8ea9695a3696639a56558d69386e8785ed86e178731ac5b1d27299a5693a7198e5392e6c5a9665594e5a56354d4b59362d1b61d0f5c368d6338d9392d4b32d2b2ac6b86c9b91d4731d2729c6785d1783c4f0bc1f9a168990e45291a318968a52986519894a58549544c9342c1b21c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "26d369b6d369b4da6db6db6da49a49b49a49a69a6db69a69b49b4d349b689249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2490019c9d50148a0000000", hexnat% "2400000000400000000000000", hexnat% "10000000040000000000000000", 4415431901184]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "410019c055000820000000", hexnat% "10400000000000000000000000", 4415431901184, hexnat% "2000000000880000000000000", hexnat% "20800000000004000000000", hexnat% "40500010080000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24041000c8d44010080000000", hexnat% "10000000110000000000000000", 4616189618054758400, hexnat% "20800000000004020000000", 4449791639552, 36310271995674624]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2490015cdd00148a0000000", hexnat% "2400000000000000000000000", hexnat% "10000000080000000000000000", 4415431901184, 1407374883553280]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "124000001dccd5014820400000", hexnat% "24000000000000000000000", hexnat% "800000100000080000000", 4415427706880, hexnat% "100000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "242490015c5500148a0000000", hexnat% "10000000080000000000000000", 577586652210266112, 4415431901184, 36310271995674624]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40490015c450014820000000", hexnat% "10020000000000000000000000", hexnat% "80100000080000000", hexnat% "2000000000880000000000000", 4415431901184, 1407374883553280]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "104041001cc504010080000000", hexnat% "2000000000880000000000000", hexnat% "20800000000004020000000", 4449791639552, 22517998136852480, hexnat% "10001000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "242090009cdd50048a8400000", hexnat% "4000000000010000000000", 4415293489152, hexnat% "10000000140000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40080009c4c5040c0c400000", hexnat% "2000000000900000000000000", hexnat% "10000000140000000000000000", hexnat% "4100000000000000000000", 4503602311725056, hexnat% "20000000000014000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2490008cd910140a0000000", hexnat% "2400000000000000000000000", 19140298416324608, hexnat% "10000000140000000000000000", 4449791639552, hexnat% "10000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "249001dc4010140a0000000", hexnat% "10400000000000000000000000", 595601050719748096, hexnat% "2000000000100000000000000", 4449791639552, 40532396646334464]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20008000dcdd1054cac400000", hexnat% "4100000000000000000000", hexnat% "100004000000000000", hexnat% "10020000000000000000000000", hexnat% "400000000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20008000ccdd1054cac400000", hexnat% "4100000000000000000000", hexnat% "400000000004000000000000", hexnat% "10020000000000000000000000", hexnat% "110000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20049000ccd910148a0000000", 19140298416324608, hexnat% "10020000000000000000000000", hexnat% "110000000000000000", hexnat% "400000000000000000400000", 4415427706880]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100249000cc5010140a0000000", hexnat% "110000000000000000", hexnat% "2400000000000000000000000", 4449791639552, 595601050719748096, 40532396646334464]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1002000019c501044c2c400000", hexnat% "40000010080000000", hexnat% "4100000000000000000000", hexnat% "400000000004000000000000", hexnat% "2000800000000000000000000", 635007547459239936]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2400009c501014020000000", hexnat% "10000000140000000000000000", hexnat% "900000000000080000000", hexnat% "2400000000000000000000000", 4449791639552, 595601050719748096, 40532396646334464]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c26 c21
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c27 c16
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c28 c15
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c29 c14
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c30 c11
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c31 c10
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c32 c3
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c33 c2
  c34
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00226.record009
