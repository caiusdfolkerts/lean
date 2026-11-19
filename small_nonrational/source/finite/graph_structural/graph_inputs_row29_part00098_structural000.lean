module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00098Data
public import GraphInputsRow29Part00098Frames
public import GraphInputsRow29Part00098Leaves
public import GraphInputsRow29Part00098Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00098.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record004
def vertexColumn : Fields := ⟨10, hexnat% "ccab29c8f2caaaa9a8eac6a9a968dac9aa6998e6c5a96958d6c3a8e938cecc5b15c4f1ca5a95a4e9c6599564d9c95a5594e5c5595554d5c358d534cdc8ce3c4cd38cd33c2ccb8ad2b2ac6b86d1b26c5bc1cc789d2729c6785d1725c5783d0fcc30c8c8b21ca0e2384e4c4b11c50d2344d28c6324c530cc8b12c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "4926db6db6db6db4924926db6db6db6db49269a49a6d26d269b49b492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1428492365332480, 67553994460889088, hexnat% "f000000c00000000000", hexnat% "f0000000000000000000", hexnat% "f000000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [67556193484144640, hexnat% "f000000c00000000000", hexnat% "f0000000000000000000", hexnat% "f000000000000000000000000", 1425123970121728, 1169371955200]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00098.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00098.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record010
def vertexColumn : Fields := ⟨10, hexnat% "2b89e0f86d1743d0ec370bc1f332ac9b29c9723cb2aaaa6a3a9a6598e6c5996558d64d8b61db0e3392e2b86ecc6b16c6715c4f1ca6a99a4e9a6659366392e479c5595554d5c34cd8749d17723a8da398d6338f13a4d9394d5334e334ccb31cf0ba2e4b32e2b4acab1af0761d4731e1745c9715e0f43f30c8a2a2a86a2384ec4515254552344dc0e0b22c4b41c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6da6db6924db6db6db4d24db6db6db6db49269a49b6da6db6db69249a4924d2491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨48, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100800b000075810009bbe00000", 9223372037928517632, hexnat% "80000040000400000000", 481036337152, hexnat% "7000000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800b00001400007d89e00000", 7025615418697973760, hexnat% "7000000000000000000000000", 1912602624, hexnat% "100000080000041000000000000", 9223372036854775808]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c2 c0
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3800b800015c0003d89e00000", hexnat% "4000000000000004000000000", hexnat% "100000000000001000002000000", 1879048192, 16140901064495857664]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8008000015800009fbe00000", 16140901064495857664, hexnat% "3000300000000000000000000", 498216206336, hexnat% "100000080000041000000000000", hexnat% "4000000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c6 c4
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800007580000000000000", hexnat% "100000080000041000000000000", hexnat% "3800300000000000000000000", 9223372037932711936, hexnat% "4000000000000004000200000", 998244352, 264140488704]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c9 c3
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00098.record010
