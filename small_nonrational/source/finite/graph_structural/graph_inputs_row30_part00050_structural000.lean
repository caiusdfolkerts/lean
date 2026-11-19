module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow30Part00050Data
public import GraphInputsRow30Part00050Frames
public import GraphInputsRow30Part00050Leaves
public import GraphInputsRow30Part00050Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00050.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003
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
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00050.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00050.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007
def vertexColumn : Fields := ⟨10, hexnat% "dc2f07c368ba1e8d9354d332c9b16cc72725c8f29a96a3aa6659a56558d69394e33a2e4b86e8791e27b61b85e1d46d174731ac5b19c5713c729aa5a9c669966745c966559715955553570d8b52d8751d2766358ce394d5334e334ccb31ce2b4ae1b46c9b91d4731e2749c6785d1725c5783d0f23c2f07e54550e2348aa15a294a4a9855158350d28c9322c2b05c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db69b6db69b4da49b6db6db6db6db6da49b6db69269249b69b4da69369b6db492492449249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨95, by decide⟩, ⟨98, by decide⟩, ⟨106, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40480000010074c41000f080000", hexnat% "1c0000000000000000000000", 8813272891392, hexnat% "c0030006000100000", 14680064]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000001c047c006008f80000", hexnat% "4800000000000410000000000", 8813306445824, hexnat% "80000000300000005000000", hexnat% "400040000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40498000000070849000d800000", hexnat% "40000000000000002200000", 1125917087236096, hexnat% "1c0030006000100000", 18014398513676288]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800001c067c006004f80000", hexnat% "4800000000000410000000000", 8813306445824, hexnat% "100000000100000009000000", hexnat% "400040000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40498000000070449000dc00000", hexnat% "40000000000000002200000", 2251816994078720, hexnat% "100070000000100000", hexnat% "c0000006000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4800000000700410000c00000", hexnat% "4001c0000000000000001000000", 8813306445824, 3377699922378752, hexnat% "1c0030006000100000", 18014398511579136]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00050.record007
