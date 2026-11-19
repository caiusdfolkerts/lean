module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow30Part00031Data
public import GraphInputsRow30Part00031Frames
public import GraphInputsRow30Part00031Leaves
public import GraphInputsRow30Part00031Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00031.record041
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041
def vertexColumn : Fields := ⟨10, hexnat% "3e0f43b0f2368e6358b61d8e9364e5334ad1b4d332c9b16cc72e278ad274ab26caca72a6a5aa9a66a5a568daa99a699966a59968d9362da4e53a2e4b86e8791eb85e1b45d1ac5b1b25c99a569a659996559366a56966559695656354d4b59354d8b52d1b61d474d32cccb1ac9b16ca719c970dc4f0bee07821c470e2078e1074c328c6324c4b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "9b6db6db6db6db4936db6db6db6db6db6db6d249b6db6db6db6db6db6db692492492491249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨110, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000003000000060000000", hexnat% "4000060000000c00000000000000", 3014656, 407896064, 92274688, 33554432]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00031.record041
