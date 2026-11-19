module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00083Data
public import GraphInputsRow26Part00083Frames
public import GraphInputsRow26Part00083Leaves
public import GraphInputsRow26Part00083Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019
def vertexColumn : Fields := ⟨10, hexnat% "cd2745d0ec8f13c1f3329c9723aa3a4e87ac9aa669a66598e6c5a5655a364d87633a2e4b8ae1ba1e4789e1783e3a725a95a59956539715955553362d4b4ad1b61d4749dc8ea368e6358ce3c4e5354ccb8ad2b2ac6b86d1b26f07a1d8791d4731e2749ca719e1745c9715e0f43c8f13c2f07cac1b05c2a86a16859855151548d1341d84d1314c8b12c1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b69b4db4da6db6db6db6da4db4db6db6924da4926db6d249b4924db6db6da4d3693449249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨96, by decide⟩, ⟨99, by decide⟩, ⟨103, by decide⟩, ⟨106, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81000088000000000000200000", 1729395451049803776, hexnat% "408000000008000400000000000", 989010709708800, hexnat% "70700000000000000", hexnat% "10000000000001a400000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record019
