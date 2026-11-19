module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow25Part00012Data
public import GraphInputsRow25Part00012Frames
public import GraphInputsRow25Part00012Leaves
public import GraphInputsRow25Part00012Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00012.record036
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record036
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
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100000080000041000000000000", 8178536923304820736, 9223372037962072064, hexnat% "3800300000000000000000000", hexnat% "4000000000000004400000000", 966787072, 246964813824, hexnat% "800000400000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record036_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record036_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record036_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record036_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record036_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record036_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record036_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record036_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00012.record036_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00012.record036
