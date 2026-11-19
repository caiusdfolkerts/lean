module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow30Part00015Data
public import GraphInputsRow30Part00015Frames
public import GraphInputsRow30Part00015Leaves
public import GraphInputsRow30Part00015Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00015.record042
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record042
def vertexColumn : Fields := ⟨10, hexnat% "ec3a8cd2b49d32cab3a2e4b8acaaaa6a96a3a99a568dac9aa699b16a5a56c3a8e8b92e2b86e4789e17ba1e4731ac5b15c4f16a5693a599564d9c96a5c56958d5352d4754b4ad4749d17783c8ea368d6338f13a4d9354cd362d4b32d2b2ac6b46c9b16f07a1e2749ca719e1745c9743c8f0bc1f1b312a4a161584e4a4a91a4651544d0b51324c5342c8b12c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6d36db6db6da49b6da6d36db6d24db6db6da49b4db6da4924924924db6d2492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨105, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1188950302162681856, hexnat% "1200000000000000000000", hexnat% "2001c0000000000000010000000", hexnat% "3800c0001c000800000", 545357968703488, 15633735483392]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record042_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record042_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record042_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record042_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record042_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record042_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record042_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record042_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record042_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00015.record042
