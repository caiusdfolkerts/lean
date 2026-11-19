module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow31Part00089Data
public import GraphInputsRow31Part00089Frames
public import GraphInputsRow31Part00089Leaves
public import GraphInputsRow31Part00089Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00089.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record003
def vertexColumn : Fields := ⟨10, hexnat% "f0ba2d8b92d4b32b29caaa9aa9a96aa699a9695a8e93ab19c6a99a699966a5996959568d9362b86e2785ef07a1d8791d4731b25c9aa5a99a569a6599965598e539b15c5a95a599565a5595955558d5352b46d2745de0f43b0dc3c8ea368e6358f13a4d9394d538cd33a2d8b92d4b32e2b4acab1ae1b46c9b16c3ba1d8791d4731e2749ca719e1745c9715c3723c4f0bc1f3303cb09c28c9323283a318362384e0b81eb05c18c53132439314352344d0b41d"⟩
def kindColumn : Fields := ⟨3, hexnat% "136da49b6db6d249b6db6d24924db6926db6db4926db6db49249b49b6db6db49b6d36db6da6db4db6db692489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨39, by decide⟩, ⟨44, by decide⟩, ⟨53, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩, ⟨125, by decide⟩, ⟨134, by decide⟩, ⟨135, by decide⟩, ⟨136, by decide⟩, ⟨141, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3c00000000003c000000", hexnat% "f000000000000000000000000000", hexnat% "400c00c0000c00100040000000", hexnat% "830030000c00020008000000000", hexnat% "10030030000000000000000000000000000", hexnat% "20c00c000000000000000000000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00089.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00089.record003
