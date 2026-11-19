module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00152Data
public import GraphInputsRow29Part00152Frames
public import GraphInputsRow29Part00152Leaves
public import GraphInputsRow29Part00152Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00152.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record004
def vertexColumn : Fields := ⟨10, hexnat% "338ad174ab16c8f13cccab26c972caaaa9a96ac6a3a4eaa6598e6a59568d9362d876a394e8b92e2b86e8791e0fb31ac5b15c729aa6695a7198e539a956539695556354d4b51d68d5362d4b4ad1b61d4743dc4d9354f0ba2e4b86d1ba1d4731e1745c5783d0f23c1fac1682d06ca494a2584ea45492544da0d4384d1324e0b42c4b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "d369b69b6da6db6d36d369b69b6d36db4db6da6da6d36d36d2492492492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨63, by decide⟩, ⟨69, by decide⟩, ⟨74, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨85, by decide⟩, ⟨92, by decide⟩, ⟨98, by decide⟩, ⟨102, by decide⟩, ⟨105, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000002007dff000000", 3848290697216, hexnat% "40000000008000200000000000", hexnat% "4100204000000000000000000", hexnat% "200002000000100000200000000", hexnat% "200010000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "208010201000000000", hexnat% "4100204000000000000000000", 2645699854336, 7365197824, 1667521052672, hexnat% "40000040000002000000000000", hexnat% "200002000000100000208000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00152.record004
