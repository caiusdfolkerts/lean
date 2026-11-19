module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow30Part00002Data
public import GraphInputsRow30Part00002Frames
public import GraphInputsRow30Part00002Leaves
public import GraphInputsRow30Part00002Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00002.record042
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record042
def vertexColumn : Fields := ⟨10, hexnat% "354cd274b32ac9b19c1f352cca72b2aaa9a99a1eb86d1ac6c9aa699b1665a5655a364d876a398e938ce8b8ae1b91e2785e0f9991e785d16c5c96a599595555351d58d334ad1b51d27783d0ec3c8ea398d9354d331cd8b32cab1ad1b26f07a1d8791d4731e2749ca719d1725c570dd0f23c4f0bc1fe105c0f3821683a1643961515154352344d0b41d60d1314c3322c4b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6d36db6d26db6db6db6db6db69349b6da49249249b6da4924924da6db6da693492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨109, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000006401ec01e9016f000000", 8461841487364096, hexnat% "1e1000000000000000", hexnat% "2020000008000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000006c0e140e11016f000000", hexnat% "2020000000002000200000000000", 501377302265856, hexnat% "100810000000000000", hexnat% "1c000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100000641e141e11016f000000", 536561674354688, hexnat% "1e800000000000000", hexnat% "2020000008000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000006c00ec00e9016f000000", hexnat% "2020000000020002000000000000", hexnat% "11001100000000000", 7881299347898368, hexnat% "1c0000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000000400040001016e000000", 554153860399104, 8444249301319680, hexnat% "1f800000000000000", hexnat% "1e0000000000000000", hexnat% "2020000068000000000001000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c5 c3
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c6 c2
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c7 c1
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record042_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record042_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record042_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record042_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record042_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record042_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record042_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record042_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record042_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00002.record042
