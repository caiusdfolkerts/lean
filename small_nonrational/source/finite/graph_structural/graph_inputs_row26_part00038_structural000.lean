module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00038Data
public import GraphInputsRow26Part00038Frames
public import GraphInputsRow26Part00038Leaves
public import GraphInputsRow26Part00038Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00038.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021
def vertexColumn : Fields := ⟨10, hexnat% "7c3cb8ab29caaa9aa3a87ae1ac671aa6698e61db0e9394e8b92e1ba1e4785e0f8f1e26c9726a96a4e91e785b15c5a95a539475c364d5362d4b46d8751d1743de0ec370ea368ce334cb31cf0ba2d8b92d4b32e2b4acab1ae1b46f07a1d8791d4731e2749ca719e1745e0f43c4f0bc1f1683a158361643915435a0d8330ca314c3382d0b12c2b06e0741c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6da6db6d36db6da4db6db4db6da6db6db492492492492492492492492492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨72, by decide⟩, ⟨79, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨97, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10201808100d9b3ef3eff000000", 2756220568431755264, 824633720832, 3377699720527872]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10201808100f53b6fb6ff000000", 721702115164028928, 54043195528445952, 38654705664, 158329674399744]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10201808100eb376f76ff000000", 1443404230328057856, 54043195528445952, 38654705664, 158329674399744]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1800000c02000001f000000", hexnat% "102000081000100080080000000", 2310348532986413056, 2215771016666284032, 272193552384, 4492604511092736]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00038.record021
