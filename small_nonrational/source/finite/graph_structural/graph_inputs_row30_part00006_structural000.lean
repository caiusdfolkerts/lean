module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow30Part00006Data
public import GraphInputsRow30Part00006Frames
public import GraphInputsRow30Part00006Leaves
public import GraphInputsRow30Part00006Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00006.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record009
def vertexColumn : Fields := ⟨10, hexnat% "f83d07c368d6178d92e4d52d45d0f4d332c9b16cc725c5713c1f1723c96a5693a2e87ab18e6358b61da4e1b85e0fbc1e8761b85e1e4751b45d16c5713c729aa719a65392e745b1725a9665594e5c569595555355352d475c362d4b61d4743db0d6338d5334d332cc73a2d2b2ad1b26c3ba1e4731ca719c9715c3783ce2348661582e07b094a5198342d074a324c2b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db6db6db4db6da4d34936db6db6da69a6db6db6db6db49249b4d34da4926da492449249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81aa00150000fca9d1d80000", 538968064, hexnat% "400000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81a200150000fca951180000", 2155872256, hexnat% "c00000000000000000000", 543162368]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81aa0015000064a9d1900000", 167125767946240, 543162368, hexnat% "400000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81ae0015000004a910100000", 10485760, 2164260864, 1614807040, 272678884212736]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c6 c2
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000000000000a000a00000", hexnat% "2e00000000000000100000", hexnat% "18000000000000001400000", 277076930723840, hexnat% "150000000140000000", 37312528384]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c8 c7
  c9
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00006.record009
