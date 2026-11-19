module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00020Data
public import GraphInputsRow26Part00020Frames
public import GraphInputsRow26Part00020Leaves
public import GraphInputsRow26Part00020Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00020.record049
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record049
def vertexColumn : Fields := ⟨10, hexnat% "3b03e1b43d1ac5b0ec370bc1f272ca8ba1e8b61d92e2b86e2785e0fba1e4731ac5b19c4f1ca5a95a4e9364b91e715654d5534cd2745dc8e6394e332cc73c2e2b4acab1ac9b16c3bc1e1725d0f23c1f6a18c8c8721a85613989614951550d2344d84c5312c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db69b6da6d34da69b6db6da6db6d24926d269b6d34da492249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨52, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41294010003428000000", 17592212258816, 41781443952640, 9895608844288]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40080010000000000000", hexnat% "1000000003400000000", 54975589777408, hexnat% "214000000028000000", 14293658501120, 16777216]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record049_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record049_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record049_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record049_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record049_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record049_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record049_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record049_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00020.record049_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00020.record049
