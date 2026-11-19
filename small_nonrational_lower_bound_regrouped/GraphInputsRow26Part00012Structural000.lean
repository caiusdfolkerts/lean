module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00012Data
public import GraphInputsRow26Part00012Frames
public import GraphInputsRow26Part00012Leaves
public import GraphInputsRow26Part00012Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00012.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record024
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨67, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 2420113408, (certNat% 4), 17592186044416]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), 4370464768, 3407872, 18141941858304]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), 11534336, 5435817984, 72075186223972352]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 7602176, 5444206592, (certNat% 4), (certNat% 10), 704643072]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨17, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record024_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00012.record024
