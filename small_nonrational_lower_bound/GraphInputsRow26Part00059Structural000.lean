module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00059Data
public import GraphInputsRow26Part00059Frames
public import GraphInputsRow26Part00059Leaves
public import GraphInputsRow26Part00059Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00059.record035
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨51, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨65, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [146402815757516800, (certNat% 2), 43092279296, 10995118374912, (certNat% 3)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [46745668550656, (certNat% 3), 103230210048, 146367005069410304, (certNat% 2)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2263350523723776, (certNat% 3), 113816633344, 144150389627813888, (certNat% 2)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2289754774700032, (certNat% 4), (certNat% 5), 78517370880, 36507222016]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [146404429599866880, (certNat% 2), 78517370880, 9345850933248, (certNat% 3)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 2203318222848, (certNat% 4), 549755813888]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [144115303435468800, (certNat% 2), (certNat% 4), 2251821288521728, 37933151158272]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2289826690236416, 34519121920, 8589934592, (certNat% 4), (certNat% 5)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 34519121920, 11811160064, 72061992084439040, 11544874188800, 146402189441499136]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨19, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨20, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00059.record035
