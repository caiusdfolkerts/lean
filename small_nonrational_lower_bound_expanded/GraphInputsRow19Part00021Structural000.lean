module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow19Part00021Data
public import GraphInputsRow19Part00021Frames
public import GraphInputsRow19Part00021Leaves
public import GraphInputsRow19Part00021Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00021.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record016
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨16, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2702631244647170048, (certNat% 2), 87960934416384, 597688320, 134217728]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2702472915140542464, 246290604621824, (certNat% 2), 568328192]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2702226624504463360, 422212465065984, 595591168, 70369016807424, (certNat% 3)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 2305843009214742528, 211106232532992, 396316767208603648]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 26388413284352, 396316767208603648, (certNat% 6), 70369012613120]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), 324259173170675712, 13469017440256]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [396845135187476480, (certNat% 9), 570425344, 13469017440256, (certNat% 10)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 14018773254144, 396633426557403136, 2305913377962131456, 17592320262144, 596639744]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00021.record016_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00021.record016
