module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow30Part00005Data
public import GraphInputsRow30Part00005Frames
public import GraphInputsRow30Part00005Leaves
public import GraphInputsRow30Part00005Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00005.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 25232932864, 17293822569102704640]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), 31943819264, 8646911284551352320, (certNat% 7)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), 17293822569102704640]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 17870283321406128128, (certNat% 11), (certNat% 12), (certNat% 13)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), 25232932864, 17293822569102704640]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), 9223372061550837760, 6629298651757805568, (certNat% 19)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 18), (certNat% 22), (certNat% 23)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), (certNat% 26), 2305843032299143168, 14987979559889010688]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), (certNat% 29), (certNat% 22), (certNat% 30)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), (certNat% 22), 45035996525363200, 6052837899454382080, (certNat% 33)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00005.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00005.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012
def vertexColumn : Fields := ⟨10, (certNat% 34)⟩
def kindColumn : Fields := ⟨3, (certNat% 35)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨87, by decide⟩, ⟨98, by decide⟩, ⟨101, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), (certNat% 37), 1702181438750720, (certNat% 38), (certNat% 39)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 19008585728, 12177733399154262016, (certNat% 41), 1702181438750720, (certNat% 42)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00005.record012
