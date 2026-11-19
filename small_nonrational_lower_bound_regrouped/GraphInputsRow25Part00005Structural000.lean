module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow25Part00005Data
public import GraphInputsRow25Part00005Frames
public import GraphInputsRow25Part00005Leaves
public import GraphInputsRow25Part00005Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00005.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record018
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨71, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨87, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 144256063003164672, (certNat% 4), 105656195481600, (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), 140913582014464, (certNat% 10), (certNat% 11), (certNat% 12)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), 2305843044177412096, (certNat% 15), (certNat% 16), 72128031501582336, (certNat% 17)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 8), (certNat% 20), (certNat% 21), 144256063003164672, (certNat% 22)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), 2305878193652891648, (certNat% 14), (certNat% 15), 72128031501582336, (certNat% 16), (certNat% 17)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 21), 72128031501582336, 144256063003164672, (certNat% 8), (certNat% 25), (certNat% 26), 2305878227945521152]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00005.record018
