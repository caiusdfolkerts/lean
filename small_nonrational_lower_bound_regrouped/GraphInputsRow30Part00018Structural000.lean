module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow30Part00018Data
public import GraphInputsRow30Part00018Frames
public import GraphInputsRow30Part00018Leaves
public import GraphInputsRow30Part00018Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00018.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record019
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨50, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨83, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 137608822784, 22552772608, (certNat% 3), (certNat% 4)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), 8690597888, (certNat% 7), (certNat% 8)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 3848290697216, (certNat% 10), (certNat% 3), (certNat% 4)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 167772160, (certNat% 12)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 8690597888, 2611474333696, 1140313817088, 1077936128]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 1694364598272, 2473901162496, (certNat% 15), (certNat% 8)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 412316860416, (certNat% 17), (certNat% 18), (certNat% 19)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 176160768, (certNat% 18), (certNat% 21), (certNat% 19)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 3332894621696, (certNat% 6), (certNat% 7), (certNat% 8)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), 125829120, 2370956165120, 16106127360, 1374389534720]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 12884901888, (certNat% 25), (certNat% 21), 4398046511104]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), 8698986496, 2611474333696, 41875931136, 1099511627776]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), 8698986496, (certNat% 21), 2611474333696, 41875931136, 1099511627776]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c17 c8
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c18 c7
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00018.record019
