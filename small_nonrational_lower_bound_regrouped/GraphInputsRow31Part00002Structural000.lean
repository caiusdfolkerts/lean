module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow31Part00002Data
public import GraphInputsRow31Part00002Frames
public import GraphInputsRow31Part00002Leaves
public import GraphInputsRow31Part00002Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00002.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨99, by decide⟩, ⟨102, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨119, by decide⟩, ⟨120, by decide⟩, ⟨125, by decide⟩, ⟨126, by decide⟩, ⟨131, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 16106127360, 257698037760, (certNat% 3), (certNat% 4)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 16106127360, 257698037760, (certNat% 4), (certNat% 3)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 257698037760, (certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨119, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00002.record000
