module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow25Part00020Data
public import GraphInputsRow25Part00020Frames
public import GraphInputsRow25Part00020Leaves
public import GraphInputsRow25Part00020Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00020.record046
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨84, by decide⟩, ⟨89, by decide⟩, ⟨96, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 8724152320, 21751660544, 35517366272, 412316860416, 6291456]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 8757706752, (certNat% 5), (certNat% 6), (certNat% 7), 4611703610613432320, 1152921504606846976]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), 8757706752, (certNat% 5), (certNat% 10), (certNat% 11)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), 38671482880, 292057776128, 6917546619827126272, (certNat% 14), 4194304]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 463856467968, (certNat% 13), (certNat% 7), (certNat% 10), 19791242854400, 94371840, 12889096192]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00020.record046
