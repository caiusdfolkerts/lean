module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00029Data
public import GraphInputsRow26Part00029Frames
public import GraphInputsRow26Part00029Leaves
public import GraphInputsRow26Part00029Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00029.record036
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record036
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨16, by decide⟩, ⟨17, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6), 2323336931573760]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record036_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record036_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record036_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record036_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record036_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record036_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record036_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record036_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record036_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00029.record036

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00029.record045
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record045
def vertexColumn : Fields := ⟨10, (certNat% 7)⟩
def kindColumn : Fields := ⟨3, (certNat% 8)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨20, by decide⟩, ⟨23, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨71, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 10), 14293659549696, 4035225266123964416, 805306368]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 576461851824488448, (certNat% 12)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 15), (certNat% 16), 576460752303423488]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [577532777492119552, (certNat% 16), (certNat% 17), (certNat% 18), 53601191854080]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [759831254269952, 577586652211314688, 365038128857088, (certNat% 19), (certNat% 20), (certNat% 21)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c6 c3
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
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record045_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record045_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record045_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record045_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record045_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record045_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record045_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record045_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record045_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00029.record045
