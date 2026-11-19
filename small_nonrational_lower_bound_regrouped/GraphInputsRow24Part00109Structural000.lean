module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00109Data
public import GraphInputsRow24Part00109Frames
public import GraphInputsRow24Part00109Leaves
public import GraphInputsRow24Part00109Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00109.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 6918655064986877952, (certNat% 5), 4504149383184384]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 3642132267008, (certNat% 4), (certNat% 7), 6922032627268452352, 549755813888]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), 37383932215296, (certNat% 10), (certNat% 11)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 14), 283967131484160, (certNat% 15), 35184372088832]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 316676528668672, (certNat% 17), (certNat% 18), 72198331526283264]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), 4504149387378688, 319957883682816, 72198340384653312, (certNat% 20), 275951648768]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6923158733425999872, (certNat% 21), (certNat% 14), (certNat% 15), 319957883682816, 141030619873280, 549793562624]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00109.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00109.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015
def vertexColumn : Fields := ⟨10, (certNat% 22)⟩
def kindColumn : Fields := ⟨3, (certNat% 23)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), 38482906972160, (certNat% 26), (certNat% 27), (certNat% 28)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 27), 22517999479029760, 6643777536, (certNat% 28)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), 23643899117436928, (certNat% 32), (certNat% 33), 3298534883328, 6912212992]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00109.record015
