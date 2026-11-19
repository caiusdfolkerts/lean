module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00078Data
public import GraphInputsRow26Part00078Frames
public import GraphInputsRow26Part00078Leaves
public import GraphInputsRow26Part00078Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩, ⟨82, by decide⟩, ⟨92, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 35218731827200, 101334384640, 103766409871360]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), (certNat% 3), 35218731827200, 101602820096, 104041287778304]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), 4647714815580569600, 130996502528, (certNat% 7)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 10), 131941395333120, (certNat% 11)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), 64424509440, 4647714815580569600, (certNat% 14)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 9), (certNat% 10), 63771674411008, (certNat% 16)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 9), 4647714815580569600, 128849018880, (certNat% 18)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), 61572651155456, (certNat% 21), (certNat% 22)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 3), (certNat% 24), (certNat% 25)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), (certNat% 28), (certNat% 29), 4611686018427387904]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), (certNat% 32), (certNat% 29), (certNat% 33), (certNat% 34)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c16 c3
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c17 c2
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010
def vertexColumn : Fields := ⟨10, (certNat% 35)⟩
def kindColumn : Fields := ⟨3, (certNat% 36)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩, ⟨84, by decide⟩, ⟨90, by decide⟩, ⟨94, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), (certNat% 40), (certNat% 41)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), (certNat% 44), (certNat% 45), 255550554112]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 43), (certNat% 44), (certNat% 47), 255550554112]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 43), (certNat% 44), (certNat% 45), 1046735069642752]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 43), (certNat% 44), (certNat% 47), 1046735069642752]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 51), (certNat% 52), 74785044299776, (certNat% 41)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 54), (certNat% 55), (certNat% 56), 1117103813820416]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), (certNat% 59), (certNat% 52), (certNat% 60)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 62), 255550554112, (certNat% 63), 1047009947549696]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), 273804165120, (certNat% 65), (certNat% 66), 1121501860331520, (certNat% 52)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c13 c5
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c14 c4
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c15 c3
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c16 c2
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c17 c1
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c18 c0
  c19
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record010
