module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow19Part00037Data
public import GraphInputsRow19Part00037Frames
public import GraphInputsRow19Part00037Leaves
public import GraphInputsRow19Part00037Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00037.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨29, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 140754668224512, 9008298766368768, 3161095929856, 25895697857380352]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 3), 281509336449024, 9008298766368768, 3161095929856, 25895697857380352]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 4504149383184384, 140754668224512, 127543348822016, 1044835113549955072]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 4504149383184384, 281509336449024, 127543348822016, 1044835113549955072]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1030748222174003200, 13510798882242560, 36028797555834880, 4260607557632, (certNat% 6)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 127543382376448, 2662879723520, 1008947054019346432]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), 30399297484750848, 1044835113549955072, 4260607557632, 127543348822016, 140789027962880]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨19, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00037.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00037.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023
def vertexColumn : Fields := ⟨10, (certNat% 9)⟩
def kindColumn : Fields := ⟨3, (certNat% 10)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨83, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), 51564773376, 206259093504, 8459649024, 17317308137472]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00037.record023
