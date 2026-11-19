module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow30Part00050Data
public import GraphInputsRow30Part00050Frames
public import GraphInputsRow30Part00050Leaves
public import GraphInputsRow30Part00050Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00050.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩, ⟨95, by decide⟩, ⟨98, by decide⟩, ⟨105, by decide⟩, ⟨108, by decide⟩, ⟨115, by decide⟩, ⟨118, by decide⟩, ⟨125, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 140187732541440, 1148417904979476480, (certNat% 5)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00050.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00050.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007
def vertexColumn : Fields := ⟨10, (certNat% 6)⟩
def kindColumn : Fields := ⟨3, (certNat% 7)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨95, by decide⟩, ⟨98, by decide⟩, ⟨106, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), 8813272891392, (certNat% 10), 14680064]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), 8813306445824, (certNat% 13), (certNat% 14)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), 1125917087236096, (certNat% 17), 18014398513676288]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 12), 8813306445824, (certNat% 19), (certNat% 14)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 16), 2251816994078720, (certNat% 21), (certNat% 22)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), 8813306445824, 3377699922378752, (certNat% 17), 18014398511579136]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00050.record007
