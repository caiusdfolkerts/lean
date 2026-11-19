module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00009Data
public import GraphInputsRow16Part00009Frames
public import GraphInputsRow16Part00009Leaves
public import GraphInputsRow16Part00009Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00009.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record008
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 2611340115968, 1152956688978935808, 571746314878976, 9223653511831486464]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [10376698377151709184, (certNat% 3), 2474974904320, 571746319073280, (certNat% 4), 134217728]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 79164874948608, 2680126701568, 844425198567424, 9223372036871553024]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 87960963776512, 10376293541545508864, 893487415296, 571746319073280, 2345589014528, 281474976710656]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00009.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00009.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record024
def vertexColumn : Fields := ⟨10, (certNat% 7)⟩
def kindColumn : Fields := ⟨3, (certNat% 8)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [874826426639974400, (certNat% 9), 7318366574346240, 1924380229632, 72127962782105600, 8321499136, 422212465065984]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record024_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00009.record024

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00009.record046
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record046
def vertexColumn : Fields := ⟨10, (certNat% 10)⟩
def kindColumn : Fields := ⟨3, (certNat% 11)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 3161095929856, (certNat% 13), 11540542764613632, 140738562097152]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), 1691602934300672, 11681211533492224, 4617966016528384, 107139301376]
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
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record046_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record046_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record046_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record046_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record046_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record046_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record046_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record046_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record046_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00009.record046
