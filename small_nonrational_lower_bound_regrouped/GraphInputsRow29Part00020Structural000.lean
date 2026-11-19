module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00020Data
public import GraphInputsRow29Part00020Frames
public import GraphInputsRow29Part00020Leaves
public import GraphInputsRow29Part00020Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨86, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 18471795346636800, (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 8796227239936, (certNat% 8), (certNat% 9), 2211941711872, (certNat% 10)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 8830586978304, (certNat% 12), (certNat% 13), 2211941711872, (certNat% 10)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 549898420224, (certNat% 15), (certNat% 16), (certNat% 17), 144678138029277184]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 15), (certNat% 16), 2290089984, (certNat% 17), 144678138029277184]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 21), 72268700354347008, (certNat% 22)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 10), 551903297536, (certNat% 24), (certNat% 17), 144678138029277184]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), 144959613274423296, 9345848836096, (certNat% 26), (certNat% 27), (certNat% 28), 10779361280]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008
def vertexColumn : Fields := ⟨10, (certNat% 29)⟩
def kindColumn : Fields := ⟨3, (certNat% 30)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), (certNat% 33), 11529496529635115008, 1688901399871488]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 11529215071838273536, (certNat% 35), 1759255111663616, (certNat% 36), 422216760033280, (certNat% 37)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011
def vertexColumn : Fields := ⟨10, (certNat% 38)⟩
def kindColumn : Fields := ⟨3, (certNat% 39)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨87, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), 1729663732021198848, 25773998080, (certNat% 42), (certNat% 43)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 45), (certNat% 46), (certNat% 47), (certNat% 48), (certNat% 49)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 51), (certNat% 52), (certNat% 53), (certNat% 54), (certNat% 55)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), (certNat% 58), (certNat% 59), (certNat% 47), 281475186425856, (certNat% 60)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record011
