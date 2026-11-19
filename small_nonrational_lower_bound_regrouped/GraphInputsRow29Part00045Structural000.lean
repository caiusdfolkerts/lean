module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00045Data
public import GraphInputsRow29Part00045Frames
public import GraphInputsRow29Part00045Leaves
public import GraphInputsRow29Part00045Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨82, by decide⟩, ⟨86, by decide⟩, ⟨91, by decide⟩, ⟨99, by decide⟩, ⟨103, by decide⟩, ⟨107, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 14740281580383633408, 2467972597174763520, 638303007145984, 8869795332096, 79691776]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020
def vertexColumn : Fields := ⟨10, (certNat% 4)⟩
def kindColumn : Fields := ⟨3, (certNat% 5)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), 9259400833873739776, (certNat% 8)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 34829500416, (certNat% 10), 43982612594688, (certNat% 7), (certNat% 11)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 4415796805632, 69122129920, 633318697598976, (certNat% 13), (certNat% 14)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), (certNat% 11), (certNat% 13), 34493956096]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 550561120256, 206158430208, 9259400833873739776, (certNat% 18), (certNat% 19)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 7), (certNat% 21), (certNat% 10), (certNat% 11)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 10), (certNat% 23), (certNat% 7), (certNat% 13)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [70367636881408, 633319771340800, (certNat% 11), (certNat% 13), (certNat% 14)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 21), (certNat% 25), (certNat% 11), 1100048498688]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 10), (certNat% 23), 52776558133248, (certNat% 7), (certNat% 13)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 13), 309371863040, 40269613367296, (certNat% 28), 17592186044416]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 13), (certNat% 30), (certNat% 31), 275548995584, 40269613367296, 17626545782784]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c19 c4
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c21 c2
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024
def vertexColumn : Fields := ⟨10, (certNat% 32)⟩
def kindColumn : Fields := ⟨3, (certNat% 33)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨105, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1188950302162681856, (certNat% 34), (certNat% 35), (certNat% 36), 545357968703488, 15633735483392]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record024
