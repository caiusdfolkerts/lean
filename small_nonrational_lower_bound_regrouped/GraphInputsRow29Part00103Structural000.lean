module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00103Data
public import GraphInputsRow29Part00103Frames
public import GraphInputsRow29Part00103Leaves
public import GraphInputsRow29Part00103Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00103.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [864691179994742784, (certNat% 2), (certNat% 3), (certNat% 4), 4479516672, 11542724608, 1153433600]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00103.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00103.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005
def vertexColumn : Fields := ⟨10, (certNat% 5)⟩
def kindColumn : Fields := ⟨3, (certNat% 6)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨61, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 2305843559103725568, (certNat% 8), (certNat% 9), 33554432]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 38654705664, (certNat% 11), (certNat% 12), (certNat% 13)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17), 4462739456, 2306969458876350464]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), 422212473454592, 1126449729765376, 2251799813685248]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 2306969458876350464, (certNat% 21), (certNat% 22), (certNat% 23), 67108864]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 2305843009347911680, (certNat% 25), 34397487104, (certNat% 26)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), 136314880, (certNat% 28), 2306968909120536576]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 25), (certNat% 28), (certNat% 30)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), 2306968909120536576, (certNat% 25), (certNat% 30), (certNat% 28), 17179869184]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), 431008566476800, (certNat% 33), (certNat% 30), 17179869184, (certNat% 28)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 6291456, (certNat% 35), (certNat% 19), 1126449863983104, (certNat% 36)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), 2305843559103725568, 51543801856, (certNat% 38), (certNat% 23), (certNat% 39)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), (certNat% 19), (certNat% 42), 14680064, 1126449863983104, 17179869184]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c22 c7
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c23 c4
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00103.record005
