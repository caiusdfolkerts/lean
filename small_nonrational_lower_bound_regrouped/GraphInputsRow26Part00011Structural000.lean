module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00011Data
public import GraphInputsRow26Part00011Frames
public import GraphInputsRow26Part00011Leaves
public import GraphInputsRow26Part00011Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 2), (certNat% 3)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 36028797018963968, 563087392374784]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 563087392374784, 324259173174870016, (certNat% 6)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 7), (certNat% 8), 2251799813685248]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c1 c7
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c1 c8
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c1 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c1 c11
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c1 c12
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c1 c13
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c1 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c1 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c1 c17
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 536870912, (certNat% 10)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 10), (certNat% 12), 288230376158003200]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c22 c15
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 563087392374784, 324259173174870016, (certNat% 14), 1152921504608944128]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c25 c6
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 5629499534213120, (certNat% 14), 324259173175394304, 1152921504608944128]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c1 c7
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c1 c28
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 12), 570425344]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 324259173170675712, (certNat% 14), 137438953472]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 6), 637534208, 563087392374784]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 137606725632, 537919488, 324259173175394304, 1152921504608944128]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 324259173174870016, (certNat% 6), (certNat% 22), 563087560146944, 70369348157440]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨17, by decide⟩ c38 c35
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c39 c27
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c40 c26
  c41
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024
def vertexColumn : Fields := ⟨10, (certNat% 23)⟩
def kindColumn : Fields := ⟨3, (certNat% 24)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨58, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 35218731958272, (certNat% 27), 134217728]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 27), (certNat% 29), 201457664, 171798953984, 175921862017024]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record024
