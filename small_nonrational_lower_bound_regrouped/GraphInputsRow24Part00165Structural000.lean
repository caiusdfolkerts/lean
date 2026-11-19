module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00165Data
public import GraphInputsRow24Part00165Frames
public import GraphInputsRow24Part00165Leaves
public import GraphInputsRow24Part00165Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00165.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨83, by decide⟩, ⟨89, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 74839805132800, (certNat% 3), (certNat% 4), (certNat% 5), 8804682956800]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), 405874409472, 415615395299328, 1100585369600]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 10), (certNat% 11), (certNat% 12), 474593886208, (certNat% 13)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 74839805132800, (certNat% 15), (certNat% 16), (certNat% 17), (certNat% 18)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), 4402341478400, (certNat% 16), 141975512678400, (certNat% 20), (certNat% 21)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), (certNat% 24), 141975512678400, 411217348788224, 401579442176]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 487083651104768, (certNat% 27), (certNat% 28)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 30), (certNat% 31), 340848604610560, (certNat% 32), 328564998144]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), (certNat% 35), 406819302277120, (certNat% 36)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), (certNat% 31), 411217348788224, (certNat% 36)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 31), 483785116221440, (certNat% 41), 397821345792, (certNat% 42)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), 369904058368, (certNat% 45), (certNat% 46), (certNat% 47)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 31), 131533373440, (certNat% 49), (certNat% 50), (certNat% 51)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), 58274116272128, 337691803648, (certNat% 53), (certNat% 54)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), (certNat% 56), (certNat% 26), 372051542016, (certNat% 57), (certNat% 58)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), (certNat% 60), (certNat% 61), (certNat% 62), 405874409472, (certNat% 53), (certNat% 63)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c19 c10
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c20 c9
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c21 c8
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c22 c7
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c23 c6
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c24 c5
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c25 c4
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c26 c3
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c27 c2
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c28 c1
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c29 c0
  c30
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00165.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00165.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005
def vertexColumn : Fields := ⟨10, (certNat% 64)⟩
def kindColumn : Fields := ⟨3, (certNat% 65)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), (certNat% 67), 3765009288481734656, 684547143360315392, (certNat% 68)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), (certNat% 70), 1158867663489859584, (certNat% 71), 990950247695908864, 2308657758980800512]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), 1157706579210928128, (certNat% 73), (certNat% 74), (certNat% 75), (certNat% 76)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 78), (certNat% 79), 702614318427930624, 15551492463263744, 1297036692682702848]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 80), 15533900277219328, (certNat% 81), (certNat% 82), 990791918021509120, 2308094809027379200]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), (certNat% 84), (certNat% 70), 9640517952339968, (certNat% 85), (certNat% 86)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), 10766418077286400, (certNat% 88), (certNat% 89), (certNat% 90), (certNat% 91)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 92), 38579663995404288, (certNat% 93), (certNat% 94), 792739087533473792, 15199648742375424]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 95), 1080969463685185536, (certNat% 96), 2344422673209098240, (certNat% 97), (certNat% 98), 15199648742375424]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c15 c2
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00165.record005
