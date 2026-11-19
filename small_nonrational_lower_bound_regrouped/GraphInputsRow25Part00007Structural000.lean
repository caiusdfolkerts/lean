module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow25Part00007Data
public import GraphInputsRow25Part00007Frames
public import GraphInputsRow25Part00007Leaves
public import GraphInputsRow25Part00007Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record064
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 9804371573157658624, (certNat% 5), 143623706378240, (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 9232379236109516800, 1170935907411296256, (certNat% 8), (certNat% 9), 288230377225453568, (certNat% 10)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 1441151885187743744, (certNat% 12), (certNat% 13), 15762599769538560, (certNat% 3), 2305843009213693952]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 20266198323167232, 297237576480194560, 1700807049216, (certNat% 15), (certNat% 16)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 9804336388785569792, 20266198323167232, (certNat% 18), (certNat% 19), (certNat% 20), (certNat% 21)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 143486267424768, (certNat% 23), (certNat% 3), (certNat% 9), 9813343588577181696, 1073741824]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 143486267424768, (certNat% 25), (certNat% 3), (certNat% 9), 9813343588577181696, 1073741824]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), 1170935907444850688, (certNat% 27), (certNat% 28), 9813343588577181696, (certNat% 29), 2251800887427072, 2594073385365405696]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record064

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record070
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070
def vertexColumn : Fields := ⟨10, (certNat% 30)⟩
def kindColumn : Fields := ⟨3, (certNat% 31)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 33), 288232850187091968, 720575940379279360, (certNat% 34), (certNat% 35)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), 432345564361785344, 11287174053888, (certNat% 37), 576460754182471680, (certNat% 38), (certNat% 39)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), (certNat% 42), (certNat% 43), (certNat% 44), 3377699720527872, (certNat% 33)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 43), 1134713179734016, (certNat% 46), (certNat% 47), (certNat% 48), 68719476736]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 48), (certNat% 50), (certNat% 51), 540431955418677248, 1152921504606846976, (certNat% 52)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 54), (certNat% 55), (certNat% 56), 1407375420424192, (certNat% 57), 2305843009213693952]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), 360287970256748544, (certNat% 46), (certNat% 59), (certNat% 60), (certNat% 61), (certNat% 62)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), 1407375420424192, 720575940379279360, (certNat% 64), 11529215063248338944, (certNat% 65)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), 1134713179734016, (certNat% 43), 567416719409152, (certNat% 67), (certNat% 68)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), 567416719409152, 540431955351568384, (certNat% 70), (certNat% 59), (certNat% 67), 1125917623582720]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), (certNat% 72), 3729543441416192, (certNat% 73), (certNat% 51), 9223372054034644992, 536870912]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 75), 9223372054034644992, 576460752907403264, (certNat% 76), 540431955284459520, 68719476736]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 78), (certNat% 79), 828662331503280128, (certNat% 70), (certNat% 51), (certNat% 72), 1125917623582720]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c18 c7
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c21 c4
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c22 c3
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c23 c2
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record070
