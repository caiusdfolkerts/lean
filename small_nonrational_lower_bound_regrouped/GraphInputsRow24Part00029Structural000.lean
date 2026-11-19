module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00029Data
public import GraphInputsRow24Part00029Frames
public import GraphInputsRow24Part00029Leaves
public import GraphInputsRow24Part00029Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 648520545364606976, (certNat% 3), (certNat% 4), (certNat% 5), 18691697672192, 51228445761339392]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 720611124751368192, (certNat% 3), (certNat% 4), (certNat% 5), 18691697672192, 51228445761339392]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 7)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record031
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031
def vertexColumn : Fields := ⟨10, (certNat% 8)⟩
def kindColumn : Fields := ⟨3, (certNat% 9)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), 13194139533312]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 577604252986245120, (certNat% 12), (certNat% 14), (certNat% 15), 4947802324992]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 576461851815051264, (certNat% 17), 10376293610181099520, (certNat% 18), (certNat% 19)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 324259173304893440, 1730508165407047680, 299342040662016, (certNat% 21)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 1730508156817113088, (certNat% 23), 6459630813184, (certNat% 24)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 1154047404513689600, (certNat% 23), 9223372105574252544, (certNat% 27)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 28)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c8 c9
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c8 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c8 c12
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c8 c13
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c14
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c8 c15
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c8 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c17 c11
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 36028797018963968, 577586652210266112, 9223372039002259456, (certNat% 30)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), 282711944069120, 1730508156817113088, 9223380835095281664, (certNat% 32), (certNat% 33)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 30), 10376293610181099520, (certNat% 17), 577604253053353984, 282711944069120, 13743895347200]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c24 c6
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c25 c5
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c26 c4
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c27 c3
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c28 c2
  c29
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record031

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record038
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038
def vertexColumn : Fields := ⟨10, (certNat% 35)⟩
def kindColumn : Fields := ⟨3, (certNat% 36)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), 153122662208503808, (certNat% 40)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1727130343279951872, 578712620836585472, (certNat% 41), (certNat% 39), (certNat% 42), (certNat% 43)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 45), 288072046477312, 36028797018963968]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 47), 288072046477312, 36028797018963968, 6917529027641081856]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c4 c2
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), 411217348788224, (certNat% 49), (certNat% 50), 686798943174000640]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 52), 704817739729993728, (certNat% 53), 1153944050420678656, (certNat% 54), 432416001691222016]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c9 c1
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c10 c0
  c11
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record038
