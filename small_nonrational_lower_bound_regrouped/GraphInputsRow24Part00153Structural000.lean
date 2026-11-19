module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00153Data
public import GraphInputsRow24Part00153Frames
public import GraphInputsRow24Part00153Leaves
public import GraphInputsRow24Part00153Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00153.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 33777005795213312, (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 3), (certNat% 8), (certNat% 5), 33777014385147904, (certNat% 9)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), 200111250472960, 32088175262302208, (certNat% 12), 2322168557862912]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 123145302310912, (certNat% 14), (certNat% 15), (certNat% 16)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 15), 123145302310912, (certNat% 17), (certNat% 18)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 14), (certNat% 15), (certNat% 16)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 263882790666240, (certNat% 22), (certNat% 23), (certNat% 24)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), (certNat% 3), 266081813921792, (certNat% 27)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), (certNat% 12), 29273406167842816, (certNat% 30), (certNat% 31)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 33), (certNat% 11), 32651108035854336, (certNat% 12), 2322168557862912]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 123145302310912, (certNat% 15), (certNat% 17), (certNat% 18)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), (certNat% 36), (certNat% 16), (certNat% 37)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), (certNat% 40), 125344325566464, (certNat% 41)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c17 c3
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c18 c14
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), 68169720922112, 33214047251857408, (certNat% 43), 70368744177664]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 29), (certNat% 3), (certNat% 5), 33776997205278720, (certNat% 45)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 19241453486080, (certNat% 45), (certNat% 47), 31525197391593472]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 49), (certNat% 11), 90159953477632, (certNat% 50), (certNat% 51)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 43), (certNat% 33), (certNat% 53), 28710449771970560, (certNat% 54)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), 27023247098773504, (certNat% 56), (certNat% 53), (certNat% 57), (certNat% 58), (certNat% 59)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c27 c22
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c28 c21
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c29 c20
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c30 c19
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c31 c13
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c32 c12
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c33 c11
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c34 c2
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c35 c1
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c36 c0
  c37
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00153.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00153.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004
def vertexColumn : Fields := ⟨10, (certNat% 60)⟩
def kindColumn : Fields := ⟨3, (certNat% 61)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 580542139465728, 18014398509481984]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c3 c4
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), 580542139465728, (certNat% 64), (certNat% 65)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), (certNat% 67), (certNat% 68), 949978046398464, (certNat% 69)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), 18031990695526400, (certNat% 65)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c11 c5
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c12 c2
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), (certNat% 73), (certNat% 74), (certNat% 75), 844424930131968]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), 870813209198592, 32651097298436096, (certNat% 74), (certNat% 77), (certNat% 78)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), (certNat% 80), (certNat% 81), (certNat% 82), (certNat% 83), 562964985806848, 18014639027650560]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c19 c18
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00153.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00153.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005
def vertexColumn : Fields := ⟨10, (certNat% 84)⟩
def kindColumn : Fields := ⟨3, (certNat% 85)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 86), (certNat% 87), (certNat% 88)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 89), 825707462656, (certNat% 88), (certNat% 90)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 91), (certNat% 92), (certNat% 93)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 94), (certNat% 88), (certNat% 93), (certNat% 87)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c10 c4
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 95), (certNat% 96), (certNat% 90), (certNat% 97), (certNat% 87)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 98), (certNat% 99), 629346926592, (certNat% 100), (certNat% 101), (certNat% 102)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 103), 70370623225856, (certNat% 104), (certNat% 105), 549755813888]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 106), 562951832469504, (certNat% 104), (certNat% 105), 549755813888]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 107), (certNat% 108), (certNat% 109), 551366426624, 633318697598976]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 110), (certNat% 111), (certNat% 112), 551366426624, (certNat% 113), 633318697598976]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c22 c17
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 114), (certNat% 115), (certNat% 116), 577203339264, 1057730454355968, (certNat% 117), (certNat% 118)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c25 c16
  c26
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00153.record005
