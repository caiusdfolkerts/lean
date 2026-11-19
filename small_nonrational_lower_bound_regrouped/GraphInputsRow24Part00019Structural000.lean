module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00019Data
public import GraphInputsRow24Part00019Frames
public import GraphInputsRow24Part00019Leaves
public import GraphInputsRow24Part00019Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record031
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 1152930300699869184, 792633534417207296, (certNat% 3), (certNat% 4)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 755914244096, (certNat% 6), 9370020499721027584, (certNat% 7), (certNat% 8)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 9345848836096, (certNat% 10), 2017612633061982208, 9223372311732682752, 144115188075855872]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), 9223653786717782016, (certNat% 13), 35433480192, 8796093022208]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17), 8796093022208, 9223372311732682752]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [10952764169450946560, (certNat% 18), 146648463403122688, 360287972337123328, (certNat% 16), (certNat% 19)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 9223372311732682752, (certNat% 12), 216172782650654720, 1441151882906042368, (certNat% 4)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 17798344474624, 9511602413006487552, (certNat% 22)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), 1441151887201009664, 9223372311732682752, (certNat% 24), 144115189686468608, 72057594037927936]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 39728447488, 9223372311732682752, (certNat% 27), 1152930300699869184]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), 1152930339354574848, (certNat% 27), 9655717601082343424, (certNat% 29), 3758096384, 2533549676691456]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c15 c6
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c16 c5
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c17 c4
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c18 c3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c19 c2
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record031

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record046
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046
def vertexColumn : Fields := ⟨10, (certNat% 30)⟩
def kindColumn : Fields := ⟨3, (certNat% 31)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 33), (certNat% 34), 28621662060544, (certNat% 35), 35184372088832]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), (certNat% 37), (certNat% 38), 126382264543084544, (certNat% 39), 144115188075855872]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 11579231830016, (certNat% 37), (certNat% 41), 10376293541461622784, 2305843009213693952]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 33), 56576470318841856, (certNat% 43), (certNat% 44), 1152921504606846976]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), 19791746170880, (certNat% 46), 90071992547409920, (certNat% 47), 30366760960]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), 30870077440, 28587302322176, 18014398509481984, 13836184504944820224, (certNat% 49)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), 30870077440, 18016597532737536, 108086391056891904, (certNat% 51), (certNat% 52)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), 30333206528, (certNat% 37), (certNat% 47), 2783138807808, 9223372036854775808]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 30903631872, (certNat% 55), (certNat% 56), 56576470318841856, 11579231830016, 17592186044416]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00019.record046
