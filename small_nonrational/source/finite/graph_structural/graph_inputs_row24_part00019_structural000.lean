module
prelude
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
def vertexColumn : Fields := ⟨10, hexnat% "f4e31ac2f1ca6a95ad19c6698e655876c398e8b92e2ba1e4783e3c789724d92e785d15c5394d52d475c368d6362d2b61d2743dd0dc338c73c2d8b52ccb8acab86c5bc1d8791d4731e2729c6785e0f43c8f0bc1f7130a0eb06518560d8a90e4c5294550d4530ce0b0ac1b81c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6d26d24db6da6db4da4926db4da6da4db4924d249249b489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "32000840910fbfcc00000", 1152930300699869184, 792633534417207296, hexnat% "8100000000000000000", hexnat% "10000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "320001400004bfcc00000", 755914244096, hexnat% "8000000080000000000", 9370020499721027584, hexnat% "10000900100000000000", hexnat% "100000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "330000100103bfcc00000", 9345848836096, hexnat% "8100009000000000000", 2017612633061982208, 9223372311732682752, 144115188075855872]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10001f0810b2b8400000", hexnat% "320000000000100000000", 9223653786717782016, hexnat% "8100000000004000000", 35433480192, 8796093022208]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30000f0010bbfcc00000", hexnat% "100001000000000000000", hexnat% "208000000000000000000", hexnat% "100009000000000000", 8796093022208, 9223372311732682752]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [10952764169450946560, hexnat% "10100000100000000000", 146648463403122688, 360287972337123328, hexnat% "208000000000000000000", hexnat% "120000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "810080918ba5cc00000", 9223372311732682752, hexnat% "320000000000100000000", 216172782650654720, 1441151882906042368, hexnat% "10000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "328101a0908cbfcc00000", 17798344474624, 9511602413006487552, hexnat% "10000100000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30810080918ba1cc00000", 1441151887201009664, 9223372311732682752, hexnat% "30000000000000000000", 144115189686468608, 72057594037927936]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18000f0110b2bc400000", hexnat% "100008000000800000", 39728447488, 9223372311732682752, hexnat% "320000000000000000000", 1152930300699869184]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800090010b21c400000", 1152930339354574848, hexnat% "320000000000000000000", 9655717601082343424, hexnat% "10100000000000000000", 3758096384, 2533549676691456]
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
def vertexColumn : Fields := ⟨10, hexnat% "1e87639467352568b61d8ae1b89e179e1e4751744f1725a95a4e96655936785c5695654b51d70d6346d4749d17743c4e5354cb31cf0b52cab46c9b16e2729c6725c570de0f23c4f07cac1aa160bb1164551625492a469296152548d0b46384c5312c2b81c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6936d24d24926d249b49a6d24d349b492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "601004d0047fe000000", hexnat% "2c000008000000000", hexnat% "200380000000000000", 28621662060544, hexnat% "183000000000000000", 35184372088832]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "600800402cffe000000", hexnat% "34008000000000000", hexnat% "100000380000000000", 126382264543084544, hexnat% "283000000000000000", 144115188075855872]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60003c51047fe000000", 11579231830016, hexnat% "34008000000000000", hexnat% "380000200000000000", 10376293541461622784, 2305843009213693952]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60001043a4ffe000000", hexnat% "2c000008000000000", 56576470318841856, hexnat% "380200000000000000", hexnat% "12000000000000000", 1152921504606846976]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3af2802888cc000000", 19791746170880, hexnat% "10009000000000000", 90071992547409920, hexnat% "6000004004000000000", 30366760960]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3b33892008ce000000", 30870077440, 28587302322176, 18014398509481984, 13836184504944820224, hexnat% "6000000004000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ab2013888ce000000", 30870077440, 18016597532737536, 108086391056891904, hexnat% "14008004000000000", hexnat% "6000004000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3833c13800ee000000", 30333206528, hexnat% "34008000000000000", hexnat% "6000004004000000000", 2783138807808, 9223372036854775808]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60831040040cc000000", 30903631872, hexnat% "3c000000000000000", hexnat% "300200200000000000", 56576470318841856, 11579231830016, 17592186044416]
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
