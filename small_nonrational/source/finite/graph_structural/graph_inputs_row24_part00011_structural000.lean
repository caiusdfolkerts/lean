module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00011Data
public import GraphInputsRow24Part00011Frames
public import GraphInputsRow24Part00011Leaves
public import GraphInputsRow24Part00011Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012
def vertexColumn : Fields := ⟨10, hexnat% "3d3c23caaa568e6358b61da8e538ae17bc13c6a9564e5354b51d68d534ad17783d0ec370ea338d5334cb31ce8b52e2b4acab86d1b16e8751c6725e0f43c8f13c3cc283a318a6158360b81ec2439314a5154350b41dc0e8350cc328c530ce0b42c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6924da4db6924da492492492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "410415ed117600000000", 261718127149056, 148619337459040256, hexnat% "38800000000000000", hexnat% "38800000000000000000", 562949953421312]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20820bba83ee00000000", 306596618382082048, hexnat% "48048000000000000000", 66039417143296, hexnat% "10010004000000000000", hexnat% "1001000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "490495ff11e400000000", 144295542342549504, hexnat% "30030000000000000000", hexnat% "800800020200000000", 79233556676608]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800820838200000000", hexnat% "1001001100400000000", 414331165718085632, 148623185749737472, hexnat% "48048002006000000000", hexnat% "3003000c000000000000", 114452288503808]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record060
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060
def vertexColumn : Fields := ⟨10, hexnat% "5707cd4b8a5ab1aa695a1e8e6a59561d94e1b91e2785e0fb51e2569c66995647939695554755346d4749d1743de0f43a8d6338f13a4e5354c73c2e8b62d4b4acab1ae1b46c9b16c3ba1d4731ca719e1745c9715c3743c8f13c2f07cacc49522a91a298661588e0b81ec45512a519294651548d0b41d"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b4da69a69349249b4d34d269249b6da6d36db69b4db6da4db4da691249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000080000000180400000", hexnat% "20001000000001200000", hexnat% "4a22000000000000000", hexnat% "94440000000000000000000", 5071497517334528, hexnat% "208010400000000000000", hexnat% "90004800000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record060
