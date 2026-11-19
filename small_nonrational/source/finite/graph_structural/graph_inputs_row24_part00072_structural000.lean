module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00072Data
public import GraphInputsRow24Part00072Frames
public import GraphInputsRow24Part00072Leaves
public import GraphInputsRow24Part00072Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00072.record043
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record043
def vertexColumn : Fields := ⟨10, hexnat% "2e89d13c2f2e2aca72b2aaa9a8ea668ba99a568d8b61d94e2b86e4789e0fae1ac6713a5994e4b94d4b51d54d4b4ad4749d0f6c3a8e6338e9364e538ccb31cd8b52ccb2ac6b46c9b0ed4729c6725c570dc8f0bc1fac06ca49164384e2c4a91a465454354344d0b51324d0b22c4b41c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6d36db6db6da6936d34da4924934db69369a49249a692492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2001621fe8243d7f000000", 70368744177664, 9223372311732682752, 1649267441664]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2001609fe8243d7f000000", hexnat% "20000400000000000", 1924145348608]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2001601fe8043d5b000000", 9223372311732682752, hexnat% "20000400000000000", 1649334550528, 35184908959744]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "16019a8008d0f000000", 144115189418033152, 9223372517891112960, hexnat% "2000020000440000000000", 36283883716608, 306244775198064640]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [11522459853842808832, hexnat% "2000020000440000000000", 1975684956160, hexnat% "1200000000100000000", hexnat% "400000000040000000", 35184372088832]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200042906045f44e000000", hexnat% "1000100000101000000", 35185177395200, 758856537211928576, 288230376151711744, hexnat% "200000000800000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "229468642c21000000", 1992965488640, 756604737398243328, hexnat% "1400100000000000000", hexnat% "2000000000000048000000", 4563402752]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000021060442000000000", 9261652633720979456, hexnat% "1200000000101000000", 1008806316665208832, hexnat% "400100001040000000", 1975752065024, 35185177395200]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c13 c6
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record043_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record043_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record043_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record043_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record043_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record043_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record043_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record043_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record043_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00072.record043

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00072.record046
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record046
def vertexColumn : Fields := ⟨10, hexnat% "2f0ba0f86713c2f07cb8ad2aca723cacaaaa6a3a99a568da2e87aa99962d876638ae1b91e2785e0fab19c6a99a5594e4b91e6a54d4b51d52d2b46d4749d1743da8e63a4e5354e332cc73a2e4b52e2b2ac6b46c9b16c3ba1e2729c6725c570dc8f13c2f07cb42b1162590e23a611c469454354342d90d1314d0b12d0705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db4db6db6db6db69349a4db4d36d349249369a69369a4da4d36db492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000a40659a0ee00000", hexnat% "a2001000000000000", 82190693199511552, 324259173187452928, hexnat% "9800000000000000000", hexnat% "800024000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000340659a07e00000", hexnat% "a2001000000000000", 324259173304893440, 586593851465007104, hexnat% "41800000000000000000", hexnat% "800024000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "49800000000004a00000", 107210973642752, 658651445502935040, hexnat% "a2240000000000000", 324259173321670656, hexnat% "800000000000000800000000", hexnat% "24000001041002400000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record046_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record046_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record046_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record046_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record046_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record046_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record046_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record046_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00072.record046_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00072.record046
