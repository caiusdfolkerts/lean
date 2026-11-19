module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00062Data
public import GraphInputsRow24Part00062Frames
public import GraphInputsRow24Part00062Leaves
public import GraphInputsRow24Part00062Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00062.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record011
def vertexColumn : Fields := ⟨10, hexnat% "1b45b15c4f2aa5aa9a5693a2eac6599564d8b65392e1b91e1783e6c749aa569a65594e4b9b15a559595555352d54d4b46d4745d0f6c3a8d63a4d534ccb3a2d4b8ad2b2ac6b86d1b26c5b0ee8791d4731d2719d1715c3743c4f0bc1f928a625a495252946545494a545495a0e4328c9382c4b0ac1b21c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6db69b6db69a6936924924d36934da492492492492492692249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ea005187f3000000", hexnat% "400000001001000000000", 18014432936329216, hexnat% "5601000000000000000", 11408532649803776, 42193758715904]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "167da69befff7000000", 71468255805440, hexnat% "400002000000000000000", hexnat% "4000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "167fa29bef1f7000000", hexnat% "4000000400000000000", 1116691496960, 18014441459154944, hexnat% "400000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [606225613694435328, hexnat% "400206000000000000000", hexnat% "78000000000000000", hexnat% "5401000400000000000", 144116287604260864, 17716740096]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ea005907f3000000", hexnat% "400000001001000000000", 18014432936329216, hexnat% "5601000000000000000", 11400286312595456, 42193758715904]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "405607001ffe157000000", 29273474887319552, hexnat% "78000000000000000", 54223962112, 720575940379279360]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5641a217fe7f7000000", 18155239077052416, 2251799813685248, hexnat% "3c000000000000000", hexnat% "400002000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41a29bff3f7000000", 18014432869220352, hexnat% "16000000000000000", hexnat% "5600000400000000000", hexnat% "400000000000000000000", hexnat% "28000000400000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "167fa29bff177000000", hexnat% "4000000400000000000", 18014441459154944, hexnat% "400000000000000000000", 19327352832]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "167da69affff7000000", 87960930222080, hexnat% "400002000000000000000", hexnat% "4000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "167fa29aff1f7000000", hexnat% "4000000400000000000", 17609365913600, 18014441459154944, hexnat% "400000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [750324307502039040, hexnat% "400206000000000000000", hexnat% "1400000500000000000", hexnat% "78000000000000000", hexnat% "4001000000000000000", 19327352832]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [29705167452504064, hexnat% "400206000000010000000", hexnat% "78000000000000000", hexnat% "5401000400000000000", 60748017434624, 62881005568, 720575940396056576]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c19 c10
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c20 c7
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c21 c6
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c22 c5
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00062.record011
