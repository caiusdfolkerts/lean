module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00143Data
public import GraphInputsRow24Part00143Frames
public import GraphInputsRow24Part00143Leaves
public import GraphInputsRow24Part00143Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00143.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record002
def vertexColumn : Fields := ⟨10, hexnat% "3e19c370bc9c8f29a8ea568da4e8ba1ea5635a362da4e33a2e2b91e2785e0fae19c4f19a4e966559365392e479b16a565655356352d58d934cd8b4ad4749d1743d98ce394d5334e334ccb31ce4b52ccb8ad2b2ac6b46c9b16c3bc1e4731e2729e1725c570de0f23c4f0bc1f4590e344b1324a9454954348d90e2344c530cd0b12c2b81d0705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6db6db69b6da69b4d36d34d269a49b4d24924924924d249a692492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400a000cbaf5bd5dc00000", 1418369999831040, hexnat% "40015000000002000000", hexnat% "1002a0000000020000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400a000c97afbd5dc00000", 11346959998648320, hexnat% "40015000000002000000", hexnat% "1002a0000000020000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400a284c3fc0bc7d400000", 36037597406953472, hexnat% "11000000002800000", 60473139527680, hexnat% "100020000000000000000", hexnat% "40000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "210cb6803d7fc00000", hexnat% "400a000000008000000000", 119846767427584, hexnat% "1000a0009000000000000", hexnat% "40005000120000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "404a015c0937b877c00000", hexnat% "1002a0000000000000000", 36107983331000320, 15340386364948480]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "410a2a0c1b92b87e400000", hexnat% "40015000000000000000", 46161917655384064, 119846792593408]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "414a2b5c0810b072400000", 36028852920647680, 1418369999831040, 14214486458105856, 111050699571200]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000befd357f800000", hexnat% "4000000800008800400000", hexnat% "1020a0001000000000000", hexnat% "40005000020000000000", hexnat% "210400000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000bffd357f800000", hexnat% "4000000800008800400000", hexnat% "42005000020000000000", hexnat% "210400000000000000", hexnat% "1000a0000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000bfdf357a800000", 35184460169216, hexnat% "4000000800008800000000", hexnat% "2021400000000000000", hexnat% "100280000000000000000", hexnat% "40014000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14a2a04bfffb07fc00000", hexnat% "4000000800000800000000", 4611686035607257088, hexnat% "11000000000000000", 4294967296]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14a2a04bfe1b07a400000", hexnat% "4000000800000800000000", 5764627314243534848, 8817634967552, hexnat% "10000000001800000", 4398046511104]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "410800082440b872400000", hexnat% "2a0400000000000000", 7740561993760768, 36037614653931520, hexnat% "40015000000000000000", 60473164693504, hexnat% "2000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c16 c7
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c19 c4
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00143.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00143.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record008
def vertexColumn : Fields := ⟨10, hexnat% "b90ec670dc2f26a3a8da2ea66398d62d94e3392e2b86e4789e1783eb86693a599364b9b16a5994e5654d52d58d534cd4b4ad1b51d2745d0f66338cd32ce4b52ccb8ad2b2ac6b26c5b0ef0751cc749ca719e1725c570dd0f23c4f0bc1f46a4689916324a946499914c5894a54549590e2344d0b12c2b06e0741c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db69b6db6d36db49249249369a69369b69249249249249249a489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨81, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000560000005c000000", hexnat% "40008300040100800000000", hexnat% "4080000000000000000", hexnat% "c60000000000000000", hexnat% "3000001280000000000", 1906553162563584, 2162516033536]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00143.record008
