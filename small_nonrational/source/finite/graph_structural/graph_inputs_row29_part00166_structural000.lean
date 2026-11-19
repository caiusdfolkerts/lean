module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00166Data
public import GraphInputsRow29Part00166Frames
public import GraphInputsRow29Part00166Leaves
public import GraphInputsRow29Part00166Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00166.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00166.record002
def vertexColumn : Fields := ⟨10, hexnat% "ba2b83e2e4ad0f4b32ac9b0eca70dc8f0bc1f2e2ac8f2b2aaa9a8eaa68da8e8ba1ea668d9361db0e9394e8b86e8785e0f8f1aa4e9664d92e479a94e5355352d475a354d3362d2b46d2745d0f6a338cd34ccb31ce8b52ccb8acab1ac9b16c3b51e2749c5783c2f4711a89866458368390e1381e384b13251926465454354344d0746344c3342c4b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db6db6db6db69249249249a49369a49a4da4934d24d26d2492492249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "914c159e0b1a700000000", hexnat% "1040008020000000000", 9224216736662814720, hexnat% "7000000000001800000000", hexnat% "6e8000000000000000000", hexnat% "200000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10c9a1d1e3034d00000000", hexnat% "4040008800000000000", hexnat% "100000000202200000000", hexnat% "400800108000000000", hexnat% "630000000000000000000", hexnat% "6800000000001000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "78c9a1c1e3a3ff00000000", hexnat% "4040008000000000000", 1729399849096314880, hexnat% "10400000000000000000", hexnat% "720000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8dde5d9ebb3dd00000000", hexnat% "100000000002200000000", hexnat% "7000000000000000000000", hexnat% "620000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10c9a1c1e3a3dd00000000", hexnat% "4040008000000000000", hexnat% "100001000002200000000", hexnat% "400800100000000000", hexnat% "630000000000000000000", hexnat% "6800000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18dd65c96b92ff00000000", hexnat% "800080010000000000", hexnat% "6000000000000000000000", hexnat% "100001000200000000000", hexnat% "620000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "185de141e283ff00000000", hexnat% "6080000000000000000000", hexnat% "40008000000000000", hexnat% "720000000000000000000", 1729435033468403712, 9223653511831486464]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8dde4c9ebb3c700000000", hexnat% "100001000002000000000", hexnat% "1000010000000800000000", hexnat% "620000000000000000000", hexnat% "6000000000001000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "814e1c8e3b3c700000000", 1224979236083728384, hexnat% "1040008000000000000", hexnat% "7000000000001800000000", hexnat% "7e8000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "181445c16b80dd00000000", hexnat% "a00080010000000000", hexnat% "100001000202200000000", hexnat% "1000800120000000000", hexnat% "60c8000000000000000000", hexnat% "620000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e040e001c400000000", hexnat% "18003000000000000", hexnat% "100001000202300000000", hexnat% "4040008800000000000", hexnat% "6f8000000000000000000", hexnat% "1000900120000000000", hexnat% "7800000000001800000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00166.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00166.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00166.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00166.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00166.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00166.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00166.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00166.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00166.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00166.record002
