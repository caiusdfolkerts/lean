module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00016Data
public import GraphInputsRow24Part00016Frames
public import GraphInputsRow24Part00016Leaves
public import GraphInputsRow24Part00016Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00016.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015
def vertexColumn : Fields := ⟨10, hexnat% "1b8373c26c9ca6a99a3693a2eb26358ce4b86e2785e0fbc16c749725a9664d94e4b9c94d5c364d3352d1b49d17783d0ec370f2368d9334d332cd8b52ccb4acab1ad1b26c5b0ef0731e2749c6785c9715d0f23c4f0bc1f0f2460d9893252926439914351342d0770360e4330d2324c3381c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6db6db4db49249b69249249249249a4db4d2492493692249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8cc1bfed8ba47000000", hexnat% "200001000000000000", hexnat% "102400000000000000", 4611686023259226112, 19327352832]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8011fed09fe0000000", hexnat% "740000000000000000", hexnat% "8000000082007000000", 7638104968020361216, hexnat% "80001000000000000", 288230376151711744]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2801bd8837c2000000", hexnat% "441000000000000000", hexnat% "8000000508005000000", 7638104968020361216, 18577383359512576, hexnat% "900400000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "86c1b7fd8ba47000000", hexnat% "800080000000000000", hexnat% "102400000000000000", 4611686023259226112, 19327352832]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2811ffd09cc0000000", hexnat% "d40000000000000000", hexnat% "8000000082007000000", 7638104968020361216, 13421772800, 288230376151711744]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1296342074634797056, 7638104968087470080, hexnat% "6c0000000000000000", hexnat% "8000000508001000000", 562951027163136, hexnat% "900400000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5c1bffd8be62000000", hexnat% "8000000000005000000", 4611686022722355200, hexnat% "a02400000000000000", 2147483648]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1013ffd09e60000000", 7493989780011614208, hexnat% "e40000000000000000", hexnat% "8000000082003000000", 6442450944, hexnat% "80400000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [141582050304983040, 7638104968020361216, hexnat% "440008800000000000", hexnat% "800000058a000000000", hexnat% "81000000000000000", hexnat% "b00400000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fc7ea758a627000000", hexnat% "8000000000000000000", 18014437164187648, 140740709580800, 78813062198460416]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fc7e27000627000000", 41875931136, hexnat% "800000058a000000000", 2392537302040576, 112590059403739136, 18014398509481984]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [269934597154799616, 7493989780011614208, 18014437701058560, hexnat% "4c1000000000000000", hexnat% "800000058a003000000", 140740709580800, hexnat% "b00400000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c18 c7
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c21 c2
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00016.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00016.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022
def vertexColumn : Fields := ⟨10, hexnat% "3c23cb8ab2a5a368bad19c6698e61db0e63a4e338ae17bc13c789b2659364b9d15c5694e51d70d6364d334ad17783d0ec370da338e5334cb31cf0ba2d8b92ccb8ae1b26c5bc1d8791d4731d2729c6745e0f43c8f13c3c2a83a158360b81e2a439154350b41dc0d8390cc328c530ce0b22c2b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db69b6d36da4db6da6db4db692492492492492492492492491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨67, by decide⟩, ⟨72, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨85, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40001082ff9cce620000000", hexnat% "2080000000000000000000", hexnat% "100004000200840000000", 1706448488759296, 1152924871861207040]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20010857fb69ac40000000", hexnat% "40100000000000000000000", hexnat% "80002000040220000000", 2549063090176, 577744981884665856]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800028a7fed7e0000000", hexnat% "2000080008000000000000", hexnat% "40001000010000000000000", 450360100176003072, 1224980198156402688, hexnat% "100004000000800000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000050a73bffe0000000", hexnat% "2000080008000000000000", hexnat% "40001000010000000000000", 504473527009673216, 594615888301260800, hexnat% "80002000040000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10057b77b29c0000000", hexnat% "40100000000000000000000", 594475975446626304, 95026151424, hexnat% "2000080008000000000000", hexnat% "80002000840000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000800a9000780000000", hexnat% "40001000010280000000000", hexnat% "80002000c40020000000", hexnat% "100004000012840000000", 578167194349731840, 1224981366387507200, 450360787370770432]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00016.record022
