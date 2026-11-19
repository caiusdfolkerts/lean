module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00019Data
public import GraphInputsRow16Part00019Frames
public import GraphInputsRow16Part00019Leaves
public import GraphInputsRow16Part00019Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record001
def vertexColumn : Fields := ⟨10, hexnat% "b30bcb8aca56ac6a9a36a3a4e338ae4783eb85c9564b9b16a52d4cd2b51d2743db0ea398ce354d3332cab16c3ba1e4731e2729d1743c8f13c2fa914a46a260d81e524c9464a50d48d0754344c3342c4b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db4d26db49a4da49249b6d24d26da492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2312734791243399168, 422212733501440, 1170935903116328960, 210520506368, 9259400833873739776]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [219127218176, 4574002739675136, 2306124484593057792, 1170935903120523264, 9225623836702015488, 189115999977472, 36046389205008384]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record020
def vertexColumn : Fields := ⟨10, hexnat% "26c5a95a4eac6a9a66599564d86e2785e0fb619a56956539b16a599565a55554d64d8b46d2745d0f6c3a8e6358d9354d3352d2b1ad1b26c5b0ee8791d4731e2749ca719d1715c3723c961382e07a85916252544d0b41d50d2344c9312c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6924db6d24d36924936d2492492492492492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "303a4c1a77ff800000", 5531917877248, hexnat% "80002000000000000", 13510798882111488, hexnat% "400000208000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4205238384827826176, 9570149208162304, hexnat% "780000000000000000", 36834176401408, 26869382512640, 4432406249472]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4038763fc7ff800000", 146366987889541120, hexnat% "80000000800000000", 206158430208, hexnat% "300000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5008143fd36e800000", 171815469056, 3485786111584763904, hexnat% "280000000000000000", 144115207671644160, 2814749767106560]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4195702316722028544, 19140298416324608, hexnat% "780000000000000000", 2821793513472, 22436976263168, 8796093022208]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1800063f7b67800000", hexnat% "200008000000000000", hexnat% "400810008008000000", 144115207671644160, 3485786111584763904]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [66461498343424, 4179340471379689472, hexnat% "780000000000800000", 3882650435584, 8444249301319680, 27021597898440704, 7264534528]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record021
def vertexColumn : Fields := ⟨10, hexnat% "d8a6a5a95a4eac6a9a66599564d86e2785e0fb619a56956539b16a599565555351b49d1743dd0ec3c8ea398d63a4d9354d3392d4b8ad2b1ad1b26c5b0ee8791d4731e2749ca719d1715c3723c961382e078951342d0768390d4388d2344c9312c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6da4936db6db6d2492492492492492492492492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [15741673069871104, 270215977642229760, hexnat% "1e00000000000000000", 2272725431222272]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100023f8fff68800000", 126100789566373888, hexnat% "e00000000000000000", 123145369419776, 2466250752]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8003c1f0fbbf800000", hexnat% "1600000000000000000", 6192467741245440, 5497558138880, 9015995347763200, 2253998836940800]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100023fffc76c000000", 240526557184, 126100789566373888, hexnat% "e00000000000000000", 2466250752]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6000e977fb67800000", hexnat% "800100000000000000", 6201245580656640, hexnat% "1000200000008000000", 140757084143616]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [270515603226230784, hexnat% "1e00000000000000000", 211518549393408, 15208444835397632, 20854079488, 2255133245177856, 39655433043968]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record021_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record022
def vertexColumn : Fields := ⟨10, hexnat% "ab13ab1aa699966559362b89e1783ed86a94e6c5a96655965555535a362d2b49d1743db0ea398d634cd2b2ad1b26c5b0ee8791d4731e2749ca719d1725c3713d521588e0b81e54685916251548d0b41d50d2344c5322c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6d34926da49a4d24926da492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81d38061ffe000000", 27487790694400, hexnat% "200080004000000000", hexnat% "40004008000000000", hexnat% "10001002000000000", hexnat% "20002000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000901fe7fe000000", hexnat% "10001000000000000", 2089670261459648512, hexnat% "e0000000000000000", 12384967694745600, 562949953421312]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "304131d7ffe000000", hexnat% "200080000000000000", hexnat% "40004008000000000", hexnat% "80808020000000000", 1224979098644774912, 9007199254740992]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2600a601dffe000000", 30786325577728, 2089670227099910144, hexnat% "90000000000000000", 2336462209024, 7036874417766400]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11d3f1c3ffe000000", hexnat% "200080004000000000", 3848290697216, hexnat% "e0000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2103484628596686848, hexnat% "200080004000000000", 10033043603456, 3940649673949184, hexnat% "f0000000000000000", 2748779069440]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22018f004cfe000000", hexnat% "d0000000000000000", 1161928781170999296, 8383776161792, 26388279066624, 869194732377473024]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000820044fc000000", 31885837205504, hexnat% "f0000000002000000", 17169973579350016, 1224979141594447872, 2886218022912, 864691201469579264]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record023
def vertexColumn : Fields := ⟨10, hexnat% "362aa93ab1aa699966559362b89e1783ed86a94e6c5a9665595554d4ad2745d0f743b0f23a8e6358e534ce8b8ad2b2ad1b26c5b0ee8791d4731e2749ca719d1725c3713d521588e0b81e544552342d0768390d4388d2344c5322c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db4d249b6db69a492492492492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800407ef67fe000000", 2269460719206400, 4503633987108864, 135107988821114880, hexnat% "3c0000000000000000", 549755813888]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8c04646d7ffe000000", 4925812092436480, hexnat% "100080008000000000", hexnat% "200102020000000000", 2269391999729664]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3401a63ffffe000000", 4996180836614144, 2251799813685248, 306244774661193728, hexnat% "880000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20011f5e3ffe000000", hexnat% "100080008000000000", hexnat% "40020200000000000", hexnat% "800400004000000000", 141836999983104, hexnat% "80040000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9804c051dffe000000", 81064793292668928, hexnat% "240000000000000000", 8725724278030336, 15530601742336, 175921860444160]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3001861ff1ce000000", hexnat% "40020200000000000", 306244774929629184, hexnat% "880000000000000000", 6825828314775552, 422213001936896]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8969953264795648, hexnat% "800400004000000000", 36421322670080, 135107988821114880, hexnat% "3c0000000000000000", 549755813888]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [135110191837347840, hexnat% "800400404410000000", hexnat% "3c0000000000000000", 6184752906240, 2269469309140992, 1310622155276288, 5348058917240832]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record023

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record055
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record055
def vertexColumn : Fields := ⟨10, hexnat% "ad25c4eac659a96958b65392e1783eac6594e6c5a9565a56558d4b59354d4b61d1743db0da358e9394d332cd2b46c5b0ee8791d4731d2719e1725c5743c8f0bd4a298361381e52685914a5854351341d50d2328c3342c4b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6da4d26da4d2492692693692492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2013672116364247040, 1407374883553280, hexnat% "a0000004008000000", hexnat% "110000000000000000", 41231686041600, 72709501353984]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "101ae5021be2000000", 111050674405376, hexnat% "10000002010000000", hexnat% "80010004408000000", hexnat% "20102000000000000", 549822922752]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "31be701fffe000000", hexnat% "80010000000000000", hexnat% "100000020000000000", 109951162777600]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11bc7013a76000000", hexnat% "a0000004008000000", hexnat% "100000020180000000", 40132174413824, 70368744177664, 13510816061980672]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10006167fffe000000", hexnat% "80010000000000000", hexnat% "30000000000000000", 1981583836043018240, 1688849860263936]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11bc7003af6000000", 13510816061980672, hexnat% "100000020100000000", hexnat% "a0000004008000000", 41231686041600, 70368744177664]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b0173004cde000000", 6184752906240, hexnat% "100200020020000000", 1729382334219681792, 37154696925806592, 105557411233792]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3004167edfa000000", hexnat% "100200000000000000", hexnat% "80010000000000000", 576460829679943680, 109775240917155840, 1161928703861587968]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1300410028e2000000", hexnat% "80010004408000000", 113253992628224, 549822922752, 1406248983646437376, 576460829612834816, 9570149476597760]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record055_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record055_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record055_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record055_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record055_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record055_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record055_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record055_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record055_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record055

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record053
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "15ab1966a5a565392e2b85e0f959b16a5596955352d2b61d1743db0da358e9394d5352cab46c5b0ee8791d4731d2719e1725c3743c8f13e544a8a61582e07a514a685914a5854550b41d50d2328c5342c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db69a49349a69249a4d2492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 49)]))
 (.branch 2
 (.leaf ([(facetIndex 55), (facetIndex 57)]))
 (.leaf ([(facetIndex 60), (facetIndex 65)]))))
 (.branch 4
 (.leaf ([(facetIndex 67), (facetIndex 69)]))
 (.branch 5
 (.leaf ([(facetIndex 68)]))
 (.leaf ([(facetIndex 70)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "15c6100020082z29;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4, 5]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record053" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record053" 33

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record053" "{\"ridges\":[[11,322],[18,641],[18,644],[36,322],[38,641],[43,322],[44,322],[46,658],[47,322],[49,706],[56,641],[56,644],[57,356],[58,641],[58,644],[59,641],[59,644],[60,344],[67,658],[69,706]],\"owners\":[[11,322,[65,68,70],[36,43,44,47]],[36,322,[70],[11,43,44,47,65,68]],[43,322,[68],[11,36,44,47,65,70]],[44,322,[65,68],[11,36,43,47,70]],[47,322,[65,70],[11,36,43,44,68]],[18,641,[46,49],[38,56,58,59]],[38,641,[],[18,46,49,56,58,59]],[56,641,[49],[18,38,46,58,59]],[58,641,[46,49],[18,38,56,59]],[59,641,[46],[18,38,49,56,58]],[18,644,[67,69],[38,56,58,59]],[56,644,[69],[18,38,58,59,67]],[58,644,[67,69],[18,38,56,59]],[59,644,[67],[18,38,56,58,69]],[46,658,[67],[]],[67,658,[46],[]],[49,706,[69],[]],[69,706,[49],[]],[57,356,[68],[]],[60,344,[70],[]]],\"edges\":[[40,[11,36,43,44,47,55,57,60,65,68,70]],[43,[18,38,46,49,56,58,59,67,69]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record053" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record053\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,16,18,20],[-3,20],[-5,18],[-6,16,18],[-8,16,20],[-2,7,9],[-4],[-11,9],[-13,7,9],[-14,7],[-2,17,19],[-11,19],[-13,17,19],[-14,17],[-7,17],[-17,7],[-9,19],[-19,9],[-12,18],[-15,20],[-7,21],[-9,21],[-10,22],[-16,23],[-17,24],[-19,24],[-18,25],[-20,26],[-23,27],[-22,27],[-21,28],[-21,-27,29],[-26,30],[-25,30],[-24,31],[-24,-30,32],[-28,-32,33],[-29,-31,33],[-33],[1,3,5,6,8,10,12,15,16,18,20],[2,4,7,9,11,13,14,17,19]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":322,\"a\":11,\"owners\":[65,68,70]},{\"tag\":\"mate\",\"ridge\":322,\"a\":36,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":322,\"a\":43,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":322,\"a\":44,\"owners\":[65,68]},{\"tag\":\"mate\",\"ridge\":322,\"a\":47,\"owners\":[65,70]},{\"tag\":\"mate\",\"ridge\":641,\"a\":18,\"owners\":[46,49]},{\"tag\":\"mate\",\"ridge\":641,\"a\":38,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":641,\"a\":56,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":641,\"a\":58,\"owners\":[46,49]},{\"tag\":\"mate\",\"ridge\":641,\"a\":59,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":644,\"a\":18,\"owners\":[67,69]},{\"tag\":\"mate\",\"ridge\":644,\"a\":56,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":644,\"a\":58,\"owners\":[67,69]},{\"tag\":\"mate\",\"ridge\":644,\"a\":59,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":658,\"a\":46,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":658,\"a\":67,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":706,\"a\":49,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":706,\"a\":69,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":356,\"a\":57,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":344,\"a\":60,\"owners\":[70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":46,\"full_literals\":[-7,21]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-9,21]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":55,\"full_literals\":[-10,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-16,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-17,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":69,\"full_literals\":[-19,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":68,\"full_literals\":[-18,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":70,\"full_literals\":[-20,26]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-23,27],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-22,false,27],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-21,false,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-21,-27,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-24,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-24,-30,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-28,-32,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-29,-31,33],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[11,36,43,44,47,55,57,60,65,68,70]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,38,46,49,56,58,59,67,69]}]}"
  "p cnf 33 41\n-1 16 18 20 0\n-3 20 0\n-5 18 0\n-6 16 18 0\n-8 16 20 0\n-2 7 9 0\n-4 0\n-11 9 0\n-13 7 9 0\n-14 7 0\n-2 17 19 0\n-11 19 0\n-13 17 19 0\n-14 17 0\n-7 17 0\n-17 7 0\n-9 19 0\n-19 9 0\n-12 18 0\n-15 20 0\n-7 21 0\n-9 21 0\n-10 22 0\n-16 23 0\n-17 24 0\n-19 24 0\n-18 25 0\n-20 26 0\n-23 27 0\n-22 27 0\n-21 28 0\n-21 -27 29 0\n-26 30 0\n-25 30 0\n-24 31 0\n-24 -30 32 0\n-28 -32 33 0\n-29 -31 33 0\n-33 0\n1 3 5 6 8 10 12 15 16 18 20 0\n2 4 7 9 11 13 14 17 19 0\n"
  "42 2 7 9 11 13 14 17 19 0 7 41 0\n43 7 9 0 6 10 16 8 18 9 42 0\n44 21 0 21 22 43 0\n45 28 0 44 31 0\n46 -32 0 45 39 37 0\n47 -24 0 46 39 44 35 36 38 33 34 32 28 27 29 30 2 20 3 19 24 23 5 1 4 40 0\n48 -17 0 47 25 0\n49 -19 0 47 26 0\n50 -2 0 48 49 11 0\n51 -13 0 48 49 13 0\n52 -14 0 48 14 0\n53 -7 0 48 15 0\n54 -11 0 49 12 0\n55 -9 0 49 17 0\n56 0 51 53 50 54 55 52 48 49 42 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record053

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record054
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "56ac659a969594e4b8ae1783e566c5596959554d4b4ad1743dd0ec3a8da358e9354d4b2ae1b46c5b0ee8791d4731d2719e1725c3743c8f13e524a8a61582e07a514a4a51542d0768390d4348ca384c5342c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db4d249b6d3492492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 58), (facetIndex 60)]))
 (.branch 2
 (.leaf ([(facetIndex 56), (facetIndex 59)]))
 (.leaf ([(facetIndex 61), (facetIndex 66)]))))
 (.branch 4
 (.leaf ([(facetIndex 68), (facetIndex 70)]))
 (.branch 5
 (.leaf ([(facetIndex 69)]))
 (.leaf ([(facetIndex 71)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "ae3080010201z2a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4, 5]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record054" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record054" 34

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record054" "{\"ridges\":[[12,322],[14,641],[14,642],[36,322],[38,641],[44,322],[45,322],[46,641],[46,642],[47,322],[49,641],[49,642],[50,641],[50,642],[51,321],[58,660],[59,356],[60,708],[61,344],[68,660],[70,708]],\"owners\":[[51,321,[56,59,61],[12,36,44,45,47]],[12,322,[66,69,71],[36,44,45,47,51]],[36,322,[71],[12,44,45,47,51,66,69]],[44,322,[69],[12,36,45,47,51,66,71]],[45,322,[66,69],[12,36,44,47,51,71]],[47,322,[66,71],[12,36,44,45,51,69]],[14,641,[58,60],[38,46,49,50]],[38,641,[],[14,46,49,50,58,60]],[46,641,[60],[14,38,49,50,58]],[49,641,[58,60],[14,38,46,50]],[50,641,[58],[14,38,46,49,60]],[14,642,[68,70],[38,46,49,50]],[46,642,[70],[14,38,49,50,68]],[49,642,[68,70],[14,38,46,50]],[50,642,[68],[14,38,46,49,70]],[58,660,[68],[]],[68,660,[58],[]],[59,356,[69],[]],[60,708,[70],[]],[70,708,[60],[]],[61,344,[71],[]]],\"edges\":[[40,[12,36,44,45,47,51,56,59,61,66,69,71]],[43,[14,38,46,49,50,58,60,68,70]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record054" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record054\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,12,14,16],[-1,17,19,21],[-3,21],[-5,19],[-6,17,19],[-8,17,21],[-2,13,15],[-4],[-7,15],[-9,13,15],[-10,13],[-2,18,20],[-7,20],[-9,18,20],[-10,18],[-13,18],[-18,13],[-14,19],[-15,20],[-20,15],[-16,21],[-13,22],[-15,22],[-12,23],[-17,24],[-18,25],[-20,25],[-19,26],[-21,27],[-24,28],[-23,28],[-22,29],[-22,-28,30],[-27,31],[-26,31],[-25,32],[-25,-31,33],[-29,-33,34],[-30,-32,34],[-34],[1,3,5,6,8,11,12,14,16,17,19,21],[2,4,7,9,10,13,15,18,20]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":321,\"a\":51,\"owners\":[56,59,61]},{\"tag\":\"mate\",\"ridge\":322,\"a\":12,\"owners\":[66,69,71]},{\"tag\":\"mate\",\"ridge\":322,\"a\":36,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":322,\"a\":44,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":322,\"a\":45,\"owners\":[66,69]},{\"tag\":\"mate\",\"ridge\":322,\"a\":47,\"owners\":[66,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":14,\"owners\":[58,60]},{\"tag\":\"mate\",\"ridge\":641,\"a\":38,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":641,\"a\":46,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":641,\"a\":49,\"owners\":[58,60]},{\"tag\":\"mate\",\"ridge\":641,\"a\":50,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":642,\"a\":14,\"owners\":[68,70]},{\"tag\":\"mate\",\"ridge\":642,\"a\":46,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":642,\"a\":49,\"owners\":[68,70]},{\"tag\":\"mate\",\"ridge\":642,\"a\":50,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":660,\"a\":58,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":660,\"a\":68,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":356,\"a\":59,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":708,\"a\":60,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":708,\"a\":70,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":344,\"a\":61,\"owners\":[71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":58,\"full_literals\":[-13,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":60,\"full_literals\":[-15,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":56,\"full_literals\":[-12,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-17,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":68,\"full_literals\":[-18,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":70,\"full_literals\":[-20,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":69,\"full_literals\":[-19,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":71,\"full_literals\":[-21,27]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-23,false,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-22,false,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-22,-28,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-31,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-29,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-30,-32,34],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[12,36,44,45,47,51,56,59,61,66,69,71]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[14,38,46,49,50,58,60,68,70]}]}"
  "p cnf 34 42\n-11 12 14 16 0\n-1 17 19 21 0\n-3 21 0\n-5 19 0\n-6 17 19 0\n-8 17 21 0\n-2 13 15 0\n-4 0\n-7 15 0\n-9 13 15 0\n-10 13 0\n-2 18 20 0\n-7 20 0\n-9 18 20 0\n-10 18 0\n-13 18 0\n-18 13 0\n-14 19 0\n-15 20 0\n-20 15 0\n-16 21 0\n-13 22 0\n-15 22 0\n-12 23 0\n-17 24 0\n-18 25 0\n-20 25 0\n-19 26 0\n-21 27 0\n-24 28 0\n-23 28 0\n-22 29 0\n-22 -28 30 0\n-27 31 0\n-26 31 0\n-25 32 0\n-25 -31 33 0\n-29 -33 34 0\n-30 -32 34 0\n-34 0\n1 3 5 6 8 11 12 14 16 17 19 21 0\n2 4 7 9 10 13 15 18 20 0\n"
  "43 2 7 9 10 13 15 18 20 0 8 42 0\n44 13 15 0 7 10 11 17 9 20 43 0\n45 22 0 22 23 44 0\n46 29 0 45 32 0\n47 -33 0 46 40 38 0\n48 -25 0 47 40 45 36 37 39 34 35 33 29 28 30 31 3 21 4 18 25 24 1 6 2 5 41 0\n49 -18 0 48 26 0\n50 -20 0 48 27 0\n51 -2 0 49 50 12 0\n52 -9 0 49 50 14 0\n53 -10 0 49 15 0\n54 -13 0 49 16 0\n55 -7 0 50 13 0\n56 -15 0 50 19 0\n57 0 52 51 55 53 54 56 49 50 43 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00019.record054
