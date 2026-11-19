module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00019Data
public import GraphInputsRow16Part00019Frames
public import GraphInputsRow16Part00019Leaves
public import GraphInputsRow16Part00019Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

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
