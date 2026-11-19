module
prelude
public meta import CertificateNumbers
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
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
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
def vertexColumn : Fields := ⟨10, (certNat% 2)⟩
def kindColumn : Fields := ⟨3, (certNat% 3)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 5531917877248, (certNat% 5), 13510798882111488, (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4205238384827826176, 9570149208162304, (certNat% 7), 36834176401408, 26869382512640, 4432406249472]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), 146366987889541120, (certNat% 9), 206158430208, (certNat% 10)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 171815469056, 3485786111584763904, (certNat% 12), 144115207671644160, 2814749767106560]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4195702316722028544, 19140298416324608, (certNat% 7), 2821793513472, 22436976263168, 8796093022208]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 15), 144115207671644160, 3485786111584763904]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [66461498343424, 4179340471379689472, (certNat% 16), 3882650435584, 8444249301319680, 27021597898440704, 7264534528]
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
def vertexColumn : Fields := ⟨10, (certNat% 17)⟩
def kindColumn : Fields := ⟨3, (certNat% 18)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [15741673069871104, 270215977642229760, (certNat% 19), 2272725431222272]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 126100789566373888, (certNat% 21), 123145369419776, 2466250752]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), 6192467741245440, 5497558138880, 9015995347763200, 2253998836940800]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 240526557184, 126100789566373888, (certNat% 21), 2466250752]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 6201245580656640, (certNat% 27), 140757084143616]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [270515603226230784, (certNat% 19), 211518549393408, 15208444835397632, 20854079488, 2255133245177856, 39655433043968]
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
def vertexColumn : Fields := ⟨10, (certNat% 28)⟩
def kindColumn : Fields := ⟨3, (certNat% 29)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), 27487790694400, (certNat% 31), (certNat% 32), (certNat% 33), (certNat% 34)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 36), 2089670261459648512, (certNat% 37), 12384967694745600, 562949953421312]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), (certNat% 32), (certNat% 40), 1224979098644774912, 9007199254740992]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), 30786325577728, 2089670227099910144, (certNat% 42), 2336462209024, 7036874417766400]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 31), 3848290697216, (certNat% 37)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2103484628596686848, (certNat% 31), 10033043603456, 3940649673949184, (certNat% 44), 2748779069440]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 46), 1161928781170999296, 8383776161792, 26388279066624, 869194732377473024]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), 31885837205504, (certNat% 48), 17169973579350016, 1224979141594447872, 2886218022912, 864691201469579264]
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
def vertexColumn : Fields := ⟨10, (certNat% 49)⟩
def kindColumn : Fields := ⟨3, (certNat% 50)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), 2269460719206400, 4503633987108864, 135107988821114880, (certNat% 52), 549755813888]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), 4925812092436480, (certNat% 54), (certNat% 55), 2269391999729664]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), 4996180836614144, 2251799813685248, 306244774661193728, (certNat% 57)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), (certNat% 54), (certNat% 59), (certNat% 60), 141836999983104, (certNat% 61)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 81064793292668928, (certNat% 63), 8725724278030336, 15530601742336, 175921860444160]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), (certNat% 59), 306244774929629184, (certNat% 57), 6825828314775552, 422213001936896]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8969953264795648, (certNat% 60), 36421322670080, 135107988821114880, (certNat% 52), 549755813888]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [135110191837347840, (certNat% 65), (certNat% 52), 6184752906240, 2269469309140992, 1310622155276288, 5348058917240832]
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
def vertexColumn : Fields := ⟨10, (certNat% 66)⟩
def kindColumn : Fields := ⟨3, (certNat% 67)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2013672116364247040, 1407374883553280, (certNat% 68), (certNat% 69), 41231686041600, 72709501353984]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), 111050674405376, (certNat% 71), (certNat% 72), (certNat% 73), 549822922752]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 75), (certNat% 76), 109951162777600]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 68), (certNat% 78), 40132174413824, 70368744177664, 13510816061980672]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), (certNat% 75), (certNat% 80), 1981583836043018240, 1688849860263936]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 81), 13510816061980672, (certNat% 82), (certNat% 68), 41231686041600, 70368744177664]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), 6184752906240, (certNat% 84), 1729382334219681792, 37154696925806592, 105557411233792]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), (certNat% 86), (certNat% 75), 576460829679943680, 109775240917155840, 1161928703861587968]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), (certNat% 72), 113253992628224, 549822922752, 1406248983646437376, 576460829612834816, 9570149476597760]
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
