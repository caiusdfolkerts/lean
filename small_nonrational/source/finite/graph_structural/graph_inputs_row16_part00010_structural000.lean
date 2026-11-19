module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00010Data
public import GraphInputsRow16Part00010Frames
public import GraphInputsRow16Part00010Leaves
public import GraphInputsRow16Part00010Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record008
def vertexColumn : Fields := ⟨10, hexnat% "3621e9c6c99663995635876c3a2e2783ed847971725594e5554d51d70d8b49d0f74370f2398d6338d531cf0b1ae1b26c5b0ef0761d4731e2749ca719d1715c3783d0f23cd28a8960b81e346292542d0770350cc388c6324c5382c2b06d0721c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db4da49b6db69b492492492492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80041ff8fff6000000", 7696715612160, hexnat% "80040000000000000", 45035996273704960, hexnat% "140000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9007199221186560, hexnat% "100080000000000000", hexnat% "800400000000000000", 27021597764222976, hexnat% "c0000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10008289fffe000000", hexnat% "800400020000000000", 1147890139398144, 7142427534032896, hexnat% "80040000000000000", hexnat% "40020000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10009ff8c798000000", 7697118265344, hexnat% "40020000006000000", hexnat% "800400001800000000", hexnat% "80040000040000000", 137438953472]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8004020209a0000000", hexnat% "100080088408000000", hexnat% "80040000052000000", 1147890139398144, hexnat% "40020200000000000", 2745480534556672, 4504089320751104]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record029
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record029
def vertexColumn : Fields := ⟨10, hexnat% "d8b529c8eac9966c59568d876538ae1b89e17b61d46713a72559715556351d54d2b46d2745dd0f23a8e6358ce3c4e5354e331cd4b32cab1ae1b26f0761d4789d2719e1745c9715c3743c4f0bc5a2988e078592948d0770350e2328c6384c5322c4b06d0721c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6da6936db6db6d3492492492492492492492492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200043ffedff800000", hexnat% "400080000000000000", 13510867601588224, hexnat% "1000200000000000000", 3377708310462464]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20005f3fefbf800000", hexnat% "1000200000000000000", 9148005462573056, hexnat% "400080000000000000", 70369817919488]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2002f2ac9dbf800000", hexnat% "1400000000000000000", 2611340115968, 87962003963904, 3660282798800896]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200040006489000000", hexnat% "1000200010810800000", hexnat% "400080000002000000", 895552220823552, 8039637612232704, 9007272806055936, 70369885028352]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record029_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record029_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record029_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record029_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record029_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record029_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record029_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record029_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record029_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record029
