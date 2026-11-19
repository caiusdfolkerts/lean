module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00022Data
public import GraphInputsRow16Part00022Frames
public import GraphInputsRow16Part00022Leaves
public import GraphInputsRow16Part00022Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00022.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record006
def vertexColumn : Fields := ⟨10, hexnat% "b329c9713c4eac6a5a564d8ce4b91e2785e0fac9a66594e6c5a56558d535a364d3352d8751d2745d0f6c3a4e5362d4b32d2b26c5b0ee8791cc749ca719e1745c9715d0f0bd32468362384e0793146685916150d48d1341d48d130cd0b22c4b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6d36d26924db4924924d24936d2492492492492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10043be3ff018000000", 63887638528, 4035225270418931712, hexnat% "20088000000000000000", hexnat% "700000000000000000", hexnat% "2000400000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [36098616409980928, hexnat% "20088002000080000000", hexnat% "1700000000000000000", hexnat% "2000410000800000000", 8295630513616453632, 512711720960, 579838452023951360]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00022.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00022.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record008
def vertexColumn : Fields := ⟨10, hexnat% "4f2caa6a5a4eac6a5a564d8ce4b8ae1b91e2785e0fac9a66594e6c5a56554d4cd4b4ad1b51d2745d0f6c3c4e9394d33a2e4b32d2b2ac6b86d1b26c5b0ee8761e4751cc729c6785c9715c3743d264588e1382e079254548d1342d0768390d2384d1322c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db4924924db6db492492492492492492492492492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9187343239970029568, hexnat% "80808004008010000000", hexnat% "7f000000000000000000", 33785795445784576, 547071459328, 271579372060672, 844424930131968]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00022.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00022.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record023
def vertexColumn : Fields := ⟨10, hexnat% "2b4ac8daa9966a5a362d94e1b91eb86b1366a5596958d4b55346d8751d70ea358e9334e332cccb1ad1b26c5ba1d4789d2729c6785d1725c3713c2f3894a4381ea84e1a4549896154341d50cc328c6324d0b12c1b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db69a49a6934d24924d2492692492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5550936713301327872, 1153203254461464576, 9002385670144, 27584548254515200, 17592186044416]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [964011254165274624, 844425735438336, 12901679104, 35802880933888, 4613938110298849280, 1152921504606846976]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [964433811066585088, 12901679104, 176488796127232, 2533274790395904, 5764607523034234880]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [100024170489839616, 864691128455135232, 5764607523034234880, 176488796127232, 2251799813685248]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [27614726271795200, 176488796127232, 4613937818241073152, 1153202979600334848, 6442450944, 936819091237240832]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [936821428773191680, 4613938110332403712, 1153202979868770304, 18031991366615040, 186435940384768, 9570149275271168, 15032385536]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00022.record023

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00022.record028
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record028
def vertexColumn : Fields := ⟨10, hexnat% "ab15c3caaa56aa655a8e53a2e2b91e178f1b25c9aa559a95558d535c368d5362d2b51d176a338d5334cb31ce8b52e2b2ad1b16e8751e2729d1715e0f43c8f13c2f07cca0daa154689524c9895150d60d434c328c530cc8b12c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db49249249269a4924934d3692492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [760009281333362688, 360850920143060992, 9288675305193472, 3848424914944, 22588367149465600, 4398046511104]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [381124171068866560, 721701840286121984, 4573968639983616, 10445897334784, 45317472324157440, 17592186044416]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [770416013901561856, 11553462026240, 3377699754082304, 360851057582014464, 18018796958646272, 70368744177664]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [68125201335844864, 360288107628593152, 26697516711936, 2322168658526208, 721701840286121984, 281474976710656]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [124201393964711936, 18018796555993088, 288793463544086528, 12128987643904, 721702115164028928, 17592186044416]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [765923409457577984, 4956392259584, 3377699821191168, 22588367149465600, 360851057582014464]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [97467489748779008, 864691403333042176, 9288674235645952, 10445897334784, 180161577280864256, 1125899906842624]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [760362079740755968, 9007199527370752, 22517998136852480, 360851057582014464, 7155415515136]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [104786388831961088, 288793326105133056, 720576215257186304, 27488327565312, 2533274861699072, 36028797018963968]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [23718700697780224, 720576215257186304, 11553462026240, 2533274895253504, 45035996810575872, 360851057582014464, 18691697672192]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record028_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record028_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record028_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record028_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record028_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record028_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record028_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record028_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record028_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00022.record028
