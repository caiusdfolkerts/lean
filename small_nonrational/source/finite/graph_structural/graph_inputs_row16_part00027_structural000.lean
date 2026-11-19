module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00027Data
public import GraphInputsRow16Part00027Frames
public import GraphInputsRow16Part00027Leaves
public import GraphInputsRow16Part00027Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record022
def vertexColumn : Fields := ⟨10, hexnat% "26c8f17272a6a6695a1ea6665a4e8b86e2783e5c5c99a599566391e66565635a364d8b46d8749d0f5c398d6364d534cc7362e4b52ccb8ac6b46c9b16c3b61e4789ca719d1725e0f13c2f0d88e07a61926250d60d2341d60d4318d130cc8b12c1b21c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6db49b4db69a49349249249249a4924d2492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c81ae201527400000", 306244774803800064, 2201439174656, 212755499974656, 30829275250688, 281749854617600]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "805ee43df3bc00000", 9223512774343131136, hexnat% "40000000004000000", 334253682327552, 13194139533312]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c80263c5f0fc00000", 283676147449856, 212755499974656, 56294995342131200, 360287970726510592, 268435456]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800077bdf87c00000", hexnat% "48020000000000000", 56294995342131200, 4398986035200, 288371113640067072, 72057594037927936]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [370100695874928640, 1374406311936, 318860519538688, hexnat% "48000000000000000", 57420895248973824, hexnat% "80000000002000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [66995464003649536, hexnat% "c0000000002400000", 360287970860728320, 9223513942574235648, 2201439174656, 343082054713344, 71201967833088]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record028
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record028
def vertexColumn : Fields := ⟨10, hexnat% "26c8f1ca9a87a999666598e9394e8b86e2783e726698e479d1665595958d58d9354d8b46d8749d0f5c398d6364cb31cd8b92d4b32e2b1ac5b0ed8791d4789d2719d1725e0f43c8f13c2f2683607a6192499894358341d60d4318c930cc8b12c1b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6db49a6da6d34d34924924924d249a492492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800057fbd1fc00000", hexnat% "11000800000000000", 47287796087390208, hexnat% "40002000000000000", 144115191833952256]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c0007301dffc00000", 6047313952768, 155374187144282112, 220039764508672, hexnat% "11080000000000000", 2199023255552]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8108f67bd7fc00000", 26388279066624, 153122389478080512, hexnat% "50000000000000000", 140737488355328]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1190495379515244544, 2748862955520, 155937137097703424, hexnat% "c0000000000000000", hexnat% "10000800000000000", 2147483648]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1191597639871758336, 26388413284352, hexnat% "10000800000000000", 153685339431501824, hexnat% "80004000000000000", hexnat% "40000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d022f05bdffc00000", 52776558133248, 1188950301625810944, 213305255788544, 8796093022208]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d002f05bdffc00000", 52776558133248, 1297036692682702848, 36030996042219520, 219902325555200]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000b359dffc00000", hexnat% "80004000000000000", 1306043891937443840, 213442694742016, hexnat% "10080000000000000", 8796093022208]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11280db39f2c00000", 321607151124480, 11821949088956416, hexnat% "c0000000008000000", 1125917103489024]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [421908591935488, hexnat% "80004000400000000", hexnat% "11000800000000000", 47287796087390208, 144115191297081344, hexnat% "40002000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [560467374243840, hexnat% "10080020000000000", 1306043891937443840, hexnat% "c0000000000000000", 3940649741058048, 16777216]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [144533646735310848, hexnat% "80004000800000000", 144173462192128, 47287796087390208, hexnat% "11000000000000000", hexnat% "40002000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "51223cbb9f3c00000", 57174738862080, 38280596899758080, hexnat% "80004000400000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [66732962086912, 352960412385280, hexnat% "110a0000000000000", 144678140180955136, hexnat% "c0000000800000000", 142936578719744, 3377699737305088]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c21 c10
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c22 c5
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c23 c4
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c24 c1
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c25 c0
  c26
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record028_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record028_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record028_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record028_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record028_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record028_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record028_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record028_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record028_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record028

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record040
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record040
def vertexColumn : Fields := ⟨10, hexnat% "9b23c9a99a71a662da4e8b86e1783ed266966639716658d4b59362d1b61d1743d70e6364cb362e4b8ad2b1ad1b26c5b61e4751cc789ca719c5783c4f0bc1f5283a25836925498a439916252543560d4324c3342c4b0ac1b21c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db4db69269a4926da4d2492492492492692249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "811c0108ff7000000", 2314854606514946048, 184992831373312, 293017649779048448, 4611686018427387904, 1305670057984]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2306054094894137344, hexnat% "84000000000000000", 1445655480385929216, 81064810472538112, 54324672652640256, 1073741824]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80040b01ff7000000", 10857677324288, 3467776111121793024, 112589990684262400, 4611967493404098560, 288232575174967296]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3467982755537616896, 44291850240, 329044247774756864, hexnat% "84000000000000000", 72057613365280768, 18014398509481984]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3539836831694585856, 184752313204736, hexnat% "80040100001000000", 329044247808311296, 4611686018427387904, 1236950581248]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84031bcff77000000", 3458764513820540928, 54043197675929600, 288233674686595072, 72057594037927936]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8703114d727000000", 184752313204736, 18014401999142912, 108086391056891904, 288233674686595072, 137438953472]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8079462495158272000, hexnat% "80040100051000000", 184752313204736, 112589992831746048, 558412857344, 1236950581248, 288514050185232384]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record040_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record040_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record040_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record040_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record040_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record040_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record040_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record040_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record040_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record040
