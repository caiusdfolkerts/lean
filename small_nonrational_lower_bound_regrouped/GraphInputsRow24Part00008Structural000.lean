module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00008Data
public import GraphInputsRow24Part00008Frames
public import GraphInputsRow24Part00008Leaves
public import GraphInputsRow24Part00008Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00008.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record008
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 35465847065542656, (certNat% 3), 1044835113549955072, (certNat% 4), 70368744177664]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 1801439850956587008, (certNat% 6), (certNat% 7), 54975598166016, 140737488355328]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), 2990390152574009344, 5764607523034234880, 34339947158700032, 55113020342272, 13194139533312]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 22526794229874688, (certNat% 3), 844975222816768, 612489549334970368, 4398046511104]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), 684547143360315392]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 15530601742336, 11601272640106397696, 34902897112121344, 1765411053929234432, 140737488355328]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 35465847065542656, (certNat% 15), (certNat% 16), 576460752303423488, 140737488355328]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 2918332558552858624, (certNat% 3), (certNat% 18), 15393171177472]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), 1971974104416256, (certNat% 21), 31569177856704512]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), 1971974104416256, 2297979302051840, 31525197391593472, 4398046511104]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), (certNat% 6), 20971520, 1408474395181056]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), 3848290697216, 33785793298300928, (certNat% 27), 468374361246531584, 562949953421312]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), 2199048421376, 1690499127705600, 15806579160907776]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 3), 1971974104416256, 2199052615680, 33820977670389760, 468374361246531584]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c19 c8
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c20 c7
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c21 c6
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c22 c3
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c23 c2
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c24 c1
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c25 c0
  c26
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00008.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00008.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record023
def vertexColumn : Fields := ⟨10, (certNat% 31)⟩
def kindColumn : Fields := ⟨3, (certNat% 32)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 27006754357248, (certNat% 34), 2684354560, 4294967296]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 36), 17725128704, 62124554452992, (certNat% 37), 68719476736]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2319415990577790976, 1747396655419752448, 481036337152, (certNat% 37), 327214660426137600, (certNat% 38)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), 26390694985728, (certNat% 34), 584115552256, 2199023255552]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 8830456954880, 331155310100086784, 17594601963520, 1747396659714719744, 35734127902720]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), 1619001344, 4503616807239680, 1215971899390033920, 576460752303423488]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), 1082130432, 1202461100507922432, 85903540224]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), 52776558133248, (certNat% 44), 1215971899390033920, 4294967296]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), 40532397720076288, (certNat% 46), 17592999739392, 1179943106666037248, 576460752303423488]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 48), 51543801856, 1729382261205237760, 9007199254740992]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 50), 1454662679640670208, 576460752303423488, 17179869184]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), 1879048192, 1454662679640670208, 6442450944]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 48), 1450159080013299712, 576495943117963264]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 54), 1887436800, 1166432303488958464]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), (certNat% 56), (certNat% 57), 292733976852824064, 1161928708156555264, 576460754987778048]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c21 c16
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c22 c15
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c23 c14
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), 324822124197838848, 26390694985728, 2392537302040576, 576495940970479616, 1179943102371069952]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), (certNat% 60), 1879048192, 240518168576]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 62), 138512695296, (certNat% 44), 17595138834432, 9448928051200]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), 1747396659714719744, (certNat% 64), 9448928051200, (certNat% 65), 17594333528064]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), (certNat% 34), 1879048192, 18014404951932928, 329325722751467520, 1161928703861587968]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), 1179943106666037248, (certNat% 37), 17595138834432, 44530220924928, 576460752303423488]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), 1887436800, (certNat% 69), 1215971899390033920, 2310346608841064448, 288230376151711744]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), 17592731303936, 328762773871788032, (certNat% 71), (certNat% 72)]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), 1747396655419752448, (certNat% 71), 328762773871788032, (certNat% 48), 9007199254740992]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 71), 137443147776, 1350565888, 337769972052787200]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), (certNat% 64), 8830456954880, 1887436800, (certNat% 44), 18014400656965632, 1490691476659634176]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c36 c35
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c37 c34
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c38 c33
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c39 c32
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c40 c31
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c41 c30
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c42 c29
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c43 c28
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c44 c25
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c45 c24
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c46 c13
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c47 c6
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c48 c3
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c49 c2
  c50
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00008.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00008.record023
