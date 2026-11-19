module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00058Data
public import GraphInputsRow24Part00058Frames
public import GraphInputsRow24Part00058Leaves
public import GraphInputsRow24Part00058Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record014
def vertexColumn : Fields := ⟨10, hexnat% "7c3cb8ab29caaa9aa3a87ae1ac671aa6698e61db0e9394e8b92e1ba1e4785e0f8f1e26c9726a96a4e91e785b15c5a95a539475c364d5362d4b46d8751d1743de0ec370ea368ce334cb31cf0ba2d8b92d4b32e2b4acab1ae1b46f07a1d8791d4731e2749ca719e1745e0f43c4f0bc1f1683a158361643915435a0d8330ca314c3382d0b12c2b06e0741c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6da6db6d36db6da4db6db4db6da6db6db492492492492492492492492492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨72, by decide⟩, ⟨79, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨97, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8100c020000001000000", hexnat% "102018000000000000000000000", 4593671619917905920, 4505523772719104, 274341036032, 4501400604114944, 503316480]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record014_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record021
def vertexColumn : Fields := ⟨10, hexnat% "7ce4acaa6a3a719964da1e4783ee44f1b2699366391e5c5654d54d4758751d17783b0dc338f13a4d938cd332ce8b92ccb8ae1b46c9b0ed8751cc749e1745c970de0f43c1f1b03c1a8661382ea45911a6190e465454351342d0768360cc318e0b12c2b41c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "9b6db6da4da6934d249249349b69249b4924d3492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40006be000002b0000000", 515396075520, hexnat% "900008000000000000", hexnat% "1000004048000000000", 131942469074944, 135107988821114880]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [10368549657176440832, 3458764515968024576, hexnat% "60000000000000000", hexnat% "900008000000000000", hexnat% "401000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60e007ce870000000", hexnat% "900008000000000000", hexnat% "400001000000000000000", 135108057540591616, 11529215054658404352, hexnat% "1000004000080000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80a5ec505240000000", hexnat% "140800040000000000", hexnat% "400021200000000000000", 174751481856, 44530220924928, hexnat% "1000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [423475737085870080, hexnat% "140800000000000000", hexnat% "808004000000000000", hexnat% "400021200000000000000", hexnat% "1000008000280000000", 2305843043573432320]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "162f607cfaf0000000", hexnat% "400001000000000000000", hexnat% "808004000000000000", 38280596832649216, hexnat% "1000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1002174590404788224, 11529215046068469760, hexnat% "400021200000000000000", hexnat% "900000000000000000", hexnat% "400000c8000000000", hexnat% "1000004000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180b50c24aaf0000000", hexnat% "400020200000000000000", 54043539125829632, 96757023244288, 9007199254740992, hexnat% "140800000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "401961fcc6ca2d0000000", 9024860160262144, 309774516224, 11529215046068469760]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "96bf0c2caad0000000", hexnat% "401000000000000000000", 344134254592, 54131156458668032, 9007199254740992]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400163f082ca0d0000000", hexnat% "808004000000000000", 54131156458668032, hexnat% "1000000000200000000", 378493992960, 9007199254740992]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4010485ec34faf0000000", hexnat% "900000000000000000", 79164837199872, 3602879701896396800, hexnat% "20800000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4011405ec7cf2d0000000", hexnat% "808000000000000000", 34896609280, hexnat% "20a00000000000000", 3458764513820540928]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40184850c64e2d0000000", 8796629893120, hexnat% "100800000000000000", 3458764548180279296, 63068055688708096, hexnat% "20200000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c18 c15
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4010617002020c0000000", 63068055688708096, hexnat% "808004000000000000", hexnat% "100008440000000000", 318364450816, 9346117271552, 2882303761517117440]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c22 c9
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c23 c8
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c24 c5
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c25 c4
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c26 c3
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c27 c0
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record021_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record025
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record025
def vertexColumn : Fields := ⟨10, hexnat% "7ce2b1a8e93a1e8e61da8e6386e8791e1783ee46d174789c66394e47939695654d5a358d1b61d4745de0ec370ce3c4e5354e334cc73c2e8b62e2b4ac6b86d1b16c3ba1d8729e1745c570de0f43c8f13c1f1d03c318660b871865190e4c5194550d42d0768360cc318e0b42c2b21c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "9b6da4da6da6db4924da6d249249b6da4924926924da492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "810e93c019b49fc000000", hexnat% "40100100000040000000000", hexnat% "1000000040000000000000", 252307338407444480]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "810e93c01db41ec000000", hexnat% "1100000000000800000000", 252236969931702272, hexnat% "40000100000040000000000", 18014398509481984]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11000927c00639fc000000", 272678883688448, hexnat% "40810000000000000000000", hexnat% "100001004000000000", hexnat% "e01800010000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "810e93c01bb49ec000000", hexnat% "1100000000000000000000", 252272154303791104, hexnat% "40000100000040000000000", 18014398509481984]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9240003090c000000", hexnat% "1900000000000000000000", 270216183800659968, hexnat% "f01800004000000000", hexnat% "40010000000000080000000", 285873023221760, 272680762736640]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record025_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record025_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record025_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record025_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record025_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record025_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record025_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record025_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record025_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record025
