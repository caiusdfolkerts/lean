module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00058Data
public import GraphInputsRow24Part00058Frames
public import GraphInputsRow24Part00058Leaves
public import GraphInputsRow24Part00058Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

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

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "670dc1f07ae1a96658d61da2e4b86e4785e0fae17259936479e16a539695654d51d58d3362d4b46d4749d1743de0ec370e63a4d9334c7352e2b4ad1b0ef07a1d8731d2719e1745c9715c3783c4f1a85a8990e0b81e3446916685616252550d0b41d88c6314d0b12c2b06e0741c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b69b6da4924db49269269a49249b69b49249249a492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 52), (facetIndex 74)]))
 (.leaf ([(facetIndex 37), (facetIndex 61), (facetIndex 63), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 88)]))
 (.leaf ([(facetIndex 81), (facetIndex 82)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 87)]))
 (.leaf ([(facetIndex 48), (facetIndex 89)])))
 (.branch 7
 (.leaf ([(facetIndex 49), (facetIndex 51), (facetIndex 53), (facetIndex 83)]))
 (.leaf ([(facetIndex 84), (facetIndex 85)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2a83fcd8000012000200208000030c35000000008z1b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4, 5]
def grouped3_0009 : List Nat := [4, 5, 6, 7]
def grouped3_0010 : List Nat := [6]
def grouped3_0011 : List Nat := [6, 7]
def grouped3_0012 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record000" 38

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record000" "{\"ridges\":[[18,644],[21,193],[21,208],[37,198],[39,644],[47,193],[47,208],[51,450],[52,706],[61,204],[63,116],[64,208],[66,644],[67,228],[68,644],[69,644],[71,193],[71,208],[73,456],[74,736],[82,198],[88,204]],\"owners\":[[18,644,[84,85],[39,66,68,69]],[39,644,[],[18,66,68,69,84,85]],[66,644,[85],[18,39,68,69,84]],[68,644,[84,85],[18,39,66,69]],[69,644,[84],[18,39,66,68,85]],[21,193,[37,51,52,61,67,73,74],[47,64,71]],[47,193,[61,67,73,74],[21,37,51,52,64,71]],[71,193,[37,51,52,67,74],[21,47,61,64,73]],[21,208,[82,88],[47,64,71]],[47,208,[88],[21,64,71,82]],[64,208,[],[21,47,71,82,88]],[71,208,[82],[21,47,64,88]],[37,198,[82],[]],[82,198,[37],[]],[51,450,[],[]],[52,706,[],[]],[61,204,[88],[]],[88,204,[61],[]],[63,116,[81,87],[]],[67,228,[],[]],[73,456,[],[]],[74,736,[],[]]],\"edges\":[[39,[21,37,47,51,52,61,64,67,71,73,74,82,88]],[43,[18,39,49,52,53,66,68,69,74,84,85]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-24,-3],[-24,-10],[-1,22,23],[-4],[-13,23],[-15,22,23],[-16,22],[-2,3,7,8,10,14,18,19],[-5,10,14,18,19],[-17,3,7,8,14,19],[-2,21,25],[-5,25],[-12],[-17,21],[-3,21],[-21,3],[-7],[-8],[-10,25],[-25,10],[-11,20,24],[-14],[-18],[-19],[-26,8,19],[-27,3,10,11,14],[-3,27],[-10,27],[-25,28],[-20,29],[-21,29],[-6,30],[-9,30],[-22,31],[-23,31],[-32,26,27],[-27,32],[-29,33],[-28,33],[-34,32,33],[-33,34],[-32,34],[-32,-33,35],[-31,36],[-30,36],[-36,37],[-35,-37,38],[-38],[2,3,5,7,8,10,12,14,17,18,19,21,25],[1,4,6,8,9,13,15,16,19,22,23]],\"atoms\":[{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":87,\"b\":37},{\"tag\":\"incompatible\",\"a\":87,\"b\":61},{\"tag\":\"mate\",\"ridge\":644,\"a\":18,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":644,\"a\":39,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":644,\"a\":66,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":644,\"a\":68,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":644,\"a\":69,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":193,\"a\":21,\"owners\":[37,51,52,61,67,73,74]},{\"tag\":\"mate\",\"ridge\":193,\"a\":47,\"owners\":[61,67,73,74]},{\"tag\":\"mate\",\"ridge\":193,\"a\":71,\"owners\":[37,51,52,67,74]},{\"tag\":\"mate\",\"ridge\":208,\"a\":21,\"owners\":[82,88]},{\"tag\":\"mate\",\"ridge\":208,\"a\":47,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":208,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":208,\"a\":71,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":198,\"a\":37,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":198,\"a\":82,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":450,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":706,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":204,\"a\":61,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":204,\"a\":88,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":116,\"a\":63,\"owners\":[81,87]},{\"tag\":\"mate\",\"ridge\":228,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":456,\"a\":73,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":74,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[52,74],\"full_literals\":[-26,8,19]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[37,61,63,67],\"full_literals\":[-27,3,10,11,14]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":37,\"full_literals\":[-3,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":61,\"full_literals\":[-10,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":88,\"full_literals\":[-25,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":81,\"full_literals\":[-20,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-21,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":49,\"full_literals\":[-6,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":53,\"full_literals\":[-9,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-22,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":85,\"full_literals\":[-23,31]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-32,26,27],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-34,32,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-33,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-30,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-35,-37,38],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[21,37,47,51,52,61,64,67,71,73,74,82,88]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,39,49,52,53,66,68,69,74,84,85]}]}"
  "p cnf 38 50\n-24 -3 0\n-24 -10 0\n-1 22 23 0\n-4 0\n-13 23 0\n-15 22 23 0\n-16 22 0\n-2 3 7 8 10 14 18 19 0\n-5 10 14 18 19 0\n-17 3 7 8 14 19 0\n-2 21 25 0\n-5 25 0\n-12 0\n-17 21 0\n-3 21 0\n-21 3 0\n-7 0\n-8 0\n-10 25 0\n-25 10 0\n-11 20 24 0\n-14 0\n-18 0\n-19 0\n-26 8 19 0\n-27 3 10 11 14 0\n-3 27 0\n-10 27 0\n-25 28 0\n-20 29 0\n-21 29 0\n-6 30 0\n-9 30 0\n-22 31 0\n-23 31 0\n-32 26 27 0\n-27 32 0\n-29 33 0\n-28 33 0\n-34 32 33 0\n-33 34 0\n-32 34 0\n-32 -33 35 0\n-31 36 0\n-30 36 0\n-36 37 0\n-35 -37 38 0\n-38 0\n2 3 5 7 8 10 12 14 17 18 19 21 25 0\n1 4 6 8 9 13 15 16 19 22 23 0\n"
  "51 -26 0 18 24 25 0\n52 -27 3 10 11 0 22 26 0\n53 -32 27 0 51 36 0\n54 2 3 5 10 17 21 25 0 17 18 13 22 23 24 49 0\n55 1 6 9 13 15 16 22 23 0 4 18 24 50 0\n56 34 0 41 42 38 39 37 31 29 27 28 14 12 11 54 0\n57 33 24 0 56 38 39 40 30 31 29 53 21 15 19 52 0\n58 27 0 24 23 22 18 17 27 28 10 16 9 20 8 54 0\n59 32 0 58 37 0\n60 33 0 38 39 57 31 29 1 2 14 12 11 54 0\n61 35 0 60 59 43 0\n62 -37 0 61 48 47 0\n63 -36 0 62 46 0\n64 -31 0 63 44 0\n65 -30 0 63 45 0\n66 -22 0 64 34 0\n67 -23 0 64 35 0\n68 -6 0 65 32 0\n69 -9 0 65 33 0\n70 -1 0 66 67 3 0\n71 -15 0 66 67 6 0\n72 -16 0 66 7 0\n73 -13 0 67 5 0\n74 0 69 73 70 68 71 72 66 67 55 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3707c7287ae1a361da8e638ce1b91e1783eb85c936479e16a5394d58d475a34cd1b51d2745d0f783b0dc398e33a2d8b52ccb1ad1b0ef07a1d8731d2719e1745c5783c8f13c2f6307216a260d90e07871624c916685616250d50d2341d88c6314c3342c4b06e0741c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b69a4d369269249b4926924db49a492492692492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 37), (facetIndex 43), (facetIndex 45), (facetIndex 50), (facetIndex 51)]))
 (.leaf ([(facetIndex 41), (facetIndex 61), (facetIndex 66), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 32), (facetIndex 58), (facetIndex 74), (facetIndex 77)]))
 (.leaf ([(facetIndex 57), (facetIndex 60), (facetIndex 69), (facetIndex 70)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 36), (facetIndex 38), (facetIndex 63), (facetIndex 80)]))
 (.leaf ([(facetIndex 34), (facetIndex 55), (facetIndex 68), (facetIndex 72), (facetIndex 82)])))
 (.branch 7
 (.leaf ([(facetIndex 31), (facetIndex 56), (facetIndex 62), (facetIndex 73), (facetIndex 79)]))
 (.branch 8
 (.leaf ([(facetIndex 44), (facetIndex 46), (facetIndex 47), (facetIndex 48)]))
 (.leaf ([(facetIndex 33), (facetIndex 35), (facetIndex 40), (facetIndex 42)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5046020026503351100461302365000000777070818040485826z1f;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 53), (facetIndex 71)]))
 (.branch 2
 (.leaf ([(facetIndex 39), (facetIndex 59), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 85)]))))
 (.branch 4
 (.leaf ([(facetIndex 84)]))
 (.branch 5
 (.leaf ([(facetIndex 49), (facetIndex 52), (facetIndex 54)]))
 (.leaf ([(facetIndex 78), (facetIndex 81), (facetIndex 83)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "13a281424000000090002001040200000002z1d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7, 8]
def grouped2_0010 : List Nat := [7, 8]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1, 2]
def grouped3_0014 : List Nat := [1]
def grouped3_0015 : List Nat := [1, 2]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [3]
def grouped3_0018 : List Nat := [3, 4, 5]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record001" 43

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record001" "{\"ridges\":[[18,641],[20,200],[39,198],[41,644],[46,200],[52,450],[53,706],[60,200],[61,641],[64,212],[65,228],[66,641],[67,641],[69,200],[70,200],[71,736],[85,212]],\"owners\":[[18,641,[49,53,54,71],[41,61,66,67]],[61,641,[53,54,71],[18,41,49,66,67]],[66,641,[49,53,54],[18,41,61,67,71]],[67,641,[49,53,71],[18,41,54,61,66]],[41,644,[],[18,61,66,67,78,81]],[20,200,[76,83,85],[46,60,69,70]],[46,200,[85],[20,60,69,70,76,83]],[60,200,[83],[20,46,69,70,76,85]],[69,200,[76,83],[20,46,60,70,85]],[70,200,[76,85],[20,46,60,69,83]],[39,198,[76],[]],[52,450,[83],[]],[53,706,[],[]],[64,212,[85],[]],[85,212,[64],[]],[65,228,[],[]],[71,736,[],[]]],\"edges\":[[39,[20,39,46,52,53,60,64,65,69,70,71,76,83,85]],[43,[18,41,49,53,54,61,66,67,71,78,81]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-15,-13],[-18,-15],[-23,-7],[-23,-10],[-24,-23],[-26,-23],[-27,-7],[-27,-10],[-27,-24],[-27,-26],[-28,-3],[-28,-11],[-28,-14],[-28,-22],[-28,-25],[-1,7,9,10,21],[-13,9,10,21],[-17,7,9,10],[-18,7,9,21],[-5],[-2,23,27,28],[-6,28],[-12,27],[-19,23,27],[-20,23,28],[-4,23],[-8,27],[-9],[-15,28],[-28,15],[-16],[-21],[-29,5,13,17,18],[-30,3,11,14,22,25],[-31,29],[-32,31],[-33,30],[-34,33],[-35,32,34],[35],[-15,36],[-28,37],[-7,38],[-10,38],[-36,-37,39],[-39,40],[-38,41],[-41,42],[-40,-42,43],[-43],[2,4,6,8,9,12,15,16,19,20,21,23,27,28],[1,5,7,9,10,13,17,18,21,24,26]],\"atoms\":[{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":67,\"b\":64},{\"tag\":\"incompatible\",\"a\":76,\"b\":49},{\"tag\":\"incompatible\",\"a\":76,\"b\":54},{\"tag\":\"incompatible\",\"a\":78,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":76},{\"tag\":\"incompatible\",\"a\":83,\"b\":49},{\"tag\":\"incompatible\",\"a\":83,\"b\":54},{\"tag\":\"incompatible\",\"a\":83,\"b\":78},{\"tag\":\"incompatible\",\"a\":83,\"b\":81},{\"tag\":\"incompatible\",\"a\":85,\"b\":31},{\"tag\":\"incompatible\",\"a\":85,\"b\":56},{\"tag\":\"incompatible\",\"a\":85,\"b\":62},{\"tag\":\"incompatible\",\"a\":85,\"b\":73},{\"tag\":\"incompatible\",\"a\":85,\"b\":79},{\"tag\":\"mate\",\"ridge\":641,\"a\":18,\"owners\":[49,53,54,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":61,\"owners\":[53,54,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":66,\"owners\":[49,53,54]},{\"tag\":\"mate\",\"ridge\":641,\"a\":67,\"owners\":[49,53,71]},{\"tag\":\"mate\",\"ridge\":644,\"a\":41,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":200,\"a\":20,\"owners\":[76,83,85]},{\"tag\":\"mate\",\"ridge\":200,\"a\":46,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":200,\"a\":60,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":200,\"a\":69,\"owners\":[76,83]},{\"tag\":\"mate\",\"ridge\":200,\"a\":70,\"owners\":[76,85]},{\"tag\":\"mate\",\"ridge\":198,\"a\":39,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":450,\"a\":52,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":706,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":212,\"a\":64,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":212,\"a\":85,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":228,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":71,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[41,61,66,67],\"full_literals\":[-29,5,13,17,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[31,56,62,73,79],\"full_literals\":[-30,3,11,14,22,25]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-31,false,29],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-32,31,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-33,30,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-34,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-35,32,34],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":64,\"full_literals\":[-15,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":85,\"full_literals\":[-28,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":49,\"full_literals\":[-7,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":54,\"full_literals\":[-10,38]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-37,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[20,39,46,52,53,60,64,65,69,70,71,76,83,85]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,41,49,53,54,61,66,67,71,78,81]}]}"
  "p cnf 43 52\n-15 -13 0\n-18 -15 0\n-23 -7 0\n-23 -10 0\n-24 -23 0\n-26 -23 0\n-27 -7 0\n-27 -10 0\n-27 -24 0\n-27 -26 0\n-28 -3 0\n-28 -11 0\n-28 -14 0\n-28 -22 0\n-28 -25 0\n-1 7 9 10 21 0\n-13 9 10 21 0\n-17 7 9 10 0\n-18 7 9 21 0\n-5 0\n-2 23 27 28 0\n-6 28 0\n-12 27 0\n-19 23 27 0\n-20 23 28 0\n-4 23 0\n-8 27 0\n-9 0\n-15 28 0\n-28 15 0\n-16 0\n-21 0\n-29 5 13 17 18 0\n-30 3 11 14 22 25 0\n-31 29 0\n-32 31 0\n-33 30 0\n-34 33 0\n-35 32 34 0\n35 0\n-15 36 0\n-28 37 0\n-7 38 0\n-10 38 0\n-36 -37 39 0\n-39 40 0\n-38 41 0\n-41 42 0\n-40 -42 43 0\n-43 0\n2 4 6 8 9 12 15 16 19 20 21 23 27 28 0\n1 5 7 9 10 13 17 18 21 24 26 0\n"
  "53 -29 13 17 18 0 20 33 0\n54 2 4 6 8 12 15 19 20 23 27 28 0 28 31 32 51 0\n55 1 7 10 13 17 18 24 26 0 20 28 32 52 0\n56 -27 0 32 28 7 8 9 10 18 19 17 16 55 0\n57 -12 0 56 23 0\n58 -8 0 56 27 0\n59 23 28 0 56 58 57 29 22 26 21 24 25 54 0\n60 -23 0 32 28 3 4 5 6 18 19 17 16 55 0\n61 28 0 60 59 0\n62 -3 0 61 11 0\n63 -11 0 61 12 0\n64 -14 0 61 13 0\n65 -22 0 61 14 0\n66 -25 0 61 15 0\n67 15 0 61 30 0\n68 37 0 61 42 0\n69 -30 0 66 62 65 64 63 34 0\n70 -13 0 67 1 0\n71 -18 0 67 2 0\n72 36 0 67 41 0\n73 -33 0 69 37 0\n74 39 0 72 68 45 0\n75 -34 0 73 38 0\n76 40 0 74 46 0\n77 32 0 75 40 39 0\n78 -42 0 76 50 49 0\n79 31 0 77 36 0\n80 -41 0 78 48 0\n81 29 0 79 35 0\n82 -38 0 80 47 0\n83 17 0 81 71 70 53 0\n84 -7 0 82 43 0\n85 -10 0 82 44 0\n86 0 83 84 28 85 18 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e61d45d13c1f1e2e4ad274b8ac6a9a669c659996558d61ba1e4785eb4699665391e595355351d52d1b61d4745d0f6c368ce3a4d9394cd3a2d8b8ad2b1ae1b46c9b16d8731d2785d1725c5783d0f13c1f4b11c4a9261990e0ba9134619194550b41da0cc318e0b0ac4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b69b6db6db4db4d349b6d34924926936934926db49b692489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 67), (facetIndex 71)]))
 (.leaf ([(facetIndex 36), (facetIndex 41), (facetIndex 45), (facetIndex 62)])))
 (.branch 3
 (.leaf ([(facetIndex 31), (facetIndex 42), (facetIndex 46), (facetIndex 48)]))
 (.leaf ([(facetIndex 57), (facetIndex 63)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 24), (facetIndex 51), (facetIndex 54), (facetIndex 65), (facetIndex 82)]))
 (.leaf ([(facetIndex 25), (facetIndex 37), (facetIndex 38), (facetIndex 39)])))
 (.branch 7
 (.leaf ([(facetIndex 23), (facetIndex 26), (facetIndex 50), (facetIndex 53), (facetIndex 55)]))
 (.leaf ([(facetIndex 22), (facetIndex 49), (facetIndex 52)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "100000000000020640018d379ba088088b690004001acdcz10;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 56), (facetIndex 59), (facetIndex 83)]))
 (.leaf ([(facetIndex 60), (facetIndex 81)])))
 (.branch 3
 (.leaf ([(facetIndex 69), (facetIndex 72), (facetIndex 80)]))
 (.leaf ([(facetIndex 34), (facetIndex 40), (facetIndex 76)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 61), (facetIndex 73), (facetIndex 85)]))
 (.leaf ([(facetIndex 27), (facetIndex 32), (facetIndex 84)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 47), (facetIndex 58)]))
 (.branch 8
 (.leaf ([(facetIndex 29), (facetIndex 33), (facetIndex 35), (facetIndex 43), (facetIndex 68), (facetIndex 74), (facetIndex 75), (facetIndex 77)]))
 (.leaf ([(facetIndex 44), (facetIndex 64), (facetIndex 66), (facetIndex 70), (facetIndex 78), (facetIndex 79)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "45001288737742082708080041060000000000600870030000737500765z1b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4, 5]
def grouped2_0009 : List Nat := [4, 5, 6, 7]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [0, 1]
def grouped3_0014 : List Nat := [0, 1, 2, 3]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [4, 5]
def grouped3_0020 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0021 : List Nat := [6]
def grouped3_0022 : List Nat := [6, 7, 8]
def grouped3_0023 : List Nat := [7]
def grouped3_0024 : List Nat := [7, 8]
def grouped3_0025 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record003" 51

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record003" "{\"ridges\":[[31,194],[36,522],[41,522],[41,642],[42,194],[45,642],[46,194],[57,208],[62,536],[66,534],[77,338],[78,594],[80,480]],\"owners\":[[36,522,[76],[4,25,39,41,66,74,75]],[41,522,[66,75],[4,25,36,39,74,76]],[31,194,[77,78,80],[6,42,46,48,68,72]],[42,194,[72,80],[6,31,46,48,68,77,78]],[46,194,[68,72,77,78],[6,31,42,48,80]],[41,642,[78,79],[7,45,48,74,76]],[45,642,[76],[7,41,48,74,78,79]],[62,536,[66,75],[12,36,52,74,85]],[57,208,[77,78],[13,42,63,68,84]],[66,534,[29],[]],[78,594,[43],[]],[77,338,[69],[]],[80,480,[],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-6,-1],[-6,-3],[-7,-4],[-9,-7],[-12,-7],[-13,-2],[-14,-13],[-15,-6],[-16,-13],[-17,-13],[-19,-4],[-19,-9],[-20,-10],[-20,-19],[-25,-22],[-27,-10],[-27,-25],[-28,-10],[-6,26],[-7,21,25],[-5,27,28,30],[-8,24,30],[-11,22,24,27,28],[-7,28,29],[-10,26],[-19,21,25],[-18,27,28],[-21,4],[-28,9],[-27,23],[-30],[-31,6,7,10,19],[-32,5,8,11,12],[-33,18,20],[-34,2,3,14,16,17],[-35,1,13,15],[-36,31],[-37,32],[-37,33],[-38,36],[-38,37],[-39,34],[-39,35],[-40,39],[-41,38],[-41,40],[41],[-23,42],[-24,42],[-26,43],[-25,44],[-29,45],[-43,46],[-42,46],[-46,47],[-44,-45,48],[-48,49],[-49,50],[-47,-50,51],[-51]],\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":36,\"b\":22},{\"tag\":\"incompatible\",\"a\":36,\"b\":26},{\"tag\":\"incompatible\",\"a\":41,\"b\":29},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":48,\"b\":41},{\"tag\":\"incompatible\",\"a\":49,\"b\":23},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":36},{\"tag\":\"incompatible\",\"a\":53,\"b\":49},{\"tag\":\"incompatible\",\"a\":55,\"b\":49},{\"tag\":\"incompatible\",\"a\":62,\"b\":29},{\"tag\":\"incompatible\",\"a\":62,\"b\":43},{\"tag\":\"incompatible\",\"a\":63,\"b\":45},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":75,\"b\":68},{\"tag\":\"incompatible\",\"a\":77,\"b\":45},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":45},{\"tag\":\"mate\",\"ridge\":522,\"a\":36,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":522,\"a\":41,\"owners\":[66,75]},{\"tag\":\"mate\",\"ridge\":194,\"a\":31,\"owners\":[77,78,80]},{\"tag\":\"mate\",\"ridge\":194,\"a\":42,\"owners\":[72,80]},{\"tag\":\"mate\",\"ridge\":194,\"a\":46,\"owners\":[68,72,77,78]},{\"tag\":\"mate\",\"ridge\":642,\"a\":41,\"owners\":[78,79]},{\"tag\":\"mate\",\"ridge\":642,\"a\":45,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":536,\"a\":62,\"owners\":[66,75]},{\"tag\":\"mate\",\"ridge\":208,\"a\":57,\"owners\":[77,78]},{\"tag\":\"mate\",\"ridge\":534,\"a\":66,\"owners\":[29]},{\"tag\":\"mate\",\"ridge\":594,\"a\":78,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":338,\"a\":77,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":480,\"a\":80,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[36,41,45,62],\"full_literals\":[-31,6,7,10,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[31,42,46,48],\"full_literals\":[-32,5,8,11,12]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[57,63],\"full_literals\":[-33,18,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[23,26,50,53,55],\"full_literals\":[-34,2,3,14,16,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[22,49,52],\"full_literals\":[-35,1,13,15]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-36,false,31],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-37,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-38,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-39,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-41,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-41,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-23,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":72,\"full_literals\":[-24,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-26,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":75,\"full_literals\":[-25,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":79,\"full_literals\":[-29,45]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-45,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-47,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "p cnf 51 60\n-6 -1 0\n-6 -3 0\n-7 -4 0\n-9 -7 0\n-12 -7 0\n-13 -2 0\n-14 -13 0\n-15 -6 0\n-16 -13 0\n-17 -13 0\n-19 -4 0\n-19 -9 0\n-20 -10 0\n-20 -19 0\n-25 -22 0\n-27 -10 0\n-27 -25 0\n-28 -10 0\n-6 26 0\n-7 21 25 0\n-5 27 28 30 0\n-8 24 30 0\n-11 22 24 27 28 0\n-7 28 29 0\n-10 26 0\n-19 21 25 0\n-18 27 28 0\n-21 4 0\n-28 9 0\n-27 23 0\n-30 0\n-31 6 7 10 19 0\n-32 5 8 11 12 0\n-33 18 20 0\n-34 2 3 14 16 17 0\n-35 1 13 15 0\n-36 31 0\n-37 32 0\n-37 33 0\n-38 36 0\n-38 37 0\n-39 34 0\n-39 35 0\n-40 39 0\n-41 38 0\n-41 40 0\n41 0\n-23 42 0\n-24 42 0\n-26 43 0\n-25 44 0\n-29 45 0\n-43 46 0\n-42 46 0\n-46 47 0\n-44 -45 48 0\n-48 49 0\n-49 50 0\n-47 -50 51 0\n-51 0\n"
  "61 38 0 47 45 0\n62 40 0 47 46 0\n63 36 0 61 40 0\n64 37 0 61 41 0\n65 39 0 62 44 0\n66 31 0 63 37 0\n67 32 0 64 38 0\n68 33 0 64 39 0\n69 34 0 65 42 0\n70 35 0 65 43 0\n71 -7 42 0 31 67 49 22 48 30 3 4 5 28 29 20 21 15 33 23 0\n72 46 0 66 68 53 54 50 48 19 25 30 71 32 12 14 29 34 27 0\n73 47 0 72 55 0\n74 -50 0 73 60 59 0\n75 -49 0 74 58 0\n76 -48 0 75 57 0\n77 -19 0 68 11 12 14 28 29 34 26 27 17 0\n78 -6 0 70 69 1 2 8 36 6 7 9 10 35 0\n79 -7 0 76 3 4 28 29 20 24 51 52 56 0\n80 10 0 79 66 78 77 32 0\n81 -20 0 80 13 0\n82 -27 0 80 16 0\n83 -28 0 80 18 0\n84 18 0 81 68 34 0\n85 0 84 82 83 27 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1f0f2e2aca7287ae1aa669876c386e8791e1783e3c789b25c91e785a95a51d70d1b61d4745d0f783b0dc3a8da334cb3c2e8b62e4b52ccb1ae1b46c3bc1e8761e2749ca719e1745c5713c2f38872168368390e078e11c4590d60d4341da0d8330ca318c530ce0b42c4b06e0741c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a6da6da4d24936d36d2692492492492492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 65), (facetIndex 69), (facetIndex 73)]))
 (.leaf ([(facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 64)])))
 (.branch 3
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 79)]))
 (.leaf ([(facetIndex 80), (facetIndex 84), (facetIndex 88)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 30), (facetIndex 33), (facetIndex 34), (facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 41)]))
 (.leaf ([(facetIndex 31), (facetIndex 43), (facetIndex 44), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51)])))
 (.branch 7
 (.leaf ([(facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58)]))
 (.leaf ([(facetIndex 32), (facetIndex 35), (facetIndex 42), (facetIndex 45)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "30030034124800000010493b6db6b6db7dbe4924f27bz17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4, 5]
def grouped2_0009 : List Nat := [4, 5, 6, 7]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record011" 21

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record011" "{\"ridges\":[[65,112],[73,112]],\"owners\":[[65,112,[28,84,88],[21,69,73,80,89]],[73,112,[28,80,84,89],[21,65,69,88]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-6,-2],[-6,-3],[-6,-4],[-7,-2],[-7,-4],[-7,-5],[-8,-3],[-8,-5],[-9,-1],[-9,-2],[-9,-3],[-9,-4],[-10,-1],[-10,-2],[-10,-4],[-10,-5],[-10,-7],[-11,-1],[-11,-3],[-11,-5],[-12,-2],[-12,-3],[-12,-4],[-6,1,10,11],[-8,1,9,10,12],[-13,6,7,8],[-14,9,10,11],[-15,2,3,4,5],[-16,13],[-17,14],[-18,16],[-18,17],[-19,15],[-20,19],[-21,18],[-21,20],[21]],\"atoms\":[{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":65,\"b\":32},{\"tag\":\"incompatible\",\"a\":65,\"b\":35},{\"tag\":\"incompatible\",\"a\":65,\"b\":42},{\"tag\":\"incompatible\",\"a\":69,\"b\":32},{\"tag\":\"incompatible\",\"a\":69,\"b\":42},{\"tag\":\"incompatible\",\"a\":69,\"b\":45},{\"tag\":\"incompatible\",\"a\":73,\"b\":35},{\"tag\":\"incompatible\",\"a\":73,\"b\":45},{\"tag\":\"incompatible\",\"a\":80,\"b\":28},{\"tag\":\"incompatible\",\"a\":80,\"b\":32},{\"tag\":\"incompatible\",\"a\":80,\"b\":35},{\"tag\":\"incompatible\",\"a\":80,\"b\":42},{\"tag\":\"incompatible\",\"a\":84,\"b\":28},{\"tag\":\"incompatible\",\"a\":84,\"b\":32},{\"tag\":\"incompatible\",\"a\":84,\"b\":42},{\"tag\":\"incompatible\",\"a\":84,\"b\":45},{\"tag\":\"incompatible\",\"a\":84,\"b\":69},{\"tag\":\"incompatible\",\"a\":88,\"b\":28},{\"tag\":\"incompatible\",\"a\":88,\"b\":35},{\"tag\":\"incompatible\",\"a\":88,\"b\":45},{\"tag\":\"incompatible\",\"a\":89,\"b\":32},{\"tag\":\"incompatible\",\"a\":89,\"b\":35},{\"tag\":\"incompatible\",\"a\":89,\"b\":42},{\"tag\":\"mate\",\"ridge\":112,\"a\":65,\"owners\":[28,84,88]},{\"tag\":\"mate\",\"ridge\":112,\"a\":73,\"owners\":[28,80,84,89]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[65,69,73],\"full_literals\":[-13,6,7,8]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[80,84,88],\"full_literals\":[-14,9,10,11]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[32,35,42,45],\"full_literals\":[-15,2,3,4,5]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-16,13,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-17,false,14],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-18,16,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-18,false,17],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-19,false,15],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-20,false,19],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-21,18,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-21,false,20],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "p cnf 21 37\n-6 -2 0\n-6 -3 0\n-6 -4 0\n-7 -2 0\n-7 -4 0\n-7 -5 0\n-8 -3 0\n-8 -5 0\n-9 -1 0\n-9 -2 0\n-9 -3 0\n-9 -4 0\n-10 -1 0\n-10 -2 0\n-10 -4 0\n-10 -5 0\n-10 -7 0\n-11 -1 0\n-11 -3 0\n-11 -5 0\n-12 -2 0\n-12 -3 0\n-12 -4 0\n-6 1 10 11 0\n-8 1 9 10 12 0\n-13 6 7 8 0\n-14 9 10 11 0\n-15 2 3 4 5 0\n-16 13 0\n-17 14 0\n-18 16 0\n-18 17 0\n-19 15 0\n-20 19 0\n-21 18 0\n-21 20 0\n21 0\n"
  "38 18 0 37 35 0\n39 20 0 37 36 0\n40 16 0 38 31 0\n41 17 0 38 32 0\n42 19 0 39 34 0\n43 13 0 40 29 0\n44 14 0 41 30 0\n45 15 0 42 33 0\n46 -1 0 44 9 13 18 27 0\n47 -7 3 5 0 45 4 5 28 0\n48 9 10 5 12 0 46 44 43 45 25 27 19 47 26 1 3 28 0\n49 -9 5 0 45 10 11 12 28 0\n50 9 5 12 0 43 45 48 14 15 17 28 2 7 26 0\n51 5 12 0 49 50 0\n52 -5 0 43 46 6 8 16 20 26 24 0\n53 12 0 52 51 0\n54 -2 0 53 21 0\n55 -3 0 53 22 0\n56 -4 0 53 23 0\n57 0 56 55 45 52 54 28 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00058.record011
