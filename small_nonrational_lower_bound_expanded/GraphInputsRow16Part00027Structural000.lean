module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00027Data
public import GraphInputsRow16Part00027Frames
public import GraphInputsRow16Part00027Leaves
public import GraphInputsRow16Part00027Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record022
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 306244774803800064, 2201439174656, 212755499974656, 30829275250688, 281749854617600]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 3), 9223512774343131136, (certNat% 4), 334253682327552, 13194139533312]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 283676147449856, 212755499974656, 56294995342131200, 360287970726510592, 268435456]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), 56294995342131200, 4398986035200, 288371113640067072, 72057594037927936]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [370100695874928640, 1374406311936, 318860519538688, (certNat% 8), 57420895248973824, (certNat% 9)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [66995464003649536, (certNat% 10), 360287970860728320, 9223513942574235648, 2201439174656, 343082054713344, 71201967833088]
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
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record028
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record028
def vertexColumn : Fields := ⟨10, (certNat% 11)⟩
def kindColumn : Fields := ⟨3, (certNat% 12)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), 47287796087390208, (certNat% 15), 144115191833952256]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 6047313952768, 155374187144282112, 220039764508672, (certNat% 17), 2199023255552]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 26388279066624, 153122389478080512, (certNat% 19), 140737488355328]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1190495379515244544, 2748862955520, 155937137097703424, (certNat% 20), (certNat% 21), 2147483648]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1191597639871758336, 26388413284352, (certNat% 21), 153685339431501824, (certNat% 22), (certNat% 23)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 52776558133248, 1188950301625810944, 213305255788544, 8796093022208]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), 52776558133248, 1297036692682702848, 36030996042219520, 219902325555200]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 22), 1306043891937443840, 213442694742016, (certNat% 27), 8796093022208]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), 321607151124480, 11821949088956416, (certNat% 29), 1125917103489024]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [421908591935488, (certNat% 30), (certNat% 14), 47287796087390208, 144115191297081344, (certNat% 15)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [560467374243840, (certNat% 31), 1306043891937443840, (certNat% 20), 3940649741058048, 16777216]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [144533646735310848, (certNat% 32), 144173462192128, 47287796087390208, (certNat% 33), (certNat% 15)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 57174738862080, 38280596899758080, (certNat% 30)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [66732962086912, 352960412385280, (certNat% 35), 144678140180955136, (certNat% 36), 142936578719744, 3377699737305088]
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
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record028

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record040
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record040
def vertexColumn : Fields := ⟨10, (certNat% 37)⟩
def kindColumn : Fields := ⟨3, (certNat% 38)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), 2314854606514946048, 184992831373312, 293017649779048448, 4611686018427387904, 1305670057984]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2306054094894137344, (certNat% 40), 1445655480385929216, 81064810472538112, 54324672652640256, 1073741824]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), 10857677324288, 3467776111121793024, 112589990684262400, 4611967493404098560, 288232575174967296]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3467982755537616896, 44291850240, 329044247774756864, (certNat% 40), 72057613365280768, 18014398509481984]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3539836831694585856, 184752313204736, (certNat% 42), 329044247808311296, 4611686018427387904, 1236950581248]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), 3458764513820540928, 54043197675929600, 288233674686595072, 72057594037927936]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 184752313204736, 18014401999142912, 108086391056891904, 288233674686595072, 137438953472]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8079462495158272000, (certNat% 45), 184752313204736, 112589992831746048, 558412857344, 1236950581248, 288514050185232384]
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
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record040

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9719a9995693a2e2b85e0faa966659996555564d2b61d1743d70da398d9362e4b8ad1b26c5b0ee4751e2729c6745c3783c8f13e2c548aa1582e079518a4a9916251560d0b41d60d4328d1314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6da69249b49249249a4d2492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 57)]))
 (.branch 2
 (.leaf ([(facetIndex 66)]))
 (.leaf ([(facetIndex 42), (facetIndex 45)]))))
 (.branch 4
 (.leaf ([(facetIndex 56), (facetIndex 63)]))
 (.branch 5
 (.leaf ([(facetIndex 65)]))
 (.leaf ([(facetIndex 67)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "a6060000300000001008z1f;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record002" 31

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record002" "{\"ridges\":[[11,385],[11,386],[17,580],[36,577],[42,586],[43,385],[44,385],[45,610],[46,385],[46,386],[47,385],[47,386],[52,580],[54,580],[55,580],[57,408],[66,408]],\"owners\":[[11,385,[57],[43,44,46,47]],[43,385,[],[11,44,46,47,57]],[44,385,[],[11,43,46,47,57]],[46,385,[57],[11,43,44,47]],[47,385,[57],[11,43,44,46]],[11,386,[66],[43,44,46,47]],[46,386,[66],[11,43,44,47]],[47,386,[66],[11,43,44,46]],[36,577,[56],[17,42,45,52,54,55]],[17,580,[63,65,67],[36,52,54,55]],[52,580,[65],[17,36,54,55,63,67]],[54,580,[63,65],[17,36,52,55,67]],[55,580,[63,67],[17,36,52,54,65]],[42,586,[63],[]],[45,610,[65],[]],[57,408,[66],[]],[66,408,[57],[]]],\"edges\":[[41,[17,36,42,45,52,54,55,56,63,65,67]],[42,[11,43,44,46,47,57,66]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,14],[-5],[-6],[-8,14],[-9,14],[-1,17],[-8,17],[-9,17],[-3,13],[-2,15,16,18],[-10,16],[-11,15,16],[-12,15,18],[-4,15],[-7,16],[-14,17],[-17,14],[-19,14],[-14,19],[-20,17],[-17,20],[-13,22],[-15,22],[-16,23],[-18,24],[-25,20,21],[-21,25],[-20,25],[-20,-21,26],[-27,19,25],[-25,27],[-26,28],[-19,27],[-19,-25,28],[-24,29],[-23,29],[-29,30],[-22,30],[-28,-30,31],[-31],[2,3,4,7,10,11,12,13,15,16,18],[1,5,6,8,9,14,17]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":385,\"a\":11,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":385,\"a\":43,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":385,\"a\":44,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":385,\"a\":46,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":385,\"a\":47,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":386,\"a\":11,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":386,\"a\":46,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":386,\"a\":47,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":577,\"a\":36,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":580,\"a\":17,\"owners\":[63,65,67]},{\"tag\":\"mate\",\"ridge\":580,\"a\":52,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":580,\"a\":54,\"owners\":[63,65]},{\"tag\":\"mate\",\"ridge\":580,\"a\":55,\"owners\":[63,67]},{\"tag\":\"mate\",\"ridge\":586,\"a\":42,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":610,\"a\":45,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":408,\"a\":57,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":408,\"a\":66,\"owners\":[57]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[57],\"full_literals\":[-19,14]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":57,\"full_literals\":[-14,19]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[66],\"full_literals\":[-20,17]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-17,20]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":56,\"full_literals\":[-13,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":63,\"full_literals\":[-15,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":65,\"full_literals\":[-16,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":67,\"full_literals\":[-18,24]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-25,20,21],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-21,25],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-20,false,25],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-20,-21,26],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-27,19,25],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-25,27],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-26,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-19,false,27],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-19,-25,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-23,false,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-22,false,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-28,-30,31],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[17,36,42,45,52,54,55,56,63,65,67]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[11,43,44,46,47,57,66]}]}"
  "43 1 8 9 14 17 0 2 3 42 0\n44 27 0 31 33 28 19 21 1 4 5 43 0\n45 -21 28 0 32 27 29 34 21 19 6 7 8 43 0\n46 -25 28 0 45 26 34 20 19 17 0\n47 25 0 44 28 30 21 18 16 0\n48 28 0 47 46 0\n49 -30 0 48 40 39 0\n50 -29 0 49 37 0\n51 -22 0 49 38 0\n52 -24 0 50 35 0\n53 -23 0 50 36 0\n54 -13 0 51 22 0\n55 -15 0 51 23 0\n56 -18 0 52 25 0\n57 -16 0 53 24 0\n58 -3 0 54 9 0\n59 -4 0 55 14 0\n60 -12 0 56 55 13 0\n61 -2 0 56 55 57 10 0\n62 -10 0 57 11 0\n63 -7 0 57 15 0\n64 -11 0 57 55 12 0\n65 0 61 62 57 58 56 64 60 54 55 59 63 41 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record027
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9b23c9a99a1ea662d98e93a2e1b89e0fb499a5998e479996352d58d9362d1b61d2743d70e6358d932cc7362e4b8ac6b46c9b16c3b61e4789ca719e0f43c8f13c2f528960d81e9864952625254358341d60d4318c930cd0b12c1b21c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6d36da4936d24d2692492492692493492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 63), (facetIndex 64), (facetIndex 69)]))
 (.leaf ([(facetIndex 40), (facetIndex 53), (facetIndex 61), (facetIndex 62)])))
 (.branch 3
 (.leaf ([(facetIndex 33), (facetIndex 41), (facetIndex 44), (facetIndex 47)]))
 (.leaf ([(facetIndex 31), (facetIndex 52), (facetIndex 56), (facetIndex 57)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 55)]))
 (.leaf ([(facetIndex 29), (facetIndex 38), (facetIndex 42), (facetIndex 45), (facetIndex 46)])))
 (.branch 7
 (.leaf ([(facetIndex 24), (facetIndex 25), (facetIndex 26), (facetIndex 27), (facetIndex 28), (facetIndex 30)]))
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 43)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4801b80b12456af5117ffd07aedb6z12;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 60)]))
 (.branch 2
 (.leaf ([(facetIndex 68), (facetIndex 72)]))
 (.leaf ([(facetIndex 32), (facetIndex 39), (facetIndex 51)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 65), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 70), (facetIndex 73), (facetIndex 75)])))
 (.branch 6
 (.leaf ([(facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 71), (facetIndex 74)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9a1d016d8000b40000400000000400002z18;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4, 5, 6, 7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1, 2]
def grouped3_0010 : List Nat := [1]
def grouped3_0011 : List Nat := [1, 2]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [3]
def grouped3_0014 : List Nat := [3, 4]
def grouped3_0015 : List Nat := [3, 4, 5, 6]
def grouped3_0016 : List Nat := [4]
def grouped3_0017 : List Nat := [5, 6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record027" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record027" 30

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record027" "{\"ridges\":[[11,385],[11,386],[33,385],[33,386],[40,584],[41,385],[44,385],[44,386],[47,385],[47,386],[53,584],[54,396],[60,408],[61,608],[62,584],[68,396],[72,408]],\"owners\":[[11,385,[54,60],[33,41,44,47]],[33,385,[60],[11,41,44,47,54]],[41,385,[],[11,33,44,47,54,60]],[44,385,[54],[11,33,41,47,60]],[47,385,[54,60],[11,33,41,44]],[11,386,[68,72],[33,41,44,47]],[33,386,[72],[11,41,44,47,68]],[44,386,[68],[11,33,41,47,72]],[47,386,[68,72],[11,33,41,44]],[40,584,[75],[18,53,61,62,67,73]],[53,584,[73],[18,40,61,62,67,75]],[62,584,[67,73,75],[18,40,53,61]],[61,608,[70],[19,46,57,73,75]],[54,396,[68],[]],[68,396,[54],[]],[60,408,[72],[]],[72,408,[60],[]]],\"edges\":[[42,[11,33,41,44,47,54,60,68,72]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record027" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record027\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,8,9],[-2,9],[-4],[-5,8],[-6,8,9],[-1,13,15],[-2,15],[-5,13],[-6,13,15],[-3,17],[-7,16],[-11,12,16,17],[-10,14],[-8,13],[-13,8],[-9,15],[-15,9],[-18,3,7,10,11],[-19,18],[-20,19],[-21,20],[21],[-8,22],[-9,22],[-13,23],[-15,23],[-12,24],[-14,25],[-16,25],[-17,25],[-23,26],[-22,-26,27],[-25,28],[-24,28],[-28,29],[-27,-29,30],[-30],[1,2,4,5,6,8,9,13,15]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":385,\"a\":11,\"owners\":[54,60]},{\"tag\":\"mate\",\"ridge\":385,\"a\":33,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":385,\"a\":41,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":385,\"a\":44,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":385,\"a\":47,\"owners\":[54,60]},{\"tag\":\"mate\",\"ridge\":386,\"a\":11,\"owners\":[68,72]},{\"tag\":\"mate\",\"ridge\":386,\"a\":33,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":386,\"a\":44,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":386,\"a\":47,\"owners\":[68,72]},{\"tag\":\"mate\",\"ridge\":584,\"a\":40,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":584,\"a\":53,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":584,\"a\":62,\"owners\":[67,73,75]},{\"tag\":\"mate\",\"ridge\":608,\"a\":61,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":396,\"a\":54,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":396,\"a\":68,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":408,\"a\":60,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":408,\"a\":72,\"owners\":[60]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[40,53,61,62],\"full_literals\":[-18,3,7,10,11]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-19,false,18],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-20,19,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-21,20,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":54,\"full_literals\":[-8,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":60,\"full_literals\":[-9,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":68,\"full_literals\":[-13,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":72,\"full_literals\":[-15,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-12,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-14,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":73,\"full_literals\":[-16,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":75,\"full_literals\":[-17,25]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-23,false,26],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-22,-26,27],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-25,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-24,false,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-29,30],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[11,33,41,44,47,54,60,68,72]}]}"
  "39 20 0 22 21 0\n40 19 0 39 20 0\n41 18 0 40 19 0\n42 1 2 5 6 8 9 13 15 0 3 38 0\n43 28 0 41 33 34 28 29 30 27 13 11 10 12 18 0\n44 29 0 43 35 0\n45 -27 0 44 37 36 0\n46 13 15 0 6 8 14 7 16 9 42 0\n47 23 0 25 26 46 0\n48 26 0 47 31 0\n49 -22 0 48 45 32 0\n50 -8 0 49 23 0\n51 -9 0 49 24 0\n52 -1 0 50 51 1 0\n53 -5 0 50 4 0\n54 -13 0 50 15 0\n55 -2 0 51 2 0\n56 -15 0 51 17 0\n57 -6 0 51 50 5 0\n58 0 53 52 55 57 50 51 54 56 42 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00027.record027
