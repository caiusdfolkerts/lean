module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00026Data
public import GraphInputsRow16Part00026Frames
public import GraphInputsRow16Part00026Leaves
public import GraphInputsRow16Part00026Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 3458764513820540928, (certNat% 3), 423586854600704, 125894081380352]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 9223372048129064960, (certNat% 5), 155692564480, (certNat% 6)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 10376293541461622784, (certNat% 8), (certNat% 9), 63771674411008, 70368744177664]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 423311976693760, (certNat% 11), 2308094809027379200, (certNat% 12)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 9), (certNat% 8), 36833639530496, 17592186044416]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 6), 37108517437440, 2251799813685248, (certNat% 15), 17592186044416]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 423312530341888, 120460410880, (certNat% 17), (certNat% 11), (certNat% 18)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [13907173098517430272, (certNat% 6), (certNat% 19), (certNat% 20), 12644383719424, (certNat% 21)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 10376293550588428288, (certNat% 23), (certNat% 24), 70506317348864, 48103633715200, (certNat% 25)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015
def vertexColumn : Fields := ⟨10, (certNat% 26)⟩
def kindColumn : Fields := ⟨3, (certNat% 27)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), 23158463660032, 211381110439936, 219550481834311680, 18295873486192640, 4611686018427387904]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1381549843129827328, 18858823439613952, (certNat% 29), 164376988352512, 36028798092705792, 103087603712]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [164781986152448, (certNat% 30), 1297107061426880512, 4898947072, 54324670773592064, 85005442966618112]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [139400802052603904, 1297036692682702848, (certNat% 29), 142391050764288, 22058952032256]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1381692263645577216, 18858823443808256, 1811939328, (certNat% 31), 22058952032256, 4611686018427387904]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), 1155173579298439168, 4370464768, 23158463660032, 211655988346880]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 85005442966618112, 1152992697984745472, 4911529984, 23158463660032, 4611967493404098560, 140737488355328]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c9 c3
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c10 c2
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c11 c1
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c12 c0
  c13
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5a8e6a5936a392e1ba1e4785e5a719a94e5a5535a364d4b46d4745d68d6338e934ce8b52d2b1ae1b16e8731d2785d1725c570de0f43c8f0be1c468a61984e07a1946685294658560d1341d48ca318d1342c4b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "69b6d249a49349a4924d3492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 44), (facetIndex 46)]))
 (.branch 2
 (.leaf ([(facetIndex 53), (facetIndex 56)]))
 (.leaf ([(facetIndex 61), (facetIndex 66)]))))
 (.branch 4
 (.leaf ([(facetIndex 67), (facetIndex 69)]))
 (.branch 5
 (.leaf ([(facetIndex 68)]))
 (.leaf ([(facetIndex 71)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "a1c680010001008z27;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record005" 34

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record005" "{\"ridges\":[[11,289],[18,641],[18,644],[36,290],[38,641],[42,290],[44,650],[45,289],[46,658],[48,290],[49,289],[55,641],[55,644],[56,308],[57,641],[57,644],[59,641],[59,644],[61,360],[67,650],[69,658]],\"owners\":[[11,289,[53,56,61],[36,42,45,48,49]],[45,289,[53,61],[11,36,42,48,49,56]],[49,289,[53,56,61],[11,36,42,45,48]],[36,290,[71],[11,42,45,48,49,66,68]],[42,290,[68],[11,36,45,48,49,66,71]],[48,290,[66,68],[11,36,42,45,49,71]],[18,641,[44,46],[38,55,57,59]],[38,641,[],[18,44,46,55,57,59]],[55,641,[46],[18,38,44,57,59]],[57,641,[44],[18,38,46,55,59]],[59,641,[44,46],[18,38,55,57]],[18,644,[67,69],[38,55,57,59]],[55,644,[69],[18,38,57,59,67]],[57,644,[67],[18,38,55,59,69]],[59,644,[67,69],[18,38,55,57]],[44,650,[67],[]],[67,650,[44],[]],[46,658,[69],[]],[69,658,[46],[]],[56,308,[68],[]],[61,360,[71],[]]],\"edges\":[[37,[11,36,42,45,48,49,53,56,61,66,68,71]],[43,[18,38,44,46,55,57,59,67,69]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,11,13,16],[-7,11,16],[-10,11,13,16],[-3,21],[-5,19],[-9,17,19],[-2,6,8],[-4],[-12,8],[-14,6],[-15,6,8],[-2,18,20],[-12,20],[-14,18],[-15,18,20],[-6,18],[-18,6],[-8,20],[-20,8],[-13,19],[-16,21],[-6,22],[-8,22],[-11,23],[-17,24],[-18,25],[-20,25],[-19,26],[-21,27],[-24,28],[-23,28],[-22,29],[-22,-28,30],[-27,31],[-26,31],[-25,32],[-25,-31,33],[-29,-33,34],[-30,-32,34],[-34],[1,3,5,7,9,10,11,13,16,17,19,21],[2,4,6,8,12,14,15,18,20]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":289,\"a\":11,\"owners\":[53,56,61]},{\"tag\":\"mate\",\"ridge\":289,\"a\":45,\"owners\":[53,61]},{\"tag\":\"mate\",\"ridge\":289,\"a\":49,\"owners\":[53,56,61]},{\"tag\":\"mate\",\"ridge\":290,\"a\":36,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":290,\"a\":42,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":290,\"a\":48,\"owners\":[66,68]},{\"tag\":\"mate\",\"ridge\":641,\"a\":18,\"owners\":[44,46]},{\"tag\":\"mate\",\"ridge\":641,\"a\":38,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":641,\"a\":55,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":641,\"a\":57,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":641,\"a\":59,\"owners\":[44,46]},{\"tag\":\"mate\",\"ridge\":644,\"a\":18,\"owners\":[67,69]},{\"tag\":\"mate\",\"ridge\":644,\"a\":55,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":644,\"a\":57,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":644,\"a\":59,\"owners\":[67,69]},{\"tag\":\"mate\",\"ridge\":650,\"a\":44,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":650,\"a\":67,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":658,\"a\":46,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":658,\"a\":69,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":308,\"a\":56,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":360,\"a\":61,\"owners\":[71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":44,\"full_literals\":[-6,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":46,\"full_literals\":[-8,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":53,\"full_literals\":[-11,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-17,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-18,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":69,\"full_literals\":[-20,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":68,\"full_literals\":[-19,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":71,\"full_literals\":[-21,27]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-23,false,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-22,false,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-22,-28,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-31,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-29,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-30,-32,34],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[11,36,42,45,48,49,53,56,61,66,68,71]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,38,44,46,55,57,59,67,69]}]}"
  "43 2 6 8 12 14 15 18 20 0 8 42 0\n44 6 8 0 7 10 11 17 9 19 43 0\n45 22 0 22 23 44 0\n46 29 0 45 32 0\n47 -33 0 46 40 38 0\n48 -25 0 47 40 45 36 37 39 34 35 33 29 28 30 31 4 21 5 20 25 24 1 2 3 6 41 0\n49 -18 0 48 26 0\n50 -20 0 48 27 0\n51 -2 0 49 50 12 0\n52 -14 0 49 14 0\n53 -6 0 49 16 0\n54 -15 0 49 50 15 0\n55 -12 0 50 13 0\n56 -8 0 50 18 0\n57 0 53 52 51 55 56 54 49 50 43 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record048
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9aa5a8e9a655a36538ae1783e9a6598e5a555635534ad1743dd0dc3a8da398d538ce4b52e2b2ac6b86c3b51e2749e1745c9715c3743c8f13e52169862982e07a51165852942d0758390d4388ca384c5312c2b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "69a6da49a69b692492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 32), (facetIndex 35), (facetIndex 48), (facetIndex 58), (facetIndex 68)]))
 (.leaf ([(facetIndex 31), (facetIndex 39), (facetIndex 44), (facetIndex 46), (facetIndex 60), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 27), (facetIndex 37), (facetIndex 53), (facetIndex 63)]))
 (.leaf ([(facetIndex 30), (facetIndex 36), (facetIndex 41), (facetIndex 54), (facetIndex 64)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 43), (facetIndex 50), (facetIndex 51)]))
 (.leaf ([(facetIndex 38), (facetIndex 45), (facetIndex 52), (facetIndex 62)])))
 (.branch 7
 (.leaf ([(facetIndex 40), (facetIndex 42), (facetIndex 47), (facetIndex 49)]))
 (.leaf ([(facetIndex 29), (facetIndex 33), (facetIndex 34)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "400035410000d5930c6999e3531f82f84z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 55), (facetIndex 57)]))
 (.branch 2
 (.leaf ([(facetIndex 56), (facetIndex 59)]))
 (.leaf ([(facetIndex 61), (facetIndex 69)]))))
 (.branch 4
 (.leaf ([(facetIndex 65), (facetIndex 67)]))
 (.branch 5
 (.leaf ([(facetIndex 66)]))
 (.leaf ([(facetIndex 71)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "a10718010201z2a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6, 7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1, 2]
def grouped3_0010 : List Nat := [1]
def grouped3_0011 : List Nat := [1, 2]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [3]
def grouped3_0014 : List Nat := [3, 4, 5]
def grouped3_0015 : List Nat := [4, 5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record048" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record048" 31

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record048" "{\"ridges\":[[11,545],[36,545],[42,545],[43,321],[43,322],[45,545],[47,545],[49,545],[50,321],[50,322],[51,321],[51,322],[66,564],[71,616]],\"owners\":[[11,545,[56,59,61],[36,42,45,47,49]],[36,545,[59,61],[11,42,45,47,49,56]],[42,545,[56],[11,36,45,47,49,59,61]],[45,545,[61],[11,36,42,47,49,56,59]],[47,545,[56,59],[11,36,42,45,49,61]],[49,545,[56,59,61],[11,36,42,45,47]],[43,321,[57],[12,37,46,50,51,55]],[50,321,[55,57],[12,37,43,46,51]],[51,321,[55,57],[12,37,43,46,50]],[43,322,[67],[12,37,46,50,51,65]],[50,322,[65,67],[12,37,43,46,51]],[51,322,[65,67],[12,37,43,46,50]],[66,564,[56],[]],[71,616,[61],[]]],\"edges\":[[38,[11,36,42,45,47,49,56,59,61,66,69,71]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record048" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record048\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,11,13,14],[-2,13,14],[-3,11],[-5,14],[-6,11,13],[-7,11,13,14],[-4,12],[-8,10,12],[-9,10,12],[-4,17],[-8,15,17],[-9,15,17],[-16,11],[-19,14],[-20,4,8,9],[-21,20],[-22,21],[-23,22],[23],[-10,24],[-12,24],[-11,25],[-13,25],[-14,26],[-18,26],[-15,27],[-17,27],[-26,28],[-25,28],[-24,-28,29],[-27,30],[-29,-30,31],[-31],[1,2,3,5,6,7,11,13,14,16,18,19]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":545,\"a\":11,\"owners\":[56,59,61]},{\"tag\":\"mate\",\"ridge\":545,\"a\":36,\"owners\":[59,61]},{\"tag\":\"mate\",\"ridge\":545,\"a\":42,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":545,\"a\":45,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":545,\"a\":47,\"owners\":[56,59]},{\"tag\":\"mate\",\"ridge\":545,\"a\":49,\"owners\":[56,59,61]},{\"tag\":\"mate\",\"ridge\":321,\"a\":43,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":321,\"a\":50,\"owners\":[55,57]},{\"tag\":\"mate\",\"ridge\":321,\"a\":51,\"owners\":[55,57]},{\"tag\":\"mate\",\"ridge\":322,\"a\":43,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":322,\"a\":50,\"owners\":[65,67]},{\"tag\":\"mate\",\"ridge\":322,\"a\":51,\"owners\":[65,67]},{\"tag\":\"mate\",\"ridge\":564,\"a\":66,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":616,\"a\":71,\"owners\":[61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[43,50,51],\"full_literals\":[-20,4,8,9]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-21,20,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-22,21,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-23,false,22],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":55,\"full_literals\":[-10,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":57,\"full_literals\":[-12,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":56,\"full_literals\":[-11,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":59,\"full_literals\":[-13,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":61,\"full_literals\":[-14,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-18,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":65,\"full_literals\":[-15,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-17,27]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-24,-28,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-29,-30,31],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[11,36,42,45,47,49,56,59,61,66,69,71]}]}"
  "35 22 0 19 18 0\n36 21 0 35 17 0\n37 20 0 36 16 0\n38 28 0 28 29 24 25 22 23 4 14 2 3 5 13 1 6 34 0\n39 10 12 0 37 8 9 7 15 0\n40 24 0 20 21 39 0\n41 29 0 40 38 30 0\n42 -30 0 41 33 32 0\n43 -27 0 42 31 0\n44 -15 0 43 26 0\n45 -17 0 43 27 0\n46 -8 0 44 45 11 0\n47 -9 0 44 45 12 0\n48 -4 0 45 10 0\n49 0 46 48 37 47 15 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00026.record048
