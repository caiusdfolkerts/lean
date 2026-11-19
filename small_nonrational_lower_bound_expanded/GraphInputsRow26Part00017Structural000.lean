module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00017Data
public import GraphInputsRow26Part00017Frames
public import GraphInputsRow26Part00017Leaves
public import GraphInputsRow26Part00017Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 566935683072, 70643622084608, 1729382256910270464]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 3), (certNat% 4), (certNat% 5)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 1157425104234217472, (certNat% 7), 1030792151040, 70368744177664]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 8), (certNat% 9)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c6 c7
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 70643622084608, 576460752303423488]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 566935683072, 70369281048576, (certNat% 12)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), 1730508156817113088, (certNat% 15), 549757911040]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), 105553384701952, (certNat% 18)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), 1154610354468159488, 708669603840, (certNat% 20), 580964351930793984]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 4), (certNat% 22), (certNat% 23), 580964351930793984, 1065151889408]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c18 c15
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c19 c14
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c20 c4
  c21
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record035
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035
def vertexColumn : Fields := ⟨10, (certNat% 24)⟩
def kindColumn : Fields := ⟨3, (certNat% 25)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨47, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), 3746994889972252672, (certNat% 27), (certNat% 28)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 28), (certNat% 30), (certNat% 31)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), 36028805610471424, (certNat% 33), (certNat% 34), 1441151880758558720]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 36), (certNat% 37), 576460752303423488]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 33), (certNat% 39), (certNat% 40), 864691128455135232]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), (certNat% 43), (certNat% 44), 9223372036854775808]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 46), (certNat% 47), (certNat% 48), (certNat% 49), (certNat% 50)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record035

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record038
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f4e31ac2f1ca6a95ad19c6698e655876c398e8b92e2ba1e4783e3c789724d92e785d15c5394d52d475c368d6362d2b61d2743dd0dc338c73c2d8b52ccb8acab86c5bc1d8791d4731e2729c6785e0f43c8f0bc1f7130a0eb06518560d8a90e4c5294550d4530ce0b0ac1b81c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6d26d24db6da6db4da4926db4da6da4db4924d249249b489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 22), (facetIndex 36), (facetIndex 37), (facetIndex 39)]))
 (.leaf ([(facetIndex 32), (facetIndex 77), (facetIndex 80), (facetIndex 81)])))
 (.branch 3
 (.leaf ([(facetIndex 26), (facetIndex 35), (facetIndex 43), (facetIndex 75)]))
 (.leaf ([(facetIndex 23), (facetIndex 38), (facetIndex 48), (facetIndex 51), (facetIndex 63)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 44), (facetIndex 68), (facetIndex 76)]))
 (.leaf ([(facetIndex 31), (facetIndex 58), (facetIndex 59), (facetIndex 60)])))
 (.branch 7
 (.leaf ([(facetIndex 27), (facetIndex 28), (facetIndex 29), (facetIndex 30), (facetIndex 33)]))
 (.leaf ([(facetIndex 56), (facetIndex 57)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "900c400004000605b7f0006030044000c0431bb6c806z11;"⟩
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
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record038" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record038" 72

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record038" "{\"ridges\":[[11,164],[14,168],[19,56],[22,25],[26,517],[26,521],[29,35],[29,164],[30,38],[35,517],[35,772],[36,26],[38,168],[39,35],[43,521],[43,776],[44,35],[44,81],[50,540],[51,164],[60,448],[64,216],[66,897],[68,38],[68,56],[69,284],[71,38],[75,772],[75,776],[76,38],[76,84],[79,38],[83,418],[84,202],[87,652]],\"owners\":[[68,38,[1,28,29,30,78,79],[15,23,71,72,73,76]],[26,517,[61,62],[3,27,30,33,35,50,52,54,55]],[35,517,[50,52,54],[3,26,27,30,33,55,61,62]],[22,25,[13,63,64],[4,36,37,48,49,50]],[36,26,[19,68,69,70],[4,22,37,82]],[26,521,[66],[6,37,39,43,50,52,54,55]],[43,521,[50,52,54],[6,26,37,39,55,66]],[44,81,[10,58,64],[8,36,56,67]],[76,84,[10,58],[16,56,77,88]],[11,164,[71,78,79,85,86,88],[29,51,57,59]],[29,164,[85,86,88],[11,51,57,59,71,78,79]],[51,164,[78,79,88],[11,29,57,59,71,85,86]],[19,56,[13,48,63,85],[68]],[68,56,[13,63],[19,48,85]],[14,168,[71,83,85,86],[38,51,63]],[38,168,[85,86],[14,51,63,71,83]],[35,772,[87],[18,55,61,62,75,81]],[75,772,[61,62],[18,35,55,81,87]],[43,776,[87],[20,55,66,75]],[75,776,[66],[20,43,55,87]],[60,448,[84],[21,46,65,80]],[84,202,[40],[]],[50,540,[70],[]],[87,652,[54],[]],[66,897,[62],[]],[64,216,[],[]],[69,284,[],[]],[83,418,[79],[]]],\"edges\":[[36,[11,14,29,38,45,51,57,59,63,67,71,78,79,83,85,86,88]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record038" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record038\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-7],[-11,-7],[-13,-7],[-14,-2],[-14,-10],[-14,-11],[-14,-12],[-14,-13],[-15,-7],[-15,-14],[-19,-4],[-19,-18],[-20,-13],[-20,-19],[-21,-18],[-21,-20],[-23,-7],[-23,-10],[-23,-17],[-23,-18],[-30,-14],[-30,-23],[-30,-26],[-31,-1],[-31,-8],[-31,-25],[-31,-27],[-32,-11],[-32,-15],[-32,-30],[-32,-31],[-33,-29],[-33,-30],[-33,-31],[-34,-16],[-34,-22],[-35,-34],[-36,-33],[-36,-34],[-37,-31],[-37,-32],[-40,-32],[-41,-8],[-41,-9],[-41,-25],[-41,-27],[-41,-28],[-41,-29],[-45,-41],[-46,-10],[-46,-24],[-46,-30],[-46,-43],[-47,-14],[-47,-46],[-48,-14],[-50,-12],[-50,-17],[-51,-31],[-51,-32],[-52,-9],[-52,-28],[-52,-29],[-52,-41],[-52,-43],[-52,-45],[-54,-32],[-12,-20,-23],[-41,1,11,12,13,47,48],[-13,-44,-46],[-13,-46,-48],[-9,35,36],[-16,26,28,29],[-7,4,37,38],[-17,6,41,42,43],[-9,39],[-22,26,28,29],[-23,2,32,38],[-46,2,32],[-3,44,47,48,51,52,54],[-12,51,52,54],[-27,47,48,54],[-6,4,25,37,51],[-41,4,37],[-5,44,49,51,52],[-19,51,52],[-16,53],[-45,35,36],[-22,53],[-45,39],[-34,50],[-50,21],[-26,43],[-53,29],[-39,36],[-38],[-42],[-49,48],[-55,7,17,18,20],[-56,9,16,22,45],[-57,8,19,25,27,37],[-58,23,41,46],[-59,14,32,33,34],[-60,10,11,12,13,15],[-61,30,31],[-62,55],[-63,56],[-63,57],[-64,62,63],[-65,62],[-65,63],[-66,58,59],[-67,58],[-67,59],[-68,60,61],[-69,60],[-69,61],[-70,66],[-70,67,69],[-71,67],[-70,68],[-71,69],[-72,64],[-72,65,71],[-72,70],[72],[3,5,12,19,24,27,31,33,37,40,44,47,48,49,51,52,54]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":27,\"b\":22},{\"tag\":\"incompatible\",\"a\":28,\"b\":22},{\"tag\":\"incompatible\",\"a\":30,\"b\":22},{\"tag\":\"incompatible\",\"a\":31,\"b\":10},{\"tag\":\"incompatible\",\"a\":31,\"b\":27},{\"tag\":\"incompatible\",\"a\":31,\"b\":28},{\"tag\":\"incompatible\",\"a\":31,\"b\":29},{\"tag\":\"incompatible\",\"a\":31,\"b\":30},{\"tag\":\"incompatible\",\"a\":33,\"b\":22},{\"tag\":\"incompatible\",\"a\":33,\"b\":31},{\"tag\":\"incompatible\",\"a\":38,\"b\":13},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":30},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":44,\"b\":22},{\"tag\":\"incompatible\",\"a\":44,\"b\":27},{\"tag\":\"incompatible\",\"a\":44,\"b\":36},{\"tag\":\"incompatible\",\"a\":44,\"b\":37},{\"tag\":\"incompatible\",\"a\":56,\"b\":31},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":56,\"b\":50},{\"tag\":\"incompatible\",\"a\":57,\"b\":1},{\"tag\":\"incompatible\",\"a\":57,\"b\":23},{\"tag\":\"incompatible\",\"a\":57,\"b\":48},{\"tag\":\"incompatible\",\"a\":57,\"b\":51},{\"tag\":\"incompatible\",\"a\":58,\"b\":28},{\"tag\":\"incompatible\",\"a\":58,\"b\":33},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":54},{\"tag\":\"incompatible\",\"a\":59,\"b\":56},{\"tag\":\"incompatible\",\"a\":59,\"b\":57},{\"tag\":\"incompatible\",\"a\":60,\"b\":35},{\"tag\":\"incompatible\",\"a\":60,\"b\":43},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":63,\"b\":57},{\"tag\":\"incompatible\",\"a\":63,\"b\":58},{\"tag\":\"incompatible\",\"a\":67,\"b\":58},{\"tag\":\"incompatible\",\"a\":68,\"b\":23},{\"tag\":\"incompatible\",\"a\":68,\"b\":26},{\"tag\":\"incompatible\",\"a\":68,\"b\":48},{\"tag\":\"incompatible\",\"a\":68,\"b\":51},{\"tag\":\"incompatible\",\"a\":68,\"b\":52},{\"tag\":\"incompatible\",\"a\":68,\"b\":54},{\"tag\":\"incompatible\",\"a\":75,\"b\":68},{\"tag\":\"incompatible\",\"a\":76,\"b\":27},{\"tag\":\"incompatible\",\"a\":76,\"b\":45},{\"tag\":\"incompatible\",\"a\":76,\"b\":56},{\"tag\":\"incompatible\",\"a\":76,\"b\":70},{\"tag\":\"incompatible\",\"a\":78,\"b\":31},{\"tag\":\"incompatible\",\"a\":78,\"b\":76},{\"tag\":\"incompatible\",\"a\":79,\"b\":31},{\"tag\":\"incompatible\",\"a\":84,\"b\":29},{\"tag\":\"incompatible\",\"a\":84,\"b\":36},{\"tag\":\"incompatible\",\"a\":85,\"b\":57},{\"tag\":\"incompatible\",\"a\":85,\"b\":58},{\"tag\":\"incompatible\",\"a\":86,\"b\":26},{\"tag\":\"incompatible\",\"a\":86,\"b\":52},{\"tag\":\"incompatible\",\"a\":86,\"b\":54},{\"tag\":\"incompatible\",\"a\":86,\"b\":68},{\"tag\":\"incompatible\",\"a\":86,\"b\":70},{\"tag\":\"incompatible\",\"a\":86,\"b\":75},{\"tag\":\"incompatible\",\"a\":88,\"b\":58},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[29,39,44]},{\"tag\":\"mate\",\"ridge\":38,\"a\":68,\"owners\":[1,28,29,30,78,79]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[30,71,76]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[30,76,79]},{\"tag\":\"mate\",\"ridge\":517,\"a\":26,\"owners\":[61,62]},{\"tag\":\"mate\",\"ridge\":517,\"a\":35,\"owners\":[50,52,54]},{\"tag\":\"mate\",\"ridge\":25,\"a\":22,\"owners\":[13,63,64]},{\"tag\":\"mate\",\"ridge\":26,\"a\":36,\"owners\":[19,68,69,70]},{\"tag\":\"mate\",\"ridge\":521,\"a\":26,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":521,\"a\":43,\"owners\":[50,52,54]},{\"tag\":\"mate\",\"ridge\":81,\"a\":44,\"owners\":[10,58,64]},{\"tag\":\"mate\",\"ridge\":84,\"a\":76,\"owners\":[10,58]},{\"tag\":\"mate\",\"ridge\":164,\"a\":11,\"owners\":[71,78,79,85,86,88]},{\"tag\":\"mate\",\"ridge\":164,\"a\":29,\"owners\":[85,86,88]},{\"tag\":\"mate\",\"ridge\":164,\"a\":51,\"owners\":[78,79,88]},{\"tag\":\"mate\",\"ridge\":56,\"a\":19,\"owners\":[13,48,63,85]},{\"tag\":\"mate\",\"ridge\":56,\"a\":68,\"owners\":[13,63]},{\"tag\":\"mate\",\"ridge\":168,\"a\":14,\"owners\":[71,83,85,86]},{\"tag\":\"mate\",\"ridge\":168,\"a\":38,\"owners\":[85,86]},{\"tag\":\"mate\",\"ridge\":772,\"a\":35,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":772,\"a\":75,\"owners\":[61,62]},{\"tag\":\"mate\",\"ridge\":776,\"a\":43,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":776,\"a\":75,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":448,\"a\":60,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":202,\"a\":84,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":540,\"a\":50,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":652,\"a\":87,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":897,\"a\":66,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":216,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":284,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":418,\"a\":83,\"owners\":[79]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[22,36,37,39],\"full_literals\":[-55,7,17,18,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[26,35,43,75],\"full_literals\":[-56,9,16,22,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[23,38,48,51,63],\"full_literals\":[-57,8,19,25,27,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[44,68,76],\"full_literals\":[-58,23,41,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[31,58,59,60],\"full_literals\":[-59,14,32,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[27,28,29,30,33],\"full_literals\":[-60,10,11,12,13,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[56,57],\"full_literals\":[-61,30,31]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,62,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-66,58,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,60,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-69,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-70,66,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-70,67,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-71,67,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-70,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-72,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-72,65,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-72,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":36,\"owners\":[11,14,29,38,45,51,57,59,63,67,71,78,79,83,85,86,88]}]}"
  "128 64 0 126 123 0\n129 70 0 126 125 0\n130 66 0 129 118 0\n131 68 0 129 121 0\n132 -32 -61 0 30 31 105 0\n133 -33 0 126 32 33 34 38 94 105 95 87 89 117 76 90 100 122 107 124 111 0\n134 -30 59 0 130 126 114 120 124 111 107 112 22 23 52 102 44 47 48 49 73 77 100 0\n135 59 0 129 126 96 97 114 119 120 117 124 110 111 106 108 134 105 25 26 27 40 59 101 11 12 14 86 83 84 74 99 65 75 0\n136 32 34 0 129 131 96 135 133 103 4 5 6 7 8 10 21 54 56 78 79 104 115 116 105 119 24 113 69 102 0\n137 -23 -32 0 131 126 132 117 122 124 110 106 115 29 28 17 18 19 20 99 13 68 104 0\n138 -41 -32 0 126 132 117 122 124 111 108 60 41 43 45 46 64 101 86 0\n139 52 -32 0 131 129 133 132 117 119 113 137 138 102 55 51 50 115 67 60 42 41 31 29 28 81 86 104 70 71 98 82 80 85 127 0\n140 -32 0 129 126 132 117 122 119 124 113 111 107 137 138 102 53 93 139 61 62 63 66 73 77 100 0\n141 34 0 140 136 0\n142 -16 0 141 35 0\n143 -22 0 141 36 0\n144 -35 0 141 37 0\n145 -36 0 141 39 0\n146 50 0 141 91 0\n147 -9 0 145 144 72 0\n148 -45 0 145 144 88 0\n149 -12 0 146 57 0\n150 -17 0 146 58 0\n151 21 0 146 92 0\n152 -56 0 148 143 147 142 100 0\n153 -18 0 151 15 0\n154 -20 0 151 16 0\n155 -63 0 152 107 0\n156 -65 0 155 111 0\n157 62 0 155 128 109 0\n158 71 0 156 126 124 0\n159 55 0 157 106 0\n160 69 0 158 122 0\n161 7 0 159 154 150 153 99 0\n162 60 0 160 116 0\n163 -10 0 161 1 0\n164 -11 0 161 2 0\n165 -13 0 161 3 0\n166 -15 0 161 9 0\n167 0 165 163 164 162 149 166 104 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record038

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record057
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "398d531c748f2668b61d8ae1ba1e279e1e4751744f1e25a95a719a6599d1715955552d475c354d8b4ad1b61d4749d70ce364d5334cb31cd8b52c6b86d1b26ca785c970de0f23c4f07caa198560bb1164551c25892a465854558342d28c6324c5322c2b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db4936d24d269a6926934926da49249a6d2492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 47), (facetIndex 52), (facetIndex 59)]))
 (.leaf ([(facetIndex 63), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 80), (facetIndex 81)]))
 (.leaf ([(facetIndex 55), (facetIndex 66)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 76), (facetIndex 78)]))
 (.leaf ([(facetIndex 34), (facetIndex 37), (facetIndex 45)])))
 (.branch 7
 (.leaf ([(facetIndex 77), (facetIndex 79)]))
 (.branch 8
 (.leaf ([(facetIndex 35), (facetIndex 46), (facetIndex 61)]))
 (.leaf ([(facetIndex 71), (facetIndex 72), (facetIndex 82)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "8226464000881000300107000003000000007500000005075z22;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
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
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8]
def grouped3_0016 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record057" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record057" 71

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record057" "{\"ridges\":[[5,137],[9,162],[11,521],[11,524],[13,532],[15,137],[16,137],[16,392],[17,265],[17,521],[17,769],[17,776],[18,273],[19,273],[20,273],[24,138],[27,137],[28,524],[31,532],[32,162],[34,282],[37,330],[38,392],[40,146],[43,400],[44,162],[45,321],[47,273],[48,524],[50,137],[51,524],[52,332],[53,524],[55,180],[57,532],[58,532],[59,836],[60,392],[61,137],[61,521],[61,664],[62,776],[63,360],[64,392],[65,392],[65,776],[66,240],[67,336],[70,480],[72,538],[74,138],[79,336],[80,284],[80,524],[81,836],[82,664]],\"owners\":[[24,138,[5,27,33,38,71,77],[74]],[74,138,[5,33,38,77],[24,27,71]],[40,146,[71,77,79],[7,30,33,41,43,76,78]],[9,162,[24,74,76,78],[32,40,44]],[32,162,[24,78],[9,40,44,74,76]],[44,162,[24,74,76],[9,32,40,78]],[11,521,[17,35,61,62,65],[28,48,51]],[17,521,[11,28,35,48,51,61],[62,65]],[61,521,[11,17,28,51],[35,48,62,65]],[11,524,[72,80],[28,48,51,53]],[28,524,[80],[11,48,51,53,72]],[48,524,[],[11,28,51,53,72,80]],[51,524,[72,80],[11,28,48,53]],[53,524,[72],[11,28,48,51,80]],[80,524,[11,28,51],[48,53,72]],[13,532,[72,80,81],[31,48,57,58]],[31,532,[80,81],[13,48,57,58,72]],[57,532,[72,80],[13,31,48,58,81]],[58,532,[72],[13,31,48,57,80,81]],[17,265,[16,34,37,38,47,52,60,63,64],[53,62]],[16,392,[77,82],[38,60,64,65]],[38,392,[82],[16,60,64,65,77]],[60,392,[],[16,38,64,65,77,82]],[64,392,[77,82],[16,38,60,65]],[65,392,[77],[16,38,60,64,82]],[17,769,[20,58,59,68,69],[53,65]],[17,776,[80,82],[53,62,65]],[62,776,[],[17,53,65,80,82]],[65,776,[80],[17,53,62,82]],[45,321,[18,52,56,59,63,68],[37,42,67,70]],[67,336,[81],[18,42,56,68,79]],[79,336,[18,56,68,81],[42,67]],[43,400,[82],[19,60,67,69,77,79]],[34,282,[77],[]],[72,538,[35],[]],[37,330,[],[]],[80,284,[47],[]],[52,332,[],[]],[55,180,[76],[]],[59,836,[81],[]],[81,836,[59],[]],[61,664,[82],[]],[82,664,[61],[]],[63,360,[],[]],[66,240,[78],[]],[70,480,[],[]]],\"edges\":[[23,[11,13,28,31,48,51,53,57,58,59,72,80,81]],[28,[16,17,34,37,38,47,52,53,60,62,63,64,65,77,80,82]],[29,[11,17,28,35,48,51,53,61,62,65,72,80,82]],[36,[9,15,24,32,40,44,50,55,64,66,70,74,76,78]],[42,[16,19,38,43,45,60,64,65,67,69,70,77,79,82]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record057" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record057\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-18,-17],[-25,-13],[-25,-18],[-28,-25],[-30,-18],[-37,-16],[-37,-20],[-40,-37],[-44,-25],[-45,-25],[-47,-37],[-51,-18],[-51,-37],[-54,-18],[-54,-32],[-54,-37],[-54,-51],[-55,-25],[-55,-54],[-56,-18],[-56,-54],[-1,-6,-37],[-5,-6,-37],[-6,-12,-37],[-6,-27,-37],[-11,1,12,16,20,47,51],[-49,1,16,20,51],[-21,47,51,53],[-2,11,49,50,52],[-15,11,52],[-23,11,49,50],[-3,7,18,37,38,41],[-7,3,13,18,26,28,37],[-37,3,7,13,28],[-3,48,54],[-13,54],[-26],[-28,48,54],[-30,48],[-54,3,13,28],[-4,48,54,55],[-14,54,55],[-33,48,54],[-34,48],[-7,6,17,19,20,25,29,36,39,40],[-6,51,56],[-20,56],[-36],[-40,51,56],[-41,51],[-7,10,34,35,44,45],[-7,54,56],[-38],[-41,54],[-8,-10,-25],[-9,-10,-25],[-24,8,29,32,35,39,44],[-43,55],[-53,8,32,44,55],[-22,56],[-17,51],[-48,18],[-19],[-54,25],[-29],[-31,50],[-35,55],[-55,35],[-37,56],[-56,37],[-39],[-42,52],[-46],[-35,57],[-55,58],[-50,59],[-52,59],[-53,60],[-37,61],[-56,62],[-57,63],[-58,64],[-63,-64,65],[-59,66],[-61,-62,67],[-67,68],[-60,-67,69],[-69,70],[-66,-68,70],[-65,-70,71],[-71],[3,4,13,14,26,28,30,33,34,35,48,54,55],[6,7,17,19,20,25,29,30,36,38,39,40,41,51,54,56],[3,7,13,18,26,28,30,37,38,41,48,54,56],[2,5,11,15,21,23,27,31,40,42,46,49,50,52],[6,9,20,22,24,36,40,41,43,45,46,51,53,56]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":35,\"b\":34},{\"tag\":\"incompatible\",\"a\":47,\"b\":28},{\"tag\":\"incompatible\",\"a\":47,\"b\":35},{\"tag\":\"incompatible\",\"a\":51,\"b\":47},{\"tag\":\"incompatible\",\"a\":53,\"b\":35},{\"tag\":\"incompatible\",\"a\":61,\"b\":33},{\"tag\":\"incompatible\",\"a\":61,\"b\":38},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":68,\"b\":47},{\"tag\":\"incompatible\",\"a\":69,\"b\":47},{\"tag\":\"incompatible\",\"a\":71,\"b\":61},{\"tag\":\"incompatible\",\"a\":77,\"b\":35},{\"tag\":\"incompatible\",\"a\":77,\"b\":61},{\"tag\":\"incompatible\",\"a\":80,\"b\":35},{\"tag\":\"incompatible\",\"a\":80,\"b\":56},{\"tag\":\"incompatible\",\"a\":80,\"b\":61},{\"tag\":\"incompatible\",\"a\":80,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":47},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":35},{\"tag\":\"incompatible\",\"a\":82,\"b\":80},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[5,16,61]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[15,16,61]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[16,27,61]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[16,50,61]},{\"tag\":\"mate\",\"ridge\":138,\"a\":24,\"owners\":[5,27,33,38,71,77]},{\"tag\":\"mate\",\"ridge\":138,\"a\":74,\"owners\":[5,33,38,77]},{\"tag\":\"mate\",\"ridge\":146,\"a\":40,\"owners\":[71,77,79]},{\"tag\":\"mate\",\"ridge\":162,\"a\":9,\"owners\":[24,74,76,78]},{\"tag\":\"mate\",\"ridge\":162,\"a\":32,\"owners\":[24,78]},{\"tag\":\"mate\",\"ridge\":162,\"a\":44,\"owners\":[24,74,76]},{\"tag\":\"mate\",\"ridge\":521,\"a\":11,\"owners\":[17,35,61,62,65]},{\"tag\":\"mate\",\"ridge\":521,\"a\":17,\"owners\":[11,28,35,48,51,61]},{\"tag\":\"mate\",\"ridge\":521,\"a\":61,\"owners\":[11,17,28,51]},{\"tag\":\"mate\",\"ridge\":524,\"a\":11,\"owners\":[72,80]},{\"tag\":\"mate\",\"ridge\":524,\"a\":28,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":524,\"a\":48,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":524,\"a\":51,\"owners\":[72,80]},{\"tag\":\"mate\",\"ridge\":524,\"a\":53,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":524,\"a\":80,\"owners\":[11,28,51]},{\"tag\":\"mate\",\"ridge\":532,\"a\":13,\"owners\":[72,80,81]},{\"tag\":\"mate\",\"ridge\":532,\"a\":31,\"owners\":[80,81]},{\"tag\":\"mate\",\"ridge\":532,\"a\":57,\"owners\":[72,80]},{\"tag\":\"mate\",\"ridge\":532,\"a\":58,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":265,\"a\":17,\"owners\":[16,34,37,38,47,52,60,63,64]},{\"tag\":\"mate\",\"ridge\":392,\"a\":16,\"owners\":[77,82]},{\"tag\":\"mate\",\"ridge\":392,\"a\":38,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":392,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":392,\"a\":64,\"owners\":[77,82]},{\"tag\":\"mate\",\"ridge\":392,\"a\":65,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":769,\"a\":17,\"owners\":[20,58,59,68,69]},{\"tag\":\"mate\",\"ridge\":776,\"a\":17,\"owners\":[80,82]},{\"tag\":\"mate\",\"ridge\":776,\"a\":62,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":776,\"a\":65,\"owners\":[80]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[18,20,47]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[19,20,47]},{\"tag\":\"mate\",\"ridge\":321,\"a\":45,\"owners\":[18,52,56,59,63,68]},{\"tag\":\"mate\",\"ridge\":336,\"a\":67,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":336,\"a\":79,\"owners\":[18,56,68,81]},{\"tag\":\"mate\",\"ridge\":400,\"a\":43,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":282,\"a\":34,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":538,\"a\":72,\"owners\":[35]},{\"tag\":\"mate\",\"ridge\":330,\"a\":37,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":284,\"a\":80,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":332,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":180,\"a\":55,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":836,\"a\":59,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":836,\"a\":81,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":664,\"a\":61,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":664,\"a\":82,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":360,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":240,\"a\":66,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":480,\"a\":70,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":59,\"full_literals\":[-35,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":81,\"full_literals\":[-55,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-50,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":78,\"full_literals\":[-52,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":79,\"full_literals\":[-53,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":61,\"full_literals\":[-37,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":82,\"full_literals\":[-56,62]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-62,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-60,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-66,-68,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-65,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[11,13,28,31,48,51,53,57,58,59,72,80,81]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[16,17,34,37,38,47,52,53,60,62,63,64,65,77,80,82]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[11,17,28,35,48,51,53,61,62,65,72,80,82]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[9,15,24,32,40,44,50,55,64,66,70,74,76,78]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[16,19,38,43,45,60,64,65,67,69,70,77,79,82]}]}"
  "97 3 4 13 14 28 30 33 34 35 48 54 55 0 37 92 0\n98 6 7 17 20 25 30 40 41 51 54 56 0 63 65 48 53 71 93 0\n99 3 7 13 18 28 30 37 41 48 54 56 0 37 53 94 0\n100 2 5 11 15 21 23 27 31 40 42 49 50 52 0 73 95 0\n101 6 9 20 22 24 40 41 43 45 51 53 56 0 48 73 96 0\n102 -18 0 1 3 5 12 14 20 50 47 46 49 52 98 0\n103 -48 0 102 62 0\n104 -30 0 103 39 0\n105 -34 0 103 44 0\n106 54 55 13 28 0 103 105 104 67 42 43 35 41 97 0\n107 55 13 28 0 53 102 105 71 65 58 67 106 15 16 17 21 40 64 50 47 60 46 49 32 9 10 51 55 56 57 59 101 0\n108 37 56 3 13 28 41 54 0 102 37 104 103 99 33 0\n109 37 13 28 0 103 107 19 35 54 70 108 0\n110 51 53 52 50 -7 -37 25 0 71 48 65 63 72 66 11 8 7 6 61 28 45 22 23 24 25 27 26 29 31 30 100 0\n111 13 28 0 91 103 107 18 19 68 75 35 74 82 81 83 90 88 109 34 69 79 80 85 86 89 84 76 77 13 87 110 78 0\n112 -13 0 2 36 64 0\n113 28 0 112 111 0\n114 -25 0 113 4 0\n115 54 0 113 103 38 0\n116 0 115 114 64 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00017.record057
