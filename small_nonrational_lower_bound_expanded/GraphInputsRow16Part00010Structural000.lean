module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00010Data
public import GraphInputsRow16Part00010Frames
public import GraphInputsRow16Part00010Leaves
public import GraphInputsRow16Part00010Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record008
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 7696715612160, (certNat% 3), 45035996273704960, (certNat% 4)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9007199221186560, (certNat% 5), (certNat% 6), 27021597764222976, (certNat% 7)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), 1147890139398144, 7142427534032896, (certNat% 3), (certNat% 10)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 7697118265344, (certNat% 12), (certNat% 13), (certNat% 14), 137438953472]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), (certNat% 17), 1147890139398144, (certNat% 18), 2745480534556672, 4504089320751104]
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
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record029
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record029
def vertexColumn : Fields := ⟨10, (certNat% 19)⟩
def kindColumn : Fields := ⟨3, (certNat% 20)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), 13510867601588224, (certNat% 23), 3377708310462464]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 23), 9148005462573056, (certNat% 22), 70369817919488]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 2611340115968, 87962003963904, 3660282798800896]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), (certNat% 29), 895552220823552, 8039637612232704, 9007272806055936, 70369885028352]
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
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record029

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record035
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "bcd28bac58b6c394e2b86e8789e1783ed24b9c54b5c354d2b46d8749d1743dd0f13a4cb3c2e4b52e2b2ac6b26c5b0ef0761cc749c6785d1715c3783d0f23e1a518a62584e0b81e86545294951342d0770350ca384c9382c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db69a49249b69a492492492492492492492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 40), (facetIndex 52), (facetIndex 53)]))
 (.leaf ([(facetIndex 32), (facetIndex 35), (facetIndex 41), (facetIndex 43), (facetIndex 50), (facetIndex 51)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 33), (facetIndex 36), (facetIndex 38), (facetIndex 47), (facetIndex 60), (facetIndex 72)]))
 (.leaf ([(facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 29), (facetIndex 39), (facetIndex 62), (facetIndex 74)]))
 (.leaf ([(facetIndex 31), (facetIndex 42), (facetIndex 44), (facetIndex 46), (facetIndex 48), (facetIndex 49)])))
 (.branch 7
 (.leaf ([(facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 37), (facetIndex 45), (facetIndex 59), (facetIndex 71)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "102fb6d80102edb6c026d57d3488ba211aaz16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 64)]))
 (.branch 2
 (.leaf ([(facetIndex 76)]))
 (.leaf ([(facetIndex 78)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 61), (facetIndex 63)]))
 (.leaf ([(facetIndex 65), (facetIndex 73)])))
 (.branch 6
 (.leaf ([(facetIndex 75)]))
 (.leaf ([(facetIndex 77)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "b1a20000020618z2d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
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
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1, 2]
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [1, 2]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [3]
def grouped3_0022 : List Nat := [3, 4]
def grouped3_0023 : List Nat := [3, 4, 5, 6]
def grouped3_0024 : List Nat := [4]
def grouped3_0025 : List Nat := [5]
def grouped3_0026 : List Nat := [5, 6]
def grouped3_0027 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record035" "{\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record035" 81

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record035" "{\"ridges\":[[22,22],[40,770],[44,42],[46,42],[54,28],[55,28],[63,788],[64,184],[65,840],[67,22],[74,22],[75,22],[75,788]],\"owners\":[[44,42,[23,66,71,76],[7,41,45,46,70]],[46,42,[23,66,70,71,76],[7,41,44,45]],[40,770,[77],[14,49,52,53,73,75]],[54,28,[22,67,68,69],[15,55,56,57,66,78]],[55,28,[22,66,68,69,78],[15,54,56,57,67]],[63,788,[75],[]],[75,788,[63],[]],[64,184,[76,78],[]],[65,840,[77],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record035" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record035\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-7,-3],[-9,-7],[-10,-3],[-11,-10],[-12,-3],[-13,-7],[-13,-10],[-13,-11],[-13,-12],[-17,-7],[-19,-10],[-25,-7],[-27,-13],[-27,-22],[-27,-23],[-33,-10],[-35,-28],[-35,-29],[-35,-31],[-35,-32],[-36,-6],[-36,-12],[-36,-15],[-36,-24],[-36,-33],[-37,-30],[-40,-3],[-40,-36],[-41,-2],[-41,-16],[-42,-30],[-43,-35],[-44,-1],[-44,-32],[-44,-40],[-44,-41],[-45,-10],[-45,-41],[-47,-40],[-47,-41],[-47,-44],[-48,-6],[-48,-12],[-48,-15],[-48,-24],[-48,-28],[-48,-40],[-48,-45],[-49,-5],[-49,-8],[-49,-26],[-49,-31],[-49,-42],[-49,-43],[-50,-3],[-50,-19],[-50,-33],[-50,-36],[-50,-45],[-50,-48],[-51,-4],[-51,-21],[-51,-34],[-51,-46],[-52,-3],[-52,-19],[-52,-33],[-52,-36],[-52,-45],[-52,-48],[-1,-48,-49],[-41,-48,-49],[-18,2,40,45,50],[-20,2,40,44,45,50],[-14,51],[-28,1,41,42,43],[-29,1,40,42,43,52],[-37,49],[-49,37],[-38,50,52],[-39,51],[-53,8,14,26,27],[-54,6,9,15,17,24,25],[-55,4,7,10,12,21,34,46],[-56,28,29,30,31,32],[-57,3,13,36,48],[-58,5,16,18,20,22,23],[-59,40,41,42,43,44],[-60,11,19,33,45],[-61,53],[-61,54],[-62,55],[-62,56],[-63,61],[-63,62],[-64,57],[-64,58],[-65,59],[-65,60],[-66,64],[-66,65],[-67,63],[-67,66],[67],[-68,38],[-69,50],[-50,69],[-70,52],[-52,70],[-71,35,37],[-72,39,47],[-73,49],[-74,51],[-75,69,70],[-70,75],[-69,75],[-76,68,75],[-75,76],[-77,71],[-77,72],[-78,73,74],[-79,77,78],[-80,76,79],[-76,-79,81],[80],[-81]],\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":33,\"b\":29},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":36,\"b\":29},{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":38,\"b\":29},{\"tag\":\"incompatible\",\"a\":39,\"b\":33},{\"tag\":\"incompatible\",\"a\":39,\"b\":36},{\"tag\":\"incompatible\",\"a\":39,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":43,\"b\":33},{\"tag\":\"incompatible\",\"a\":45,\"b\":36},{\"tag\":\"incompatible\",\"a\":51,\"b\":33},{\"tag\":\"incompatible\",\"a\":53,\"b\":39},{\"tag\":\"incompatible\",\"a\":53,\"b\":48},{\"tag\":\"incompatible\",\"a\":53,\"b\":49},{\"tag\":\"incompatible\",\"a\":59,\"b\":36},{\"tag\":\"incompatible\",\"a\":61,\"b\":54},{\"tag\":\"incompatible\",\"a\":61,\"b\":55},{\"tag\":\"incompatible\",\"a\":61,\"b\":57},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":32},{\"tag\":\"incompatible\",\"a\":62,\"b\":38},{\"tag\":\"incompatible\",\"a\":62,\"b\":41},{\"tag\":\"incompatible\",\"a\":62,\"b\":50},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":29},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":67,\"b\":23},{\"tag\":\"incompatible\",\"a\":67,\"b\":42},{\"tag\":\"incompatible\",\"a\":68,\"b\":56},{\"tag\":\"incompatible\",\"a\":69,\"b\":61},{\"tag\":\"incompatible\",\"a\":70,\"b\":22},{\"tag\":\"incompatible\",\"a\":70,\"b\":58},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":71,\"b\":36},{\"tag\":\"incompatible\",\"a\":71,\"b\":67},{\"tag\":\"incompatible\",\"a\":73,\"b\":66},{\"tag\":\"incompatible\",\"a\":73,\"b\":67},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":32},{\"tag\":\"incompatible\",\"a\":74,\"b\":38},{\"tag\":\"incompatible\",\"a\":74,\"b\":41},{\"tag\":\"incompatible\",\"a\":74,\"b\":50},{\"tag\":\"incompatible\",\"a\":74,\"b\":54},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":71},{\"tag\":\"incompatible\",\"a\":75,\"b\":31},{\"tag\":\"incompatible\",\"a\":75,\"b\":34},{\"tag\":\"incompatible\",\"a\":75,\"b\":52},{\"tag\":\"incompatible\",\"a\":75,\"b\":57},{\"tag\":\"incompatible\",\"a\":75,\"b\":68},{\"tag\":\"incompatible\",\"a\":75,\"b\":69},{\"tag\":\"incompatible\",\"a\":76,\"b\":29},{\"tag\":\"incompatible\",\"a\":76,\"b\":45},{\"tag\":\"incompatible\",\"a\":76,\"b\":59},{\"tag\":\"incompatible\",\"a\":76,\"b\":62},{\"tag\":\"incompatible\",\"a\":76,\"b\":71},{\"tag\":\"incompatible\",\"a\":76,\"b\":74},{\"tag\":\"incompatible\",\"a\":77,\"b\":30},{\"tag\":\"incompatible\",\"a\":77,\"b\":47},{\"tag\":\"incompatible\",\"a\":77,\"b\":60},{\"tag\":\"incompatible\",\"a\":77,\"b\":72},{\"tag\":\"incompatible\",\"a\":78,\"b\":29},{\"tag\":\"incompatible\",\"a\":78,\"b\":45},{\"tag\":\"incompatible\",\"a\":78,\"b\":59},{\"tag\":\"incompatible\",\"a\":78,\"b\":62},{\"tag\":\"incompatible\",\"a\":78,\"b\":71},{\"tag\":\"incompatible\",\"a\":78,\"b\":74},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[22,74,75]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[67,74,75]},{\"tag\":\"mate\",\"ridge\":42,\"a\":44,\"owners\":[23,66,71,76]},{\"tag\":\"mate\",\"ridge\":42,\"a\":46,\"owners\":[23,66,70,71,76]},{\"tag\":\"mate\",\"ridge\":770,\"a\":40,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":28,\"a\":54,\"owners\":[22,67,68,69]},{\"tag\":\"mate\",\"ridge\":28,\"a\":55,\"owners\":[22,66,68,69,78]},{\"tag\":\"mate\",\"ridge\":788,\"a\":63,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":788,\"a\":75,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":184,\"a\":64,\"owners\":[76,78]},{\"tag\":\"mate\",\"ridge\":840,\"a\":65,\"owners\":[77]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[34,40,52,53],\"full_literals\":[-53,8,14,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[32,35,41,43,50,51],\"full_literals\":[-54,6,9,15,17,24,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[30,33,36,38,47,60,72],\"full_literals\":[-55,4,7,10,12,21,34,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[54,55,56,57,58],\"full_literals\":[-56,28,29,30,31,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[29,39,62,74],\"full_literals\":[-57,3,13,36,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[31,42,44,46,48,49],\"full_literals\":[-58,5,16,18,20,22,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[66,67,68,69,70],\"full_literals\":[-59,40,41,42,43,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[37,45,59,71],\"full_literals\":[-60,11,19,33,45]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-63,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-67,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-67,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[64],\"full_literals\":[-68,38]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[76],\"full_literals\":[-69,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":76,\"full_literals\":[-50,69]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[78],\"full_literals\":[-70,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":78,\"full_literals\":[-52,70]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[61,63],\"full_literals\":[-71,35,37]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[65,73],\"full_literals\":[-72,39,47]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[75],\"full_literals\":[-73,49]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[77],\"full_literals\":[-74,51]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-75,69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-76,68,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-77,71,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,73,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-80,76,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-76,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "127 63 0 104 102 0\n128 66 0 104 103 0\n129 61 0 127 94 0\n130 62 0 127 95 0\n131 64 0 128 100 0\n132 65 0 128 101 0\n133 53 0 129 90 0\n134 54 0 129 91 0\n135 55 0 130 92 0\n136 56 0 130 93 0\n137 57 0 131 96 0\n138 58 0 131 97 0\n139 59 0 132 98 0\n140 60 0 132 99 0\n141 -13 -51 0 135 64 63 62 61 6 7 9 84 0\n142 -3 -51 0 135 64 63 62 61 1 3 5 84 0\n143 -7 -36 0 134 24 23 21 2 10 12 83 0\n144 -36 -51 0 135 140 64 63 62 61 22 25 143 84 4 11 37 89 0\n145 -10 45 0 140 4 11 16 89 0\n146 -51 0 137 135 134 61 62 63 64 141 142 144 86 42 43 44 45 48 145 84 2 10 12 83 0\n147 -14 0 146 75 0\n148 -39 0 146 81 0\n149 -74 0 146 113 0\n150 -48 -49 52 0 139 136 79 26 54 53 52 46 47 71 72 77 88 85 34 0\n151 -44 -49 52 0 136 79 26 54 53 52 33 34 35 36 77 76 85 0\n152 -40 48 13 0 137 27 28 86 0\n153 -49 75 0 147 133 139 138 116 107 115 109 49 50 51 53 54 82 13 14 15 150 151 152 88 29 30 38 73 74 87 0\n154 -79 0 126 149 148 136 139 124 118 153 78 112 121 122 119 120 110 111 17 18 19 20 32 39 40 41 85 88 31 0\n155 76 0 154 125 123 0\n156 -50 0 140 137 55 56 57 58 59 60 89 86 8 0\n157 -69 0 156 106 0\n158 52 0 156 157 155 108 80 105 114 117 0\n159 -3 0 158 65 0\n160 -19 0 158 66 0\n161 -33 0 158 67 0\n162 -36 0 158 68 0\n163 -45 0 158 69 0\n164 -48 0 158 70 0\n165 11 0 161 140 160 163 89 0\n166 13 0 162 137 164 159 86 0\n167 0 166 165 8 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record035

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record039
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ce334cb31c8f13c36a3a39936338ae1783ecc729aa719366394e72539715556354d70d3362d4b4ad8751d1743d38cd38cd3332e2b86c9b16c3b31d2729c6745c3723c4f2a8560b81ec87118a4a986525454550b41d30ca314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db69249269a6934da4924926d2492492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 31), (facetIndex 40), (facetIndex 41)]))
 (.leaf ([(facetIndex 24), (facetIndex 33), (facetIndex 37), (facetIndex 43), (facetIndex 65)])))
 (.branch 3
 (.leaf ([(facetIndex 25), (facetIndex 32), (facetIndex 64), (facetIndex 66)]))
 (.leaf ([(facetIndex 27), (facetIndex 44), (facetIndex 51), (facetIndex 53), (facetIndex 54)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 30), (facetIndex 47), (facetIndex 48), (facetIndex 56)]))
 (.leaf ([(facetIndex 58), (facetIndex 60), (facetIndex 62), (facetIndex 63)])))
 (.branch 7
 (.leaf ([(facetIndex 36), (facetIndex 42), (facetIndex 46), (facetIndex 61)]))
 (.branch 8
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 45)]))
 (.leaf ([(facetIndex 26), (facetIndex 29)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "2125565050403303004467316000016771204803821z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 49), (facetIndex 55)]))
 (.leaf ([(facetIndex 59), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 69)]))
 (.leaf ([(facetIndex 71)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 50), (facetIndex 52), (facetIndex 57)]))
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 74)])))
 (.branch 7
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 77)]))
 (.branch 8
 (.leaf ([(facetIndex 38), (facetIndex 39)]))
 (.leaf ([(facetIndex 68), (facetIndex 70)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "6665553828100000001040000404000000000077z26;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7, 8]
def grouped2_0008 : List Nat := [7]
def grouped2_0009 : List Nat := [7, 8]
def grouped2_0010 : List Nat := [8]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0022 : List Nat := [5]
def grouped3_0023 : List Nat := [6]
def grouped3_0024 : List Nat := [6, 7, 8]
def grouped3_0025 : List Nat := [7]
def grouped3_0026 : List Nat := [7, 8]
def grouped3_0027 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record039" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record039" 60

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record039" "{\"ridges\":[[9,194],[18,784],[19,769],[31,194],[37,194],[40,194],[41,194],[47,292],[48,552],[54,784],[56,800],[58,552],[60,784],[62,800],[63,784],[63,800],[75,780],[76,564],[77,312]],\"owners\":[[9,194,[67,69,71],[31,37,40,41]],[31,194,[71],[9,37,40,41,67,69]],[37,194,[69],[9,31,40,41,67,71]],[40,194,[67,69],[9,31,37,41,71]],[41,194,[67,71],[9,31,37,40,69]],[47,292,[68,76],[14,30,51,56,72,75]],[48,552,[70,77],[17,36,58,61,62,73,75]],[58,552,[75],[17,36,48,61,62,70,73,77]],[19,769,[18,50,54,60],[56,62]],[18,784,[74,76,77],[54,60,63]],[54,784,[77],[18,60,63,74,76]],[60,784,[76],[18,54,63,74,77]],[63,784,[74],[18,54,60,76,77]],[56,800,[77],[19,62,63,75,76]],[62,800,[76],[19,56,63,75,77]],[63,800,[75],[19,56,62,76,77]],[75,780,[50,74],[]],[76,564,[52,73],[]],[77,312,[57,72],[]]],\"edges\":[[39,[9,31,37,40,41,49,55,59,67,69,71]],[44,[18,19,50,54,56,60,62,63,74,75,76,77]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record039" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record039\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-6,-4],[-6,-5],[-1,25,27,29],[-7,29],[-8,27],[-9,25,27],[-10,25,29],[-11,26,34],[-12,28,35],[-20,33],[-3,2,14,16,22],[-2,32,34,35],[-16,35],[-22,34],[-24,32],[-18,35],[-23,34],[-24,33],[-33,14,32],[-34,15,31],[-35,19,30],[-36,6,11,12,18],[-37,20,22,23,24],[-38,4,5],[-39,36,37],[-40,37],[-41,38],[-42,41],[-43,39],[-43,40,42],[-44,43],[44],[-13,45],[-17,45],[-21,46],[-25,46],[-27,47],[-29,48],[-14,49],[-15,49],[-19,49],[-30,50],[-31,50],[-32,50],[-33,51],[-34,51],[-35,51],[-26,52],[-28,52],[-46,53],[-45,53],[-48,54],[-47,54],[-54,55],[-53,55],[-50,56],[-49,56],[-52,57],[-57,58],[-51,58],[-56,-58,59],[-55,-59,60],[-60],[1,7,8,9,10,13,17,21,25,27,29],[2,3,14,16,18,22,23,24,32,33,34,35]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":30,\"b\":26},{\"tag\":\"incompatible\",\"a\":30,\"b\":29},{\"tag\":\"mate\",\"ridge\":194,\"a\":9,\"owners\":[67,69,71]},{\"tag\":\"mate\",\"ridge\":194,\"a\":31,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":194,\"a\":37,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":194,\"a\":40,\"owners\":[67,69]},{\"tag\":\"mate\",\"ridge\":194,\"a\":41,\"owners\":[67,71]},{\"tag\":\"mate\",\"ridge\":292,\"a\":47,\"owners\":[68,76]},{\"tag\":\"mate\",\"ridge\":552,\"a\":48,\"owners\":[70,77]},{\"tag\":\"mate\",\"ridge\":552,\"a\":58,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":769,\"a\":19,\"owners\":[18,50,54,60]},{\"tag\":\"mate\",\"ridge\":784,\"a\":18,\"owners\":[74,76,77]},{\"tag\":\"mate\",\"ridge\":784,\"a\":54,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":784,\"a\":60,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":784,\"a\":63,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":800,\"a\":56,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":800,\"a\":62,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":800,\"a\":63,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":780,\"a\":75,\"owners\":[50,74]},{\"tag\":\"mate\",\"ridge\":564,\"a\":76,\"owners\":[52,73]},{\"tag\":\"mate\",\"ridge\":312,\"a\":77,\"owners\":[57,72]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[30,47,48,56],\"full_literals\":[-36,6,11,12,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[58,60,62,63],\"full_literals\":[-37,20,22,23,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[26,29],\"full_literals\":[-38,4,5]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-39,36,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-40,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-41,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-42,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-43,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-43,40,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-44,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-13,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":55,\"full_literals\":[-17,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":59,\"full_literals\":[-21,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-25,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-27,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-29,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":50,\"full_literals\":[-14,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":52,\"full_literals\":[-15,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":57,\"full_literals\":[-19,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":72,\"full_literals\":[-30,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":73,\"full_literals\":[-31,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-32,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-33,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":76,\"full_literals\":[-34,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":77,\"full_literals\":[-35,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":68,\"full_literals\":[-26,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":70,\"full_literals\":[-28,52]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-58,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-55,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[9,31,37,40,41,49,55,59,67,69,71]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[18,19,50,54,56,60,62,63,74,75,76,77]}]}"
  "66 43 0 32 31 0\n67 39 0 66 29 0\n68 55 0 54 55 52 53 50 51 38 37 35 36 33 34 4 5 3 6 7 64 0\n69 -59 0 68 63 62 0\n70 56 0 56 57 42 43 44 39 40 41 21 20 12 15 19 13 16 14 17 11 65 0\n71 -58 0 70 69 61 0\n72 -57 0 71 59 0\n73 -51 0 71 60 0\n74 -52 0 72 58 0\n75 -33 0 73 45 0\n76 -34 0 73 46 0\n77 -35 0 73 47 0\n78 -26 0 74 48 0\n79 -28 0 74 49 0\n80 -20 0 75 10 0\n81 -24 0 75 18 0\n82 -22 0 76 14 0\n83 -23 0 76 17 0\n84 -18 0 77 16 0\n85 -11 0 78 76 8 0\n86 -12 0 79 77 9 0\n87 -37 0 83 81 80 82 23 0\n88 -40 0 87 26 0\n89 36 0 87 67 25 0\n90 42 0 88 66 30 0\n91 6 0 89 85 86 84 22 0\n92 41 0 90 28 0\n93 -4 0 91 1 0\n94 -5 0 91 2 0\n95 38 0 92 27 0\n96 0 95 94 93 24 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00010.record039
