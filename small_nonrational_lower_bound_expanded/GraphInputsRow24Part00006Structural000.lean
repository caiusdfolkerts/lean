module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00006Data
public import GraphInputsRow24Part00006Frames
public import GraphInputsRow24Part00006Leaves
public import GraphInputsRow24Part00006Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record037
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record037
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 8444249326485504, (certNat% 3), 1879048192, 18016634073513984, (certNat% 4), 67108864]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record037_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record037_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record037_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record037_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record037_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record037_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record037_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record037_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record037_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record037

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e315c1f38ad287ae18b61db0ea398e5386e1783e78789d25591e78569565554b51d70da358d5346d4745d0f783d0dc3a8ce32cf0ba2d8b92d4b1ae1b0ef07a1d8751c6725c5783d0f23c4f0bc72168a60d81ee0471c254916585294354341da0ca318c530ce0b12c1b21c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db69a4db6d26924936926934926d24934924d2692492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 47), (facetIndex 48), (facetIndex 49)]))
 (.leaf ([(facetIndex 36), (facetIndex 58), (facetIndex 65), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 27), (facetIndex 33), (facetIndex 34), (facetIndex 62), (facetIndex 80)]))
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 52), (facetIndex 70)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 32), (facetIndex 39), (facetIndex 41), (facetIndex 53), (facetIndex 67), (facetIndex 72), (facetIndex 82)]))
 (.leaf ([(facetIndex 55), (facetIndex 57), (facetIndex 60), (facetIndex 68), (facetIndex 69)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 54), (facetIndex 61), (facetIndex 73), (facetIndex 79)]))
 (.branch 8
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 40), (facetIndex 42), (facetIndex 43)]))
 (.leaf ([(facetIndex 29)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "40260000064035541100265015056430000033077474001022477862z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 50), (facetIndex 71)]))
 (.leaf ([(facetIndex 35), (facetIndex 56), (facetIndex 63), (facetIndex 64)])))
 (.branch 3
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 86)]))
 (.leaf ([(facetIndex 85)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 38), (facetIndex 44), (facetIndex 59)]))
 (.leaf ([(facetIndex 76), (facetIndex 77), (facetIndex 78)])))
 (.branch 7
 (.leaf ([(facetIndex 81), (facetIndex 84), (facetIndex 87)]))
 (.branch 8
 (.leaf ([(facetIndex 51)]))
 (.leaf ([(facetIndex 83)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "62368060055522000000000110004001000070000004000004001z23;"⟩
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
def grouped2_0009 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7, 8]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8]
def grouped2_0014 : List Nat := [8]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0017 : List Nat := [0, 1, 2, 3]
def grouped3_0019 : List Nat := [1]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [2, 3]
def grouped3_0022 : List Nat := [3]
def grouped3_0023 : List Nat := [4]
def grouped3_0024 : List Nat := [4, 5]
def grouped3_0025 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0026 : List Nat := [5]
def grouped3_0027 : List Nat := [6]
def grouped3_0028 : List Nat := [6, 7, 8]
def grouped3_0029 : List Nat := [7]
def grouped3_0030 : List Nat := [7, 8]
def grouped3_0031 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record000" 64

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record000" "{\"ridges\":[[11,642],[18,328],[21,896],[36,388],[37,642],[42,328],[45,642],[46,776],[49,642],[50,450],[52,642],[52,896],[57,328],[58,388],[64,356],[66,388],[66,896],[68,328],[69,328],[70,896],[71,480],[81,774],[84,394],[87,652]],\"owners\":[[11,642,[77,81,84],[37,45,49,52]],[37,642,[84],[11,45,49,52,77,81]],[45,642,[81],[11,37,49,52,77,84]],[49,642,[77,81,84],[11,37,45,52]],[52,642,[77],[11,37,45,49,81,84]],[36,388,[87],[16,58,65,66,76,81]],[58,388,[81],[16,36,65,66,76,87]],[66,388,[76],[16,36,58,65,81,87]],[18,328,[75,83,86],[42,57,68,69]],[42,328,[86],[18,57,68,69,75,83]],[57,328,[83],[18,42,68,69,75,86]],[68,328,[75,83],[18,42,57,69,86]],[69,328,[75,86],[18,42,57,68,83]],[46,776,[87],[19,60,69,70,78,83,84]],[21,896,[81,84,87],[52,66,70]],[52,896,[87],[21,66,70,81,84]],[66,896,[84],[21,52,70,81,87]],[70,896,[81],[21,52,66,84,87]],[81,774,[38,78],[]],[84,394,[44,76],[]],[50,450,[],[]],[87,652,[59,77],[]],[64,356,[],[]],[71,480,[],[]]],\"edges\":[[40,[18,35,42,50,51,57,63,64,68,69,71,75,83,86]],[43,[11,21,37,45,49,52,59,66,70,77,81,84,87]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-22,-4],[-1,30,32,34],[-7,34],[-11,32],[-13,30,32,34],[-16,30],[-6,36],[-18,32],[-23,29],[-2,28,33,35],[-9,35],[-17,33],[-24,28,33],[-25,28,35],[-12,36],[-3,32,34,36],[-16,36],[-23,34],[-26,32],[-32,8,31],[-34,10,29],[-14],[-36,19,30],[-21],[-27],[-37,6,18,22,23],[-38,11,12,16,26],[-39,4],[-40,37],[-41,38],[-42,40,41],[-43,41],[-44,39],[-45,44],[-46,45],[-47,42],[-47,43,46],[47],[-5,48],[-20,48],[-28,49],[-35,49],[-8,50],[-10,50],[-19,50],[-29,51],[-30,51],[-31,51],[-32,52],[-34,52],[-36,52],[-15,53],[-33,54],[-48,55],[-49,56],[-56,57],[-55,57],[-51,58],[-50,58],[-54,59],[-53,59],[-52,60],[-52,-59,61],[-58,-60,62],[-58,-61,63],[-63,64],[-57,-62,64],[-64],[2,5,9,14,15,17,20,21,24,25,27,28,33,35],[1,3,7,11,13,16,19,23,26,30,32,34,36]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":65,\"b\":29},{\"tag\":\"mate\",\"ridge\":642,\"a\":11,\"owners\":[77,81,84]},{\"tag\":\"mate\",\"ridge\":642,\"a\":37,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":642,\"a\":45,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":642,\"a\":49,\"owners\":[77,81,84]},{\"tag\":\"mate\",\"ridge\":642,\"a\":52,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":388,\"a\":36,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":388,\"a\":58,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":388,\"a\":66,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":328,\"a\":18,\"owners\":[75,83,86]},{\"tag\":\"mate\",\"ridge\":328,\"a\":42,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":328,\"a\":57,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":328,\"a\":68,\"owners\":[75,83]},{\"tag\":\"mate\",\"ridge\":328,\"a\":69,\"owners\":[75,86]},{\"tag\":\"mate\",\"ridge\":776,\"a\":46,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":896,\"a\":21,\"owners\":[81,84,87]},{\"tag\":\"mate\",\"ridge\":896,\"a\":52,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":896,\"a\":66,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":896,\"a\":70,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":774,\"a\":81,\"owners\":[38,78]},{\"tag\":\"mate\",\"ridge\":394,\"a\":84,\"owners\":[44,76]},{\"tag\":\"mate\",\"ridge\":450,\"a\":50,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":652,\"a\":87,\"owners\":[59,77]},{\"tag\":\"mate\",\"ridge\":356,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":480,\"a\":71,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[36,58,65,66],\"full_literals\":[-37,6,18,22,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[45,46,52,70],\"full_literals\":[-38,11,12,16,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[29],\"full_literals\":[-39,4]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-40,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-41,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-42,40,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-46,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-47,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-47,43,46],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":35,\"full_literals\":[-5,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":63,\"full_literals\":[-20,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-28,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":86,\"full_literals\":[-35,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":38,\"full_literals\":[-8,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":44,\"full_literals\":[-10,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":59,\"full_literals\":[-19,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":76,\"full_literals\":[-29,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":77,\"full_literals\":[-30,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-31,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":81,\"full_literals\":[-32,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-34,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-36,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":51,\"full_literals\":[-15,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":83,\"full_literals\":[-33,54]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-58,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-57,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[18,35,42,50,51,57,63,64,68,69,71,75,83,86]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[11,21,37,45,49,52,59,66,70,77,81,84,87]}]}"
  "71 42 0 38 36 0\n72 -63 0 68 66 0\n73 2 5 9 15 17 20 24 25 28 33 35 0 22 24 25 69 0\n74 58 0 58 59 46 47 48 43 44 45 9 21 6 20 23 3 4 16 19 2 5 70 0\n75 -61 0 74 72 65 0\n76 52 0 71 38 49 50 51 4 8 19 18 7 15 17 27 30 32 31 37 29 35 26 34 1 33 28 0\n77 60 0 76 62 0\n78 -59 0 76 75 63 0\n79 62 0 77 74 64 0\n80 -54 0 78 60 0\n81 -53 0 78 61 0\n82 -57 0 79 68 67 0\n83 -33 0 80 53 0\n84 -15 0 81 52 0\n85 -56 0 82 56 0\n86 -55 0 82 57 0\n87 -17 0 83 12 0\n88 -49 0 85 55 0\n89 -48 0 86 54 0\n90 -28 0 88 41 0\n91 -35 0 88 42 0\n92 -5 0 89 39 0\n93 -20 0 89 40 0\n94 -24 0 90 83 13 0\n95 -9 0 91 11 0\n96 -25 0 91 90 14 0\n97 -2 0 91 90 83 10 0\n98 0 97 93 87 95 92 84 94 96 90 83 91 73 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record014
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "15c1f38ad2aaa1eb86718b61d94e1b85e0fb89d26a96a5591e785715a5554b51d54d4b46d4745d0f783d0dc3a8cb31cf0ba2d8b92d4b8acab1ae1bc1e8761d4731c6725d0f13c2f07c5a0e8a615836e0709524590e585514a515435a0ca314c3382c4b0ac1b21c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db4da4da49369249249b6926d249349249a4924d2449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 62), (facetIndex 64)]))
 (.leaf ([(facetIndex 42), (facetIndex 58), (facetIndex 66), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 31), (facetIndex 32), (facetIndex 48), (facetIndex 60), (facetIndex 76)]))
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 61), (facetIndex 63)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 52), (facetIndex 70)]))
 (.leaf ([(facetIndex 27), (facetIndex 47), (facetIndex 71), (facetIndex 72), (facetIndex 75), (facetIndex 79)])))
 (.branch 7
 (.leaf ([(facetIndex 53), (facetIndex 54), (facetIndex 59), (facetIndex 65)]))
 (.branch 8
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 49)]))
 (.leaf ([(facetIndex 29), (facetIndex 38), (facetIndex 39), (facetIndex 43)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "50025005541001603032610006640072544081778800033220825z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 44), (facetIndex 67), (facetIndex 68)]))
 (.branch 2
 (.leaf ([(facetIndex 80), (facetIndex 82)]))
 (.leaf ([(facetIndex 30), (facetIndex 55), (facetIndex 56), (facetIndex 57)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 84)]))
 (.leaf ([(facetIndex 83)])))
 (.branch 6
 (.leaf ([(facetIndex 37), (facetIndex 50), (facetIndex 51)]))
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 81)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "38711b00d8000000000012400b4000000002800008z16;"⟩
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
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6, 7, 8]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1, 2]
def grouped3_0014 : List Nat := [1]
def grouped3_0015 : List Nat := [1, 2]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [3, 4]
def grouped3_0018 : List Nat := [3, 4, 5, 6]
def grouped3_0019 : List Nat := [5]
def grouped3_0020 : List Nat := [5, 6]
def grouped3_0021 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record014" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record014" 52

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record014" "{\"ridges\":[[11,642],[16,388],[19,328],[20,769],[20,776],[21,896],[35,388],[36,642],[37,774],[42,328],[44,394],[45,642],[46,776],[49,642],[50,450],[52,896],[57,300],[58,324],[62,388],[63,388],[64,896],[66,328],[67,424],[69,776],[70,776],[70,896],[74,270],[78,774],[82,394],[84,284]],\"owners\":[[11,642,[78,80,82],[36,45,49,52]],[36,642,[80,82],[11,45,49,52,78]],[45,642,[78],[11,36,49,52,80,82]],[49,642,[78,82],[11,36,45,52,80]],[58,324,[77],[15,34,61,63,74,84]],[16,388,[77,78],[35,62,63,64]],[35,388,[],[16,62,63,64,77,78]],[62,388,[77,78],[16,35,63,64]],[63,388,[78],[16,35,62,64,77]],[19,328,[74,81,84],[42,58,66,69]],[42,328,[84],[19,58,66,69,74,81]],[66,328,[74,81],[19,42,58,69,84]],[20,769,[21,37,51,52,64],[46,69]],[20,776,[81,82],[46,69,70]],[46,776,[],[20,69,70,81,82]],[69,776,[82],[20,46,70,81]],[70,776,[81],[20,46,69,82]],[21,896,[78,82],[52,64,70]],[52,896,[],[21,64,70,78,82]],[64,896,[82],[21,52,70,78]],[70,896,[78],[21,52,64,82]],[74,270,[30],[]],[37,774,[78],[]],[78,774,[37],[]],[44,394,[82],[]],[82,394,[44],[]],[50,450,[77],[]],[84,284,[55],[]],[57,300,[],[]],[67,424,[],[]]],\"edges\":[[28,[19,20,30,42,44,46,55,57,58,66,67,69,70,74,81,82,84]],[42,[16,21,35,44,50,52,62,63,64,67,70,77,78,82]],[43,[11,21,36,45,49,52,64,68,70,78,80,82]],[44,[20,21,37,46,51,52,64,69,70,78,81,82]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record014" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record014\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-27,-11],[-30,-16],[-31,-30],[-33,-30],[-33,-31],[-34,-10],[-34,-29],[-34,-30],[-34,-33],[-1,31,32,34],[-8,32,34],[-12,31],[-14,31,34],[-20,30],[-2,30,31],[-7],[-21,30,31],[-22,31],[-3,29,33,35],[-10,35],[-24,29,33],[-4,5,9,16,17,23],[-4,33,34],[-13],[-27,34],[-28,33],[-5,31,34],[-17],[-23,34],[-28,31],[-29,6],[-9,31],[-31,9],[-11,34],[-34,11],[-15,30],[-35,18],[-19],[-25],[-36,10,20,24,27],[-37,12,13,17,28],[-38,36],[-39,38],[-40,37],[-41,40],[-42,39,41],[42],[-11,43],[-26,43],[-32,44],[-34,44],[-6,45],[-18,45],[-9,46],[-31,47],[-45,48],[-44,48],[-48,49],[-43,49],[-46,-47,50],[-50,51],[-49,-51,52],[-52],[3,4,6,10,11,13,18,19,20,24,25,27,28,29,33,34,35],[2,5,7,11,15,17,21,22,23,25,28,30,31,34],[1,5,8,12,14,17,23,26,28,31,32,34],[4,5,9,13,16,17,23,27,28,31,33,34]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":69,\"b\":44},{\"tag\":\"incompatible\",\"a\":77,\"b\":51},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":78},{\"tag\":\"incompatible\",\"a\":82,\"b\":42},{\"tag\":\"incompatible\",\"a\":82,\"b\":74},{\"tag\":\"incompatible\",\"a\":82,\"b\":77},{\"tag\":\"incompatible\",\"a\":82,\"b\":81},{\"tag\":\"mate\",\"ridge\":642,\"a\":11,\"owners\":[78,80,82]},{\"tag\":\"mate\",\"ridge\":642,\"a\":36,\"owners\":[80,82]},{\"tag\":\"mate\",\"ridge\":642,\"a\":45,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":642,\"a\":49,\"owners\":[78,82]},{\"tag\":\"mate\",\"ridge\":324,\"a\":58,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":388,\"a\":16,\"owners\":[77,78]},{\"tag\":\"mate\",\"ridge\":388,\"a\":35,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":388,\"a\":62,\"owners\":[77,78]},{\"tag\":\"mate\",\"ridge\":388,\"a\":63,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":328,\"a\":19,\"owners\":[74,81,84]},{\"tag\":\"mate\",\"ridge\":328,\"a\":42,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":328,\"a\":66,\"owners\":[74,81]},{\"tag\":\"mate\",\"ridge\":769,\"a\":20,\"owners\":[21,37,51,52,64]},{\"tag\":\"mate\",\"ridge\":776,\"a\":20,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":776,\"a\":46,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":776,\"a\":69,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":776,\"a\":70,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":896,\"a\":21,\"owners\":[78,82]},{\"tag\":\"mate\",\"ridge\":896,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":896,\"a\":64,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":896,\"a\":70,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":270,\"a\":74,\"owners\":[30]},{\"tag\":\"mate\",\"ridge\":774,\"a\":37,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":774,\"a\":78,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":394,\"a\":44,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":394,\"a\":82,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":450,\"a\":50,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":284,\"a\":84,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":300,\"a\":57,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":424,\"a\":67,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[42,58,66,69],\"full_literals\":[-36,10,20,24,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[45,46,52,70],\"full_literals\":[-37,12,13,17,28]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-39,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-41,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-42,39,41],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":44,\"full_literals\":[-11,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":68,\"full_literals\":[-26,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-32,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-34,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":30,\"full_literals\":[-6,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":55,\"full_literals\":[-18,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":37,\"full_literals\":[-9,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":78,\"full_literals\":[-31,47]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-47,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-49,-51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":28,\"owners\":[19,20,30,42,44,46,55,57,58,66,67,69,70,74,81,82,84]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[16,21,35,44,50,52,62,63,64,67,70,77,78,82]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[11,21,36,45,49,52,64,68,70,78,80,82]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[20,21,37,46,51,52,64,69,70,78,81,82]}]}"
  "68 -37 12 28 0 24 28 41 0\n69 3 4 6 10 11 18 20 24 27 28 29 33 34 35 0 24 38 39 64 0\n70 2 5 11 15 21 22 23 28 30 31 34 0 16 28 39 65 0\n71 1 5 8 12 14 23 26 28 31 32 34 0 28 66 0\n72 4 5 9 16 23 27 28 31 33 34 0 24 28 67 0\n73 31 -37 0 12 30 68 0\n74 -31 49 0 58 56 53 37 20 57 51 25 52 31 59 48 3 5 14 23 26 19 21 69 0\n75 49 0 58 59 57 49 50 51 11 29 74 12 30 10 13 27 71 0\n76 -51 0 75 63 62 0\n77 -50 0 76 61 0\n78 30 34 31 0 27 34 29 30 18 15 17 36 70 0\n79 34 31 0 28 32 30 25 29 27 78 2 4 22 72 0\n80 31 0 47 73 44 45 46 43 42 79 6 7 8 9 35 14 21 1 40 0\n81 9 0 80 33 0\n82 47 0 80 55 0\n83 46 0 81 54 0\n84 0 83 82 77 60 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00006.record014_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00006.record014
