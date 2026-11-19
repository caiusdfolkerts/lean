module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00070Data
public import GraphInputsRow26Part00070Frames
public import GraphInputsRow26Part00070Leaves
public import GraphInputsRow26Part00070Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record012
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 4035333121476919296, 1017736255766528, 575334859912773632]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record012_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f34a9695a2eb46959562d876c3a8e63a2e4b8ae8791e2783ed2659564b9d1655554b51d70da358d8b52d2b61d4749d0f74394d532cc73c2e8b62e4b52e2b4ae1b46c9b16f07a1d8731e2749c6785d1725e0f43c8f0bc1f2a83a91946298560d8a90e645514a51543590d4328c530ce0b42c8b0ac1b81d0721c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db49249b6da6da6da4924db6d36d2492492492492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 38), (facetIndex 71), (facetIndex 73), (facetIndex 74), (facetIndex 75)]))
 (.branch 2
 (.leaf ([(facetIndex 90), (facetIndex 92), (facetIndex 93), (facetIndex 94)]))
 (.leaf ([(facetIndex 31), (facetIndex 57), (facetIndex 61), (facetIndex 65), (facetIndex 72), (facetIndex 76)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 80), (facetIndex 84), (facetIndex 91), (facetIndex 95)]))
 (.leaf ([(facetIndex 45), (facetIndex 56), (facetIndex 58), (facetIndex 59), (facetIndex 60)])))
 (.branch 6
 (.leaf ([(facetIndex 30), (facetIndex 32), (facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 44)]))
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "649640003003002002000010014914db6db6da5b6da2db6d54z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 79)]))
 (.leaf ([(facetIndex 96), (facetIndex 97), (facetIndex 98)])))
 (.branch 3
 (.leaf ([(facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 70)]))
 (.branch 4
 (.leaf ([(facetIndex 81), (facetIndex 82), (facetIndex 83), (facetIndex 85), (facetIndex 86), (facetIndex 87), (facetIndex 88), (facetIndex 89)]))
 (.leaf ([(facetIndex 99)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "84900001b6d86d800000009248248z2e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [1, 2]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [3]
def grouped2_0007 : List Nat := [3, 4]
def grouped2_0008 : List Nat := [3, 4, 5, 6]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [0, 1]
def grouped3_0015 : List Nat := [2]
def grouped3_0016 : List Nat := [2, 3, 4]
def grouped3_0017 : List Nat := [3]
def grouped3_0018 : List Nat := [3, 4]
def grouped3_0019 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record009" 48

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record009" "{\"ridges\":[[66,300],[67,556]],\"owners\":[[66,300,[85],[]],[67,556,[86],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-2,-1],[-3,-2],[-4,-2],[-5,-2],[-6,-2],[-7,-2],[-8,-2],[-9,-2],[-10,-2],[-11,-2],[-12,-2],[-13,-2],[-14,-2],[-18,-16],[-19,-16],[-20,-18],[-20,-19],[-23,-16],[-23,-20],[-24,-16],[-24,-20],[-25,-16],[-25,-20],[-28,-17],[-28,-18],[-28,-19],[-28,-21],[-28,-22],[-28,-23],[-28,-24],[-28,-25],[-29,-17],[-29,-18],[-29,-19],[-29,-21],[-29,-22],[-29,-23],[-29,-24],[-29,-25],[-32,-15],[-32,-17],[-32,-26],[-32,-27],[-32,-30],[-32,-31],[-33,-15],[-33,-17],[-33,-26],[-33,-27],[-33,-30],[-33,-31],[-34,-2],[-34,-15],[-34,-16],[-34,-20],[-34,-26],[-34,-27],[-21,30],[-22,31],[-35,2,15,16,20,26,27],[-36,28,29,32,33],[-37,1,3,4,5,6,7,8,9,10,11,12,13,14],[-38,35],[-39,38],[-40,36],[-41,37],[-42,40],[-42,41],[-43,39],[-43,42],[43],[-44,17,18,19,21,22,23,24,25],[-45,34],[-46,45],[-47,44,46],[-48,47],[48]],\"atoms\":[{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":31,\"b\":30},{\"tag\":\"incompatible\",\"a\":32,\"b\":31},{\"tag\":\"incompatible\",\"a\":33,\"b\":31},{\"tag\":\"incompatible\",\"a\":34,\"b\":31},{\"tag\":\"incompatible\",\"a\":35,\"b\":31},{\"tag\":\"incompatible\",\"a\":36,\"b\":31},{\"tag\":\"incompatible\",\"a\":37,\"b\":31},{\"tag\":\"incompatible\",\"a\":39,\"b\":31},{\"tag\":\"incompatible\",\"a\":40,\"b\":31},{\"tag\":\"incompatible\",\"a\":41,\"b\":31},{\"tag\":\"incompatible\",\"a\":42,\"b\":31},{\"tag\":\"incompatible\",\"a\":43,\"b\":31},{\"tag\":\"incompatible\",\"a\":44,\"b\":31},{\"tag\":\"incompatible\",\"a\":63,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":65,\"b\":63},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":61},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":69,\"b\":61},{\"tag\":\"incompatible\",\"a\":69,\"b\":65},{\"tag\":\"incompatible\",\"a\":70,\"b\":61},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":80,\"b\":62},{\"tag\":\"incompatible\",\"a\":80,\"b\":63},{\"tag\":\"incompatible\",\"a\":80,\"b\":64},{\"tag\":\"incompatible\",\"a\":80,\"b\":66},{\"tag\":\"incompatible\",\"a\":80,\"b\":67},{\"tag\":\"incompatible\",\"a\":80,\"b\":68},{\"tag\":\"incompatible\",\"a\":80,\"b\":69},{\"tag\":\"incompatible\",\"a\":80,\"b\":70},{\"tag\":\"incompatible\",\"a\":84,\"b\":62},{\"tag\":\"incompatible\",\"a\":84,\"b\":63},{\"tag\":\"incompatible\",\"a\":84,\"b\":64},{\"tag\":\"incompatible\",\"a\":84,\"b\":66},{\"tag\":\"incompatible\",\"a\":84,\"b\":67},{\"tag\":\"incompatible\",\"a\":84,\"b\":68},{\"tag\":\"incompatible\",\"a\":84,\"b\":69},{\"tag\":\"incompatible\",\"a\":84,\"b\":70},{\"tag\":\"incompatible\",\"a\":91,\"b\":57},{\"tag\":\"incompatible\",\"a\":91,\"b\":62},{\"tag\":\"incompatible\",\"a\":91,\"b\":72},{\"tag\":\"incompatible\",\"a\":91,\"b\":76},{\"tag\":\"incompatible\",\"a\":91,\"b\":85},{\"tag\":\"incompatible\",\"a\":91,\"b\":86},{\"tag\":\"incompatible\",\"a\":95,\"b\":57},{\"tag\":\"incompatible\",\"a\":95,\"b\":62},{\"tag\":\"incompatible\",\"a\":95,\"b\":72},{\"tag\":\"incompatible\",\"a\":95,\"b\":76},{\"tag\":\"incompatible\",\"a\":95,\"b\":85},{\"tag\":\"incompatible\",\"a\":95,\"b\":86},{\"tag\":\"incompatible\",\"a\":99,\"b\":31},{\"tag\":\"incompatible\",\"a\":99,\"b\":57},{\"tag\":\"incompatible\",\"a\":99,\"b\":61},{\"tag\":\"incompatible\",\"a\":99,\"b\":65},{\"tag\":\"incompatible\",\"a\":99,\"b\":72},{\"tag\":\"incompatible\",\"a\":99,\"b\":76},{\"tag\":\"mate\",\"ridge\":300,\"a\":66,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":556,\"a\":67,\"owners\":[86]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[31,57,61,65,72,76],\"full_literals\":[-35,2,15,16,20,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[80,84,91,95],\"full_literals\":[-36,28,29,32,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[30,32,33,34,35,36,37,39,40,41,42,43,44],\"full_literals\":[-37,1,3,4,5,6,7,8,9,10,11,12,13,14]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-42,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-42,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-43,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-43,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[62,63,64,66,67,68,69,70],\"full_literals\":[-44,17,18,19,21,22,23,24,25]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[99],\"full_literals\":[-45,34]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true}]}"
  "78 39 0 71 69 0\n79 42 0 71 70 0\n80 38 0 78 64 0\n81 40 0 79 67 0\n82 41 0 79 68 0\n83 35 0 80 63 0\n84 36 0 81 65 0\n85 37 0 82 66 0\n86 47 0 77 76 0\n87 -34 0 83 52 53 54 55 56 57 60 0\n88 -45 0 87 73 0\n89 -46 0 88 74 0\n90 44 0 89 86 75 0\n91 -29 0 90 32 33 34 35 36 37 38 39 72 0\n92 -20 -32 0 90 45 59 44 58 41 16 17 19 21 23 72 0\n93 -32 2 0 83 90 40 41 42 43 44 45 58 59 92 60 14 15 18 20 22 72 0\n94 -28 0 90 24 25 26 27 28 29 30 31 72 0\n95 -16 -33 0 90 51 59 50 58 47 14 15 18 20 22 72 0\n96 2 0 91 84 94 83 90 93 61 46 47 48 49 50 51 58 59 95 60 16 17 19 21 23 72 0\n97 -1 0 96 1 0\n98 -3 0 96 2 0\n99 -4 0 96 3 0\n100 -5 0 96 4 0\n101 -6 0 96 5 0\n102 -7 0 96 6 0\n103 -8 0 96 7 0\n104 -9 0 96 8 0\n105 -10 0 96 9 0\n106 -11 0 96 10 0\n107 -12 0 96 11 0\n108 -13 0 96 12 0\n109 -14 0 96 13 0\n110 0 108 109 85 97 100 99 98 101 102 103 104 105 106 107 62 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record027
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5e2e49d0f49b0ec1f1723c9aa5a8ea5693a1ea563591e17ae1cc6713c5a99a4e94e479b16a5994e5954d58d4b51d64d3362d2b46d4745d0f5a338e5334d332cc7362ccb4acab1ad1b16c3b91cc785d1725c5743c4f07e703a254330ca318562384e8c5314a4a98548d44d0b22c8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b4da6db69b6934d269a4db6d34db4d36db6da6d249a6da492491249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 55), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 35), (facetIndex 63), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 22), (facetIndex 24), (facetIndex 28), (facetIndex 71), (facetIndex 73)]))
 (.leaf ([(facetIndex 57), (facetIndex 74), (facetIndex 87)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 21), (facetIndex 25), (facetIndex 26), (facetIndex 27)]))
 (.leaf ([(facetIndex 34), (facetIndex 40), (facetIndex 78)])))
 (.branch 7
 (.leaf ([(facetIndex 23), (facetIndex 32), (facetIndex 37)]))
 (.leaf ([(facetIndex 36), (facetIndex 49), (facetIndex 51), (facetIndex 64), (facetIndex 84)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6070001400d0400047200018000e38000005037346002922caz10;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027_matrix_checked

def leafCount : Nat := 1
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 5), (facetIndex 6), (facetIndex 13), (facetIndex 23), (facetIndex 27), (facetIndex 61), (facetIndex 66), (facetIndex 69), (facetIndex 70), (facetIndex 73), (facetIndex 77), (facetIndex 78), (facetIndex 87), (facetIndex 89)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.leaf (leaf0000))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record027" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record027" 88

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record027" "{\"ridges\":[[0,14],[2,7],[9,296],[10,304],[12,70],[23,7],[23,14],[27,7],[28,7],[28,70],[28,131],[32,274],[33,104],[35,296],[38,82],[39,178],[40,304],[41,82],[43,99],[44,418],[49,13],[51,76],[52,585],[55,517],[57,517],[63,304],[64,161],[65,104],[66,137],[66,296],[67,209],[68,545],[69,273],[69,304],[69,545],[73,134],[73,194],[74,70],[74,82],[77,82],[79,354],[81,82],[82,82],[84,104],[84,224],[85,556],[87,580],[87,608],[89,104],[89,344]],\"owners\":[[49,13,[0,21,22,23,46,47,52],[6,45,48,50,51]],[0,14,[12,13,71,72],[21,23]],[23,14,[12,13,71],[0,21,72]],[28,131,[3,34,37,39,44],[2,25,36,41,43]],[73,134,[2,13],[15,25]],[66,137,[3,6,36,51],[8,37,64]],[69,273,[5,26,32,47],[10,63]],[32,274,[82],[5,26,40,72,76,77]],[55,517,[29,52,61],[7,27,50,57,59,60]],[57,517,[50,60],[7,27,29,52,55,59,61]],[64,161,[39,44,54,60],[8,34,43,49,58,66,67,70]],[9,296,[76,79,80,89],[35,63,66]],[35,296,[89],[9,63,66,76,79,80]],[66,296,[76,79,89],[9,35,63,80]],[10,304,[76,82,89],[40,63,69]],[40,304,[89],[10,63,69,76,82]],[63,304,[82],[10,40,69,76,89]],[69,304,[76,82,89],[10,40,63]],[68,545,[50,60],[11,55,59,65,69,70]],[69,545,[50,59,60,65,70],[11,55,68]],[51,76,[12,71,83,85],[17,22,46,48,52,84]],[73,194,[16,36,43,78],[15,28,41,81]],[87,580,[29,52,61],[18,57,59,74,85,88]],[84,224,[43,67,70,81],[19,58,64,78,86,88]],[87,608,[65,70],[20,59,68,85,88]],[43,99,[33,38],[]],[39,178,[81],[]],[67,209,[41,56],[]],[44,418,[80],[]],[85,556,[50],[]],[52,585,[65],[]],[89,344,[77],[]],[79,354,[82],[]]],\"edges\":[[37,[9,10,35,40,44,63,66,69,76,79,80,82,89]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record027" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record027\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-3],[-13,-12],[-15,-13],[-16,-13],[-17,-14],[-18,-9],[-18,-12],[-19,-17],[-22,-13],[-23,-13],[-23,-22],[-24,-12],[-24,-13],[-24,-18],[-24,-19],[-25,-12],[-25,-23],[-25,-24],[-28,-23],[-30,-18],[-34,-22],[-35,-34],[-36,-12],[-36,-18],[-36,-19],[-36,-22],[-37,-18],[-37,-24],[-37,-36],[-39,-34],[-39,-38],[-41,-17],[-41,-24],[-41,-36],[-41,-39],[-43,-34],[-43,-39],[-44,-24],[-44,-36],[-46,-18],[-46,-19],[-46,-22],[-46,-37],[-46,-41],[-46,-44],[-48,-21],[-48,-22],[-48,-25],[-48,-31],[-48,-34],[-48,-35],[-48,-46],[-48,-47],[-49,-41],[-50,-12],[-50,-14],[-50,-18],[-50,-36],[-50,-41],[-50,-46],[-51,-26],[-51,-28],[-51,-45],[-52,-12],[-52,-14],[-52,-18],[-52,-24],[-52,-36],[-52,-41],[-53,-45],[-55,-8],[-56,-14],[-56,-17],[-56,-40],[-56,-53],[-56,-55],[-57,-11],[-57,-22],[-57,-27],[-57,-53],[-59,-23],[-59,-36],[-59,-46],[-59,-57],[-61,-22],[-61,-48],[-61,-59],[-63,-22],[-63,-27],[-63,-30],[-63,-31],[-63,-59],[-63,-62],[-64,-57],[-65,-10],[-65,-35],[-65,-39],[-65,-42],[-65,-43],[-65,-59],[-67,-34],[-67,-39],[-67,-50],[-67,-65],[-68,-11],[-68,-20],[-68,-32],[-68,-33],[-68,-45],[-68,-53],[-68,-54],[-2,-13,-17],[-13,-17,-18],[-34,1,11,12,13,32,33,37],[-1,8,9,53,54],[-13,8,9,53],[-18,3,22,25,27,31],[-55,2,9],[-48,3,5,24,36],[-51,4,16,20,33],[-20,63],[-39,19,37,44],[-41,35,43],[-46,27,31,38,43],[-6,57,60,61,68],[-23,68],[-48,57,60,68],[-7,57,63,68],[-28,68],[-45,63],[-51,57,63,68],[-50,35,43],[-51,35,42,43,47,52],[-8,-18,-56],[-36,8,53,64,66],[-26,-56,-58],[-29,-56,-58],[-29,-56,-63],[-56,-58,-62],[-55,10,24,30,59],[-67,19,37,44],[-21,-65,-68],[-47,-65,-68],[-65,30,49,52,62],[-67,47,52],[-30,21,26],[-27,62],[-49,29,40],[-31,61],[-66,35],[-37,47],[-68,58],[-60,63],[-69,39,50,51],[-70,23,45,48],[-71,12,14,18,53,55],[-72,41,56,67],[-73,11,15,16,17],[-74,22,28,59],[-75,13,20,25],[-76,24,34,36,46,65],[-77,69],[-77,70],[-78,71,72],[-79,71],[-79,72],[-80,77,79],[-81,77],[-80,78],[-81,79],[-82,73,74],[-83,73],[-83,74],[-84,75,76],[-85,75],[-85,76],[-86,82],[-86,83,85],[-87,83],[-86,84],[-87,85],[-88,80],[-88,81,87],[-88,86],[88],[-4,-5,-9,-13,-17,-44,-48,-51,-52,-55,-58,-59,-67,-68],[6,7,23,28,31,45,48,51,57,60,61,63,68]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":23,\"b\":3},{\"tag\":\"incompatible\",\"a\":23,\"b\":22},{\"tag\":\"incompatible\",\"a\":25,\"b\":23},{\"tag\":\"incompatible\",\"a\":26,\"b\":23},{\"tag\":\"incompatible\",\"a\":27,\"b\":24},{\"tag\":\"incompatible\",\"a\":28,\"b\":13},{\"tag\":\"incompatible\",\"a\":28,\"b\":22},{\"tag\":\"incompatible\",\"a\":29,\"b\":27},{\"tag\":\"incompatible\",\"a\":34,\"b\":23},{\"tag\":\"incompatible\",\"a\":35,\"b\":23},{\"tag\":\"incompatible\",\"a\":35,\"b\":34},{\"tag\":\"incompatible\",\"a\":36,\"b\":22},{\"tag\":\"incompatible\",\"a\":36,\"b\":23},{\"tag\":\"incompatible\",\"a\":36,\"b\":28},{\"tag\":\"incompatible\",\"a\":36,\"b\":29},{\"tag\":\"incompatible\",\"a\":37,\"b\":22},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":43,\"b\":28},{\"tag\":\"incompatible\",\"a\":49,\"b\":34},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":22},{\"tag\":\"incompatible\",\"a\":51,\"b\":28},{\"tag\":\"incompatible\",\"a\":51,\"b\":29},{\"tag\":\"incompatible\",\"a\":51,\"b\":34},{\"tag\":\"incompatible\",\"a\":52,\"b\":28},{\"tag\":\"incompatible\",\"a\":52,\"b\":36},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":55,\"b\":49},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":57,\"b\":27},{\"tag\":\"incompatible\",\"a\":57,\"b\":36},{\"tag\":\"incompatible\",\"a\":57,\"b\":51},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":60,\"b\":49},{\"tag\":\"incompatible\",\"a\":60,\"b\":55},{\"tag\":\"incompatible\",\"a\":61,\"b\":36},{\"tag\":\"incompatible\",\"a\":61,\"b\":51},{\"tag\":\"incompatible\",\"a\":64,\"b\":28},{\"tag\":\"incompatible\",\"a\":64,\"b\":29},{\"tag\":\"incompatible\",\"a\":64,\"b\":34},{\"tag\":\"incompatible\",\"a\":64,\"b\":52},{\"tag\":\"incompatible\",\"a\":64,\"b\":57},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":33},{\"tag\":\"incompatible\",\"a\":66,\"b\":34},{\"tag\":\"incompatible\",\"a\":66,\"b\":37},{\"tag\":\"incompatible\",\"a\":66,\"b\":44},{\"tag\":\"incompatible\",\"a\":66,\"b\":49},{\"tag\":\"incompatible\",\"a\":66,\"b\":50},{\"tag\":\"incompatible\",\"a\":66,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":57},{\"tag\":\"incompatible\",\"a\":68,\"b\":22},{\"tag\":\"incompatible\",\"a\":68,\"b\":24},{\"tag\":\"incompatible\",\"a\":68,\"b\":28},{\"tag\":\"incompatible\",\"a\":68,\"b\":51},{\"tag\":\"incompatible\",\"a\":68,\"b\":57},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":69,\"b\":38},{\"tag\":\"incompatible\",\"a\":69,\"b\":40},{\"tag\":\"incompatible\",\"a\":69,\"b\":63},{\"tag\":\"incompatible\",\"a\":70,\"b\":22},{\"tag\":\"incompatible\",\"a\":70,\"b\":24},{\"tag\":\"incompatible\",\"a\":70,\"b\":28},{\"tag\":\"incompatible\",\"a\":70,\"b\":36},{\"tag\":\"incompatible\",\"a\":70,\"b\":51},{\"tag\":\"incompatible\",\"a\":70,\"b\":57},{\"tag\":\"incompatible\",\"a\":71,\"b\":63},{\"tag\":\"incompatible\",\"a\":73,\"b\":12},{\"tag\":\"incompatible\",\"a\":74,\"b\":24},{\"tag\":\"incompatible\",\"a\":74,\"b\":27},{\"tag\":\"incompatible\",\"a\":74,\"b\":56},{\"tag\":\"incompatible\",\"a\":74,\"b\":71},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":76,\"b\":21},{\"tag\":\"incompatible\",\"a\":76,\"b\":34},{\"tag\":\"incompatible\",\"a\":76,\"b\":39},{\"tag\":\"incompatible\",\"a\":76,\"b\":71},{\"tag\":\"incompatible\",\"a\":78,\"b\":35},{\"tag\":\"incompatible\",\"a\":78,\"b\":51},{\"tag\":\"incompatible\",\"a\":78,\"b\":64},{\"tag\":\"incompatible\",\"a\":78,\"b\":76},{\"tag\":\"incompatible\",\"a\":80,\"b\":34},{\"tag\":\"incompatible\",\"a\":80,\"b\":66},{\"tag\":\"incompatible\",\"a\":80,\"b\":78},{\"tag\":\"incompatible\",\"a\":82,\"b\":34},{\"tag\":\"incompatible\",\"a\":82,\"b\":39},{\"tag\":\"incompatible\",\"a\":82,\"b\":43},{\"tag\":\"incompatible\",\"a\":82,\"b\":44},{\"tag\":\"incompatible\",\"a\":82,\"b\":78},{\"tag\":\"incompatible\",\"a\":82,\"b\":81},{\"tag\":\"incompatible\",\"a\":83,\"b\":76},{\"tag\":\"incompatible\",\"a\":84,\"b\":16},{\"tag\":\"incompatible\",\"a\":84,\"b\":50},{\"tag\":\"incompatible\",\"a\":84,\"b\":55},{\"tag\":\"incompatible\",\"a\":84,\"b\":59},{\"tag\":\"incompatible\",\"a\":84,\"b\":60},{\"tag\":\"incompatible\",\"a\":84,\"b\":78},{\"tag\":\"incompatible\",\"a\":87,\"b\":49},{\"tag\":\"incompatible\",\"a\":87,\"b\":55},{\"tag\":\"incompatible\",\"a\":87,\"b\":68},{\"tag\":\"incompatible\",\"a\":87,\"b\":84},{\"tag\":\"incompatible\",\"a\":89,\"b\":21},{\"tag\":\"incompatible\",\"a\":89,\"b\":32},{\"tag\":\"incompatible\",\"a\":89,\"b\":46},{\"tag\":\"incompatible\",\"a\":89,\"b\":47},{\"tag\":\"incompatible\",\"a\":89,\"b\":63},{\"tag\":\"incompatible\",\"a\":89,\"b\":71},{\"tag\":\"incompatible\",\"a\":89,\"b\":72},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[2,23,27]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[23,27,28]},{\"tag\":\"mate\",\"ridge\":13,\"a\":49,\"owners\":[0,21,22,23,46,47,52]},{\"tag\":\"mate\",\"ridge\":14,\"a\":0,\"owners\":[12,13,71,72]},{\"tag\":\"mate\",\"ridge\":14,\"a\":23,\"owners\":[12,13,71]},{\"tag\":\"mate\",\"ridge\":131,\"a\":28,\"owners\":[3,34,37,39,44]},{\"tag\":\"mate\",\"ridge\":134,\"a\":73,\"owners\":[2,13]},{\"tag\":\"mate\",\"ridge\":137,\"a\":66,\"owners\":[3,6,36,51]},{\"tag\":\"mate\",\"ridge\":273,\"a\":69,\"owners\":[5,26,32,47]},{\"tag\":\"mate\",\"ridge\":274,\"a\":32,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":517,\"a\":55,\"owners\":[29,52,61]},{\"tag\":\"mate\",\"ridge\":517,\"a\":57,\"owners\":[50,60]},{\"tag\":\"mate\",\"ridge\":161,\"a\":64,\"owners\":[39,44,54,60]},{\"tag\":\"mate\",\"ridge\":296,\"a\":9,\"owners\":[76,79,80,89]},{\"tag\":\"mate\",\"ridge\":296,\"a\":35,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":296,\"a\":66,\"owners\":[76,79,89]},{\"tag\":\"mate\",\"ridge\":304,\"a\":10,\"owners\":[76,82,89]},{\"tag\":\"mate\",\"ridge\":304,\"a\":40,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":304,\"a\":63,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":304,\"a\":69,\"owners\":[76,82,89]},{\"tag\":\"mate\",\"ridge\":545,\"a\":68,\"owners\":[50,60]},{\"tag\":\"mate\",\"ridge\":545,\"a\":69,\"owners\":[50,59,60,65,70]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[12,28,74]},{\"tag\":\"mate\",\"ridge\":76,\"a\":51,\"owners\":[12,71,83,85]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[38,74,77]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[41,74,77]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[41,74,82]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[74,77,81]},{\"tag\":\"mate\",\"ridge\":194,\"a\":73,\"owners\":[16,36,43,78]},{\"tag\":\"mate\",\"ridge\":580,\"a\":87,\"owners\":[29,52,61]},{\"tag\":\"three\",\"ridge\":104,\"vertices\":[33,84,89]},{\"tag\":\"three\",\"ridge\":104,\"vertices\":[65,84,89]},{\"tag\":\"mate\",\"ridge\":224,\"a\":84,\"owners\":[43,67,70,81]},{\"tag\":\"mate\",\"ridge\":608,\"a\":87,\"owners\":[65,70]},{\"tag\":\"mate\",\"ridge\":99,\"a\":43,\"owners\":[33,38]},{\"tag\":\"mate\",\"ridge\":178,\"a\":39,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":209,\"a\":67,\"owners\":[41,56]},{\"tag\":\"mate\",\"ridge\":418,\"a\":44,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":556,\"a\":85,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":585,\"a\":52,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":344,\"a\":89,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":354,\"a\":79,\"owners\":[82]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[55,68,69],\"full_literals\":[-69,39,50,51]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[35,63,66],\"full_literals\":[-70,23,45,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[22,24,28,71,73],\"full_literals\":[-71,12,14,18,53,55]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[57,74,87],\"full_literals\":[-72,41,56,67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[21,25,26,27],\"full_literals\":[-73,11,15,16,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[34,40,78],\"full_literals\":[-74,22,28,59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[23,32,37],\"full_literals\":[-75,13,20,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[36,49,51,64,84],\"full_literals\":[-76,24,34,36,46,65]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-77,69,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,71,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-79,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-80,77,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-81,77,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,false,78],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-81,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-82,73,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-83,73,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-83,false,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-84,75,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-85,75,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,false,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-86,82,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,83,85],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-87,83,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-86,false,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-87,false,85],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-88,80,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-88,81,87],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-88,false,86],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[5,6,13,23,27,61,66,69,70,73,77,78,87,89]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[9,10,35,40,44,63,66,69,76,79,80,82,89]}]}"
  "188 80 0 185 182 0\n189 86 0 185 184 0\n190 78 0 188 169 0\n191 82 0 189 177 0\n192 84 0 189 180 0\n193 28 68 6 7 31 45 48 23 57 60 61 63 0 187 131 0\n194 57 61 63 68 0 149 153 130 129 126 128 125 127 193 0\n195 61 63 68 0 191 189 185 130 121 129 126 149 194 77 78 79 80 84 94 159 173 171 178 179 175 176 183 168 170 163 165 166 155 48 50 51 52 160 150 1 2 3 4 13 117 158 5 32 73 156 157 71 104 135 161 0\n196 63 68 0 185 129 126 130 195 85 86 87 155 159 163 173 168 179 183 0\n197 -67 51 -69 0 102 103 154 0\n198 -24 -56 53 -71 0 76 72 12 14 156 0\n199 -39 -45 68 0 189 185 196 88 129 92 159 173 179 183 168 162 63 197 70 170 166 165 178 176 91 89 30 31 35 37 97 124 157 72 76 198 161 23 24 156 0\n200 -45 68 0 185 196 88 129 92 159 173 179 183 170 166 165 168 162 63 70 197 199 154 55 56 57 59 156 157 76 0\n201 -12 -56 68 0 189 185 74 196 138 148 88 129 92 159 173 179 183 170 165 75 198 168 163 126 200 155 52 50 178 176 93 90 23 64 161 144 0\n202 -56 68 0 189 185 196 88 129 92 159 173 179 183 168 163 126 200 155 52 50 170 165 178 176 93 90 72 74 75 76 138 198 148 201 156 24 66 161 144 0\n203 -41 68 0 189 185 196 88 129 92 159 173 179 183 168 163 126 200 155 52 50 178 176 93 90 33 34 54 69 161 144 0\n204 68 0 189 185 126 129 196 88 92 159 173 178 179 176 183 168 170 163 166 200 155 50 52 53 202 203 157 104 145 67 68 161 0\n205 -11 0 204 105 0\n206 -20 0 204 106 0\n207 -32 0 204 107 0\n208 -33 0 204 108 0\n209 -45 0 204 109 0\n210 -53 0 204 110 0\n211 -54 0 204 111 0\n212 58 0 204 152 0\n213 -24 56 0 206 185 13 15 18 28 33 38 160 141 175 157 181 166 183 170 0\n214 -34 56 0 188 185 209 21 22 30 36 50 101 123 132 157 166 170 167 183 162 163 179 154 155 173 62 81 159 0\n215 -36 56 0 188 185 25 26 29 34 39 58 82 122 141 157 166 170 167 183 162 179 154 173 62 159 0\n216 -46 56 0 188 185 41 42 43 44 45 60 83 122 141 157 166 170 167 183 162 179 154 173 62 159 0\n217 -65 56 0 204 190 188 210 213 95 96 97 98 99 100 104 142 143 123 132 157 166 164 167 162 154 61 133 146 64 65 66 140 156 0\n218 -25 -70 0 209 17 48 155 0\n219 56 0 192 189 185 205 209 210 208 206 204 212 213 214 215 216 217 161 176 174 181 178 183 172 173 168 170 162 163 165 166 218 160 1 2 3 4 9 10 158 155 5 8 32 113 112 53 119 157 156 118 151 197 145 141 62 120 186 159 0\n220 -14 0 219 72 0\n221 -17 0 219 73 0\n222 -40 0 219 74 0\n223 -55 0 219 76 0\n224 -26 0 219 212 136 0\n225 -29 0 219 212 137 0\n226 -62 0 219 212 139 0\n227 -49 0 225 222 148 0\n228 -27 0 226 147 0\n229 -13 -48 25 0 228 221 205 210 220 223 185 49 47 1 2 3 4 117 158 156 172 165 179 170 183 0\n230 -12 24 -76 30 46 34 0 226 227 23 64 161 144 0\n231 -48 25 0 224 206 192 185 219 210 220 223 226 227 46 50 52 146 229 160 174 175 181 183 170 165 198 230 156 24 66 161 144 0\n232 -70 0 209 206 189 218 231 155 10 11 19 81 160 159 175 173 178 0\n233 -77 0 232 163 0\n234 79 0 233 188 167 0\n235 -81 0 233 168 0\n236 71 0 234 165 0\n237 87 0 235 185 183 0\n238 -24 0 236 210 219 198 0\n239 85 0 237 181 0\n240 75 0 239 175 0\n241 76 0 239 176 0\n242 -18 0 219 211 226 227 210 238 241 208 207 205 6 7 20 24 27 40 66 134 115 144 116 161 114 0\n243 12 0 242 223 236 220 210 156 0\n244 -13 0 243 2 0\n245 -25 0 243 16 0\n246 0 244 245 240 206 160 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027.l) :=
(.leaf (⟨0, by decide⟩))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027.g)) :=
(.leaf ([]))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record027
