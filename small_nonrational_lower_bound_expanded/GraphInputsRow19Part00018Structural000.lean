module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00018Frames
public import GraphInputsRow19Part00018Leaves
public import GraphInputsRow19Part00018Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00018.record077
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "bcb89723ab46b1a8e2b91e0fae15c4e92e745b15c52d68d2b51d2743dd0ec3a8e6358ce354d331ce8b32cab1ad1bc1e8791d4731ca785c3783d0f23c2f0e91607ac1384a90e6854548d0764350c6344c330ac1b81d0705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6926934da49249a4924da49249b492489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 55), (facetIndex 60)]))
 (.leaf ([(facetIndex 23), (facetIndex 25), (facetIndex 49), (facetIndex 52)])))
 (.branch 3
 (.leaf ([(facetIndex 22), (facetIndex 26), (facetIndex 48), (facetIndex 51), (facetIndex 61)]))
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 57), (facetIndex 58)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 30), (facetIndex 40), (facetIndex 41), (facetIndex 43)]))
 (.leaf ([(facetIndex 24), (facetIndex 27), (facetIndex 34), (facetIndex 50), (facetIndex 62)])))
 (.branch 7
 (.leaf ([(facetIndex 39), (facetIndex 42), (facetIndex 44), (facetIndex 47)]))
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 33)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1500d800154ac069a4c0377ff00a8d28z10;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00018.record077" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00018.record077" 33

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00018.record077" "{\"ridges\":[[9,322],[30,322],[32,644],[41,321],[42,224],[43,321],[46,704],[47,322],[54,452],[59,368],[60,704],[66,836],[68,322]],\"owners\":[[41,321,[54,56],[9,30,43,47,59]],[43,321,[54,56],[9,30,41,47,59]],[9,322,[66,68],[30,41,43,47]],[30,322,[68],[9,41,43,47,66]],[47,322,[68],[9,30,41,43,66]],[68,322,[9,30,47,66],[41,43]],[32,644,[],[14,52,55,64,65]],[42,224,[],[17,58,60,67,69]],[46,704,[],[18,55,60,65,69]],[60,704,[65],[18,46,55,69]],[54,452,[],[]],[66,836,[56],[]],[59,368,[68],[]]],\"edges\":[[40,[9,30,41,43,47,54,56,59,66,68]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00018.record077" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00018.record077\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-3,-2],[-5,-2],[-11,-1],[-11,-2],[-13,-2],[-13,-3],[-13,-5],[-16,-3],[-16,-5],[-16,-15],[-19,-16],[-21,-6],[-21,-7],[-8,14,16],[-10,14,16],[-1,20,21],[-2,21],[-13,21],[-21,1,2,13,20],[-4],[-9],[-12],[-18,19],[-14],[-20,16],[-17,21],[-22,12,15,18],[-23,2,7,8,10],[-24,6,9,11,13],[-25,3,4,5],[-26,22],[-27,26],[-28,23],[-29,24,25],[-30,24],[-30,25],[-31,28,30],[-31,29],[-32,30],[-33,27,32],[-33,31],[33],[1,2,8,10,13,14,16,17,20,21]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":31,\"b\":30},{\"tag\":\"incompatible\",\"a\":33,\"b\":30},{\"tag\":\"incompatible\",\"a\":44,\"b\":9},{\"tag\":\"incompatible\",\"a\":44,\"b\":30},{\"tag\":\"incompatible\",\"a\":47,\"b\":30},{\"tag\":\"incompatible\",\"a\":47,\"b\":31},{\"tag\":\"incompatible\",\"a\":47,\"b\":33},{\"tag\":\"incompatible\",\"a\":56,\"b\":31},{\"tag\":\"incompatible\",\"a\":56,\"b\":33},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":68,\"b\":39},{\"tag\":\"incompatible\",\"a\":68,\"b\":40},{\"tag\":\"mate\",\"ridge\":321,\"a\":41,\"owners\":[54,56]},{\"tag\":\"mate\",\"ridge\":321,\"a\":43,\"owners\":[54,56]},{\"tag\":\"mate\",\"ridge\":322,\"a\":9,\"owners\":[66,68]},{\"tag\":\"mate\",\"ridge\":322,\"a\":30,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":322,\"a\":47,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":322,\"a\":68,\"owners\":[9,30,47,66]},{\"tag\":\"mate\",\"ridge\":644,\"a\":32,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":224,\"a\":42,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":704,\"a\":46,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":704,\"a\":60,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":452,\"a\":54,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":836,\"a\":66,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":368,\"a\":59,\"owners\":[68]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[46,55,60],\"full_literals\":[-22,12,15,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[30,40,41,43],\"full_literals\":[-23,2,7,8,10]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[39,42,44,47],\"full_literals\":[-24,6,9,11,13]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[31,32,33],\"full_literals\":[-25,3,4,5]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-26,22,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-27,26,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-28,23,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-29,24,25],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-30,24,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-30,false,25],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-31,28,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-31,false,29],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-32,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-33,27,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-33,false,31],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[9,30,41,43,47,54,56,59,66,68]}]}"
  "44 -22 15 18 0 22 27 0\n45 -24 6 11 13 0 21 29 0\n46 -25 3 5 0 20 30 0\n47 31 0 42 41 0\n48 29 0 47 38 0\n49 1 2 8 10 13 16 17 20 21 0 24 43 0\n50 -16 0 42 8 9 10 11 46 23 36 44 39 31 40 32 0\n51 -8 0 50 24 14 0\n52 -10 0 50 24 15 0\n53 -20 0 50 25 0\n54 21 0 53 50 52 51 17 18 26 16 49 0\n55 -6 0 54 12 0\n56 -7 0 54 13 0\n57 2 13 0 47 55 51 52 56 54 53 19 28 3 33 45 37 35 0\n58 13 0 55 48 57 1 2 4 46 45 34 0\n59 -2 0 58 5 0\n60 -3 0 58 6 0\n61 -5 0 58 7 0\n62 -23 0 59 51 52 56 28 0\n63 -25 0 61 60 46 0\n64 -28 0 62 33 0\n65 -30 0 63 36 0\n66 0 64 65 47 37 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00018.record077_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00018.record077
