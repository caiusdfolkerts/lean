module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00088Frames
public import GraphInputsRow29Part00088Leaves
public import GraphInputsRow29Part00088Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "34c2f07cd28ba1eb46958b61db0e63a4e538ce4b86e4789ed24b91e745954b51d70d6364d534cd4b46d4749dd0e532cc73c2d8b92d4b32d2b1ad1b26e8761d4731e2749c6785d1725e0f2b05c0f0aa1683ac1a46298560d90e2384e0b81e2a4590e705914a5154354348d1342d0770390ca314c3342c8b12c2b06e0741c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "349a49249249249a492492492492492492492492492489249249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 53), (facetIndex 54), (facetIndex 68), (facetIndex 81), (facetIndex 97)])))
 (.branch 3
 (.leaf ([(facetIndex 52), (facetIndex 56), (facetIndex 69), (facetIndex 82), (facetIndex 98)]))
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 78)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 66), (facetIndex 79), (facetIndex 83), (facetIndex 88), (facetIndex 95), (facetIndex 99), (facetIndex 102)]))
 (.leaf ([(facetIndex 47), (facetIndex 67), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 96), (facetIndex 100), (facetIndex 103)])))
 (.branch 7
 (.leaf ([(facetIndex 87), (facetIndex 89), (facetIndex 90), (facetIndex 91), (facetIndex 92), (facetIndex 93), (facetIndex 94)]))
 (.leaf ([(facetIndex 48), (facetIndex 51), (facetIndex 55)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "b0588d9b6db4d4588d8db6db6d1b00000002e4ae4faz23;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 1
 (.leaf ([(facetIndex 85)]))
 (.branch 2
 (.leaf ([(facetIndex 101)]))
 (.leaf ([(facetIndex 104)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "204z32;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 3
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7]
def grouped2_0010 : List Nat := [7]
def grouped3_0011 : List Nat := [0]
def grouped3_0013 : List Nat := [1]
def grouped3_0014 : List Nat := [1, 2]
def grouped3_0015 : List Nat := [2]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record001" 21

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record001" "{\"ridges\":[],\"owners\":[],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-3,-1],[-3,-2],[-4,-3],[-5,-1],[-5,-2],[-5,-4],[-9,-6],[-9,-7],[-9,-8],[-10,-6],[-10,-7],[-10,-8],[-11,3,5,6,7,8],[-12,1,2,4],[-13,11],[-14,13],[-15,12],[-16,15],[-17,14],[-17,16],[17],[-18,9],[-19,10],[-20,18,19],[-21,20],[21]],\"atoms\":[{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":52,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":48},{\"tag\":\"incompatible\",\"a\":56,\"b\":51},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":101,\"b\":69},{\"tag\":\"incompatible\",\"a\":101,\"b\":82},{\"tag\":\"incompatible\",\"a\":101,\"b\":98},{\"tag\":\"incompatible\",\"a\":104,\"b\":69},{\"tag\":\"incompatible\",\"a\":104,\"b\":82},{\"tag\":\"incompatible\",\"a\":104,\"b\":98},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[52,56,69,82,98],\"full_literals\":[-11,3,5,6,7,8]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[48,51,55],\"full_literals\":[-12,1,2,4]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-13,11,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-14,false,13],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-15,false,12],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-16,false,15],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-17,14,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-17,false,16],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[101],\"full_literals\":[-18,9]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[104],\"full_literals\":[-19,10]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-20,18,19],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-21,false,20],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "27 14 0 21 19 0\n28 16 0 21 20 0\n29 13 0 27 16 0\n30 15 0 28 18 0\n31 11 0 29 15 0\n32 12 0 30 17 0\n33 20 0 26 25 0\n34 -5 0 32 4 5 6 14 0\n35 -3 0 32 1 2 3 14 0\n36 -8 0 33 9 12 22 23 24 0\n37 -6 0 33 7 10 22 23 24 0\n38 7 0 37 31 36 34 35 13 0\n39 -9 0 38 8 0\n40 -10 0 38 11 0\n41 -18 0 39 22 0\n42 -19 0 40 23 0\n43 0 41 42 33 24 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f07c9cb4ac6a5a2e87ad1b16958b61d98e538ce4b8ae4785e9c749c66592e479d1715954b51d58d534cd4b4ad4745dd0e63c4e9394e332cc73c2d8b92d4b32d2b2ae1b46c5bc1d8791d4731d2729e1745c571b09c0f06a2683a198960d90e2384e0b81e1a4990e465254354348d1342d0770390c6384c930cd0b22c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "49b6d26da4924926db49b692492492492492492492492492489249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 75), (facetIndex 76)]))
 (.leaf ([(facetIndex 88), (facetIndex 89), (facetIndex 90), (facetIndex 91), (facetIndex 92), (facetIndex 93), (facetIndex 94)])))
 (.branch 3
 (.leaf ([(facetIndex 44), (facetIndex 54), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 69)]))
 (.leaf ([(facetIndex 47), (facetIndex 49), (facetIndex 57), (facetIndex 59), (facetIndex 68)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 45), (facetIndex 55), (facetIndex 63), (facetIndex 78), (facetIndex 83), (facetIndex 96), (facetIndex 101), (facetIndex 107)]))
 (.leaf ([(facetIndex 42), (facetIndex 52), (facetIndex 62), (facetIndex 77), (facetIndex 82), (facetIndex 95), (facetIndex 100), (facetIndex 106)])))
 (.branch 7
 (.leaf ([(facetIndex 51), (facetIndex 53), (facetIndex 56), (facetIndex 58), (facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 43), (facetIndex 46), (facetIndex 48), (facetIndex 50)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "940025004a4924900094012800001349297679e8b5ddf7e2f4z1f;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 79), (facetIndex 84), (facetIndex 87)]))
 (.branch 2
 (.leaf ([(facetIndex 97), (facetIndex 102), (facetIndex 105)]))
 (.leaf ([(facetIndex 80), (facetIndex 81)]))))
 (.branch 4
 (.leaf ([(facetIndex 85), (facetIndex 86)]))
 (.branch 5
 (.leaf ([(facetIndex 98), (facetIndex 99)]))
 (.leaf ([(facetIndex 103), (facetIndex 104)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da409080000000d8012z3c;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1, 2]
def grouped3_0016 : List Nat := [1]
def grouped3_0017 : List Nat := [1, 2]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [3]
def grouped3_0020 : List Nat := [3, 4, 5]
def grouped3_0021 : List Nat := [4]
def grouped3_0022 : List Nat := [4, 5]
def grouped3_0023 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record003" 60

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record003" "{\"ridges\":[[15,577],[15,578],[44,529],[49,577],[49,578],[54,529],[59,577],[59,578],[64,529],[64,530],[65,530],[65,577],[66,529],[66,530],[67,529],[67,530],[68,577],[68,578],[69,577],[69,578],[79,596],[81,836],[84,600],[85,769],[86,769],[86,840],[87,624],[98,788],[99,836],[104,840]],\"owners\":[[44,529,[84,85,87],[13,54,64,65,66,67,79,80]],[54,529,[79,80,87],[13,44,64,65,66,67,84,85]],[64,529,[79,80,84,85],[13,44,54,65,66,67,87]],[66,529,[79,80,84,85,87],[13,44,54,64,65,67]],[67,529,[79,84,87],[13,44,54,64,65,66,80,85]],[64,530,[97,98,102,103],[13,44,54,65,66,67,105]],[65,530,[98,103],[13,44,54,64,66,67,97,102,105]],[66,530,[97,98,102,103,105],[13,44,54,64,65,67]],[67,530,[97,102,105],[13,44,54,64,65,66,98,103]],[15,577,[79,81,84,86,87],[49,59,65,68,69]],[49,577,[84,86,87],[15,59,65,68,69,79,81]],[59,577,[79,81,87],[15,49,65,68,69,84,86]],[65,577,[81,86],[15,49,59,68,69,79,84,87]],[68,577,[79,81,84,86],[15,49,59,65,69,87]],[69,577,[79,84,87],[15,49,59,65,68,81,86]],[15,578,[97,99,102,104,105],[49,59,65,68,69]],[49,578,[102,104,105],[15,59,65,68,69,97,99]],[59,578,[97,99,105],[15,49,65,68,69,102,104]],[68,578,[97,99,102,104],[15,49,59,65,69,105]],[69,578,[97,102,105],[15,49,59,65,68,99,104]],[85,769,[16,51,69,81],[61,67,80,86]],[86,769,[16,51,67,80],[61,69,81,85]],[79,596,[97],[]],[98,788,[80],[]],[81,836,[99],[]],[99,836,[81],[]],[84,600,[102],[]],[86,840,[104],[]],[104,840,[86],[]],[87,624,[105],[]]],\"edges\":[[41,[15,49,59,65,68,69,79,81,84,86,87,97,99,102,104,105]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-4],[-10,-6],[-10,-7],[-10,-9],[-16,-2],[-24,-5],[-24,-23],[-28,-27],[-31,-3],[-31,-11],[-31,-14],[-31,-21],[-31,-25],[-31,-30],[-32,-24],[-34,-31],[-35,-3],[-35,-11],[-35,-14],[-35,-21],[-35,-25],[-35,-30],[-35,-34],[-38,-3],[-38,-11],[-38,-14],[-38,-21],[-38,-25],[-38,-30],[-38,-34],[-39,-31],[-39,-35],[-39,-38],[-5,26,27,29],[-12,22,23,29],[-15,22,23,26,27],[-17,22,23,26,27,29],[-18,22,26,29],[-15,31,32,35,36],[-16,32,36],[-17,31,32,35,36,38],[-18,31,35,38],[-1,22,24,26,28,29],[-8,26,28,29],[-13,22,24,29],[-16,24,28],[-19,22,24,26,28],[-20,22,26,29],[-1,31,33,35,37,38],[-8,35,37,38],[-13,31,33,38],[-19,31,33,35,37],[-20,31,35,38],[-27,2,10,20,24],[-28,2,10,18,23],[-22,31],[-32,23],[-24,33],[-33,24],[-26,35],[-28,37],[-37,28],[-29,38],[-40,5,12,15,16,17,18,20],[-41,3,11,14,21,25,30,34,39],[-42,4,6,7,9],[-43,40],[-44,43],[-45,41],[-46,42],[-47,45],[-47,46],[-48,44],[-48,47],[48],[-22,49],[-26,49],[-29,49],[-31,50],[-35,50],[-38,50],[-23,51],[-24,51],[-52,27,28],[-28,52],[-53,32,33],[-33,53],[-36,54],[-37,54],[-51,55],[-50,55],[-55,56],[-49,56],[-54,57],[-58,53],[-53,-54,58],[-59,52,58],[-58,59],[-52,-57,59],[-56,-59,60],[-60],[1,8,13,16,19,20,22,24,26,28,29,31,33,35,37,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":51,\"b\":43},{\"tag\":\"incompatible\",\"a\":51,\"b\":46},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":65,\"b\":16},{\"tag\":\"incompatible\",\"a\":81,\"b\":44},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":86,\"b\":85},{\"tag\":\"incompatible\",\"a\":97,\"b\":42},{\"tag\":\"incompatible\",\"a\":97,\"b\":52},{\"tag\":\"incompatible\",\"a\":97,\"b\":62},{\"tag\":\"incompatible\",\"a\":97,\"b\":77},{\"tag\":\"incompatible\",\"a\":97,\"b\":82},{\"tag\":\"incompatible\",\"a\":97,\"b\":95},{\"tag\":\"incompatible\",\"a\":98,\"b\":81},{\"tag\":\"incompatible\",\"a\":100,\"b\":97},{\"tag\":\"incompatible\",\"a\":102,\"b\":42},{\"tag\":\"incompatible\",\"a\":102,\"b\":52},{\"tag\":\"incompatible\",\"a\":102,\"b\":62},{\"tag\":\"incompatible\",\"a\":102,\"b\":77},{\"tag\":\"incompatible\",\"a\":102,\"b\":82},{\"tag\":\"incompatible\",\"a\":102,\"b\":95},{\"tag\":\"incompatible\",\"a\":102,\"b\":100},{\"tag\":\"incompatible\",\"a\":105,\"b\":42},{\"tag\":\"incompatible\",\"a\":105,\"b\":52},{\"tag\":\"incompatible\",\"a\":105,\"b\":62},{\"tag\":\"incompatible\",\"a\":105,\"b\":77},{\"tag\":\"incompatible\",\"a\":105,\"b\":82},{\"tag\":\"incompatible\",\"a\":105,\"b\":95},{\"tag\":\"incompatible\",\"a\":105,\"b\":100},{\"tag\":\"incompatible\",\"a\":106,\"b\":97},{\"tag\":\"incompatible\",\"a\":106,\"b\":102},{\"tag\":\"incompatible\",\"a\":106,\"b\":105},{\"tag\":\"mate\",\"ridge\":529,\"a\":44,\"owners\":[84,85,87]},{\"tag\":\"mate\",\"ridge\":529,\"a\":54,\"owners\":[79,80,87]},{\"tag\":\"mate\",\"ridge\":529,\"a\":64,\"owners\":[79,80,84,85]},{\"tag\":\"mate\",\"ridge\":529,\"a\":66,\"owners\":[79,80,84,85,87]},{\"tag\":\"mate\",\"ridge\":529,\"a\":67,\"owners\":[79,84,87]},{\"tag\":\"mate\",\"ridge\":530,\"a\":64,\"owners\":[97,98,102,103]},{\"tag\":\"mate\",\"ridge\":530,\"a\":65,\"owners\":[98,103]},{\"tag\":\"mate\",\"ridge\":530,\"a\":66,\"owners\":[97,98,102,103,105]},{\"tag\":\"mate\",\"ridge\":530,\"a\":67,\"owners\":[97,102,105]},{\"tag\":\"mate\",\"ridge\":577,\"a\":15,\"owners\":[79,81,84,86,87]},{\"tag\":\"mate\",\"ridge\":577,\"a\":49,\"owners\":[84,86,87]},{\"tag\":\"mate\",\"ridge\":577,\"a\":59,\"owners\":[79,81,87]},{\"tag\":\"mate\",\"ridge\":577,\"a\":65,\"owners\":[81,86]},{\"tag\":\"mate\",\"ridge\":577,\"a\":68,\"owners\":[79,81,84,86]},{\"tag\":\"mate\",\"ridge\":577,\"a\":69,\"owners\":[79,84,87]},{\"tag\":\"mate\",\"ridge\":578,\"a\":15,\"owners\":[97,99,102,104,105]},{\"tag\":\"mate\",\"ridge\":578,\"a\":49,\"owners\":[102,104,105]},{\"tag\":\"mate\",\"ridge\":578,\"a\":59,\"owners\":[97,99,105]},{\"tag\":\"mate\",\"ridge\":578,\"a\":68,\"owners\":[97,99,102,104]},{\"tag\":\"mate\",\"ridge\":578,\"a\":69,\"owners\":[97,102,105]},{\"tag\":\"mate\",\"ridge\":769,\"a\":85,\"owners\":[16,51,69,81]},{\"tag\":\"mate\",\"ridge\":769,\"a\":86,\"owners\":[16,51,67,80]},{\"tag\":\"mate\",\"ridge\":596,\"a\":79,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":788,\"a\":98,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":836,\"a\":81,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":836,\"a\":99,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":600,\"a\":84,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":840,\"a\":86,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":840,\"a\":104,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":624,\"a\":87,\"owners\":[105]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[44,54,64,65,66,67,69],\"full_literals\":[-40,5,12,15,16,17,18,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[42,52,62,77,82,95,100,106],\"full_literals\":[-41,3,11,14,21,25,30,34,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[43,46,48,50],\"full_literals\":[-42,4,6,7,9]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-47,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-48,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-48,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":79,\"full_literals\":[-22,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":84,\"full_literals\":[-26,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":87,\"full_literals\":[-29,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":97,\"full_literals\":[-31,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":102,\"full_literals\":[-35,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":105,\"full_literals\":[-38,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":80,\"full_literals\":[-23,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":81,\"full_literals\":[-24,51]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[85,86],\"full_literals\":[-52,27,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":86,\"full_literals\":[-28,52]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[98,99],\"full_literals\":[-53,32,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":99,\"full_literals\":[-33,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":103,\"full_literals\":[-36,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":104,\"full_literals\":[-37,54]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,53,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-54,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,52,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-58,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-56,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[15,49,59,65,68,69,79,81,84,86,87,97,99,102,104,105]}]}"
  "103 44 0 75 73 0\n104 47 0 75 74 0\n105 43 0 103 68 0\n106 45 0 104 71 0\n107 46 0 104 72 0\n108 40 0 105 67 0\n109 41 0 106 69 0\n110 42 0 107 70 0\n111 10 2 -59 0 101 100 92 90 83 59 82 57 86 95 97 93 78 77 76 48 38 55 54 84 0\n112 -10 0 110 1 2 3 4 66 0\n113 28 -59 0 101 112 111 5 100 92 90 83 59 93 78 77 76 48 45 91 81 80 79 62 43 44 47 102 0\n114 -59 0 101 112 108 100 92 93 90 76 77 78 82 35 38 48 111 5 113 8 36 34 37 64 0\n115 -58 0 114 98 0\n116 -28 0 114 61 85 89 99 94 0\n117 -37 0 116 62 0\n118 31 35 38 20 24 0 117 116 50 60 63 46 59 51 56 49 52 102 0\n119 -31 0 109 9 10 11 12 13 14 16 31 65 0\n120 -22 0 119 56 0\n121 -35 0 109 17 18 19 20 21 22 23 32 65 0\n122 -38 0 109 24 25 26 27 28 29 30 33 65 0\n123 -29 0 122 63 0\n124 -20 0 122 119 121 53 0\n125 -18 0 119 121 122 42 0\n126 24 0 124 119 121 122 118 0\n127 -5 0 126 6 0\n128 -23 0 126 7 0\n129 -32 0 126 15 0\n130 33 0 126 58 0\n131 -12 0 128 120 123 35 0\n132 53 0 130 87 0\n133 -54 0 132 115 96 0\n134 -36 0 133 88 0\n135 -15 0 134 129 121 119 39 0\n136 -16 0 134 129 40 0\n137 -17 0 134 119 121 129 122 41 0\n138 0 137 135 108 127 131 136 125 124 64 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "bc1f26a968ba1eb46358b6c398e9392e2b86e4785e9a6592e479d14d52d70d6364d4b4ad1b51d1774398e5334cb3a2d8b92e2b4acab1ae1b46c5bc1d8791d4731d2729d1783c4f1d09c0f072c289a0e866258560d90e2382e07871c24990e465254550d50d2342d0770390c6324c530ce0b42c8b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "24da4d249a4926d26924d2492492492492492492492249249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 49), (facetIndex 65), (facetIndex 78), (facetIndex 93)]))
 (.leaf ([(facetIndex 50), (facetIndex 51), (facetIndex 66), (facetIndex 67), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 48), (facetIndex 59), (facetIndex 73), (facetIndex 88)]))
 (.leaf ([(facetIndex 52), (facetIndex 62), (facetIndex 75), (facetIndex 90)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 54), (facetIndex 57), (facetIndex 61), (facetIndex 69), (facetIndex 71), (facetIndex 80), (facetIndex 84), (facetIndex 86), (facetIndex 95), (facetIndex 99)]))
 (.leaf ([(facetIndex 70), (facetIndex 85), (facetIndex 100)])))
 (.branch 7
 (.leaf ([(facetIndex 53), (facetIndex 55), (facetIndex 76), (facetIndex 91)]))
 (.branch 8
 (.leaf ([(facetIndex 56), (facetIndex 58), (facetIndex 60), (facetIndex 63)]))
 (.leaf ([(facetIndex 47), (facetIndex 64), (facetIndex 72), (facetIndex 77), (facetIndex 81), (facetIndex 87), (facetIndex 92), (facetIndex 96)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "540084008630284540084008630284541110873472747646311028022z2c;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 74), (facetIndex 79)]))
 (.leaf ([(facetIndex 89), (facetIndex 94)])))
 (.branch 3
 (.leaf ([(facetIndex 82), (facetIndex 83)]))
 (.leaf ([(facetIndex 97), (facetIndex 98)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "3c100400az29;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
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
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1]
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [2]
def grouped3_0022 : List Nat := [2, 3]
def grouped3_0023 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record005" 98

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record005" "{\"ridges\":[[10,521],[16,769],[16,770],[27,265],[27,521],[27,769],[37,42],[38,26],[39,522],[39,770],[46,259],[48,259],[52,259],[53,769],[56,521],[56,522],[60,41],[60,42],[60,521],[60,522],[61,578],[63,521],[63,522],[73,41],[74,588],[76,521],[79,769],[79,836],[81,41],[82,521],[82,600],[83,521],[87,42],[87,138],[88,42],[89,588],[91,522],[94,770],[94,836],[95,42],[96,42],[97,522],[97,600],[98,522]],\"owners\":[[46,259,[9,16,59,62,68],[5,48,50,52,55]],[48,259,[9,16,55,62,68],[5,46,50,52,59]],[52,259,[9,16,55,59,68],[5,46,48,50,62]],[38,26,[6,29,37,54,55,56,84,85,95,97],[]],[87,138,[8,38,62,63],[31,58,90,96]],[27,265,[9,20,55,59,62,70,73,75],[]],[10,521,[27,74,76,82,83],[45,56,60,61,63]],[56,521,[27,74,76,83],[10,45,60,61,63,82]],[60,521,[27,74,76,82],[10,45,56,61,63,83]],[39,522,[10,45,56,60,61,63,89,97,98],[91]],[63,522,[39,89,91,97,98],[10,45,56,60,61]],[61,578,[94],[15,51,66,67,68,89,97,98]],[16,769,[27,76,79],[53,68]],[53,769,[27],[16,68,76,79]],[79,769,[16,27],[53,68,76]],[94,770,[16,39],[53,68,91]],[74,588,[89],[]],[89,588,[74],[]],[79,836,[94],[]],[94,836,[79],[]],[82,600,[97],[]],[97,600,[82],[]]],\"edges\":[[29,[10,27,39,45,56,60,61,63,74,76,82,83,89,91,97,98]],[44,[16,27,39,53,68,76,79,91,94]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-23,-4],[-24,-3],[-24,-12],[-24,-22],[-24,-23],[-26,-4],[-26,-15],[-26,-22],[-27,-24],[-28,-1],[-28,-2],[-28,-3],[-28,-12],[-28,-22],[-28,-23],[-28,-27],[-29,-5],[-29,-23],[-29,-26],[-30,-24],[-30,-28],[-31,-3],[-31,-12],[-31,-22],[-31,-23],[-31,-27],[-31,-30],[-32,-24],[-32,-26],[-33,-24],[-34,-17],[-34,-24],[-34,-32],[-34,-33],[-35,-17],[-35,-28],[-36,-24],[-36,-28],[-36,-31],[-40,-6],[-40,-26],[-40,-38],[-41,-38],[-41,-40],[-42,-22],[-42,-25],[-42,-37],[-42,-38],[-42,-39],[-42,-40],[-43,-38],[-43,-40],[-43,-41],[-45,-26],[-45,-38],[-46,-38],[-46,-45],[-48,-42],[-49,-24],[-49,-26],[-49,-38],[-50,-22],[-50,-24],[-50,-25],[-50,-37],[-50,-39],[-50,-48],[-51,-22],[-51,-25],[-51,-28],[-51,-37],[-51,-39],[-51,-48],[-52,-42],[-52,-50],[-52,-51],[-54,-42],[-54,-50],[-54,-51],[-55,-8],[-55,-26],[-55,-52],[-55,-53],[-56,-53],[-57,-53],[-57,-55],[-58,-53],[-58,-56],[-60,-26],[-60,-53],[-61,-53],[-61,-60],[-62,-13],[-62,-18],[-62,-19],[-62,-21],[-62,-36],[-62,-42],[-62,-44],[-62,-57],[-62,-59],[-63,-42],[-63,-50],[-63,-51],[-64,-24],[-64,-26],[-64,-53],[-67,-42],[-67,-50],[-67,-51],[-68,-15],[-68,-32],[-68,-40],[-68,-45],[-68,-49],[-68,-55],[-68,-60],[-68,-64],[-14,3,5,27,30,36],[-16,3,5,23,30,36],[-20,3,5,23,27,36],[-10,1,8,9,22,23,24,52,53,63,65],[-28,-41,-49],[-9,-28,-55],[-28,-55,-63],[-28,-56,-64],[-55,2,10,30,31],[-7,3,6,23,27,30,38,41,43],[-4,7,42,44,50,51],[-24,7,42,44,51],[-28,7,42,44,50],[-7,-24,-51],[-7,-28,-50],[-7,-31,-50],[-7,-31,-51],[-24,-44,-51],[-28,-44,-50],[-31,-44,-50],[-31,-44,-51],[-11,4,13,24,28,29,31,57,65,66],[-31,11,57,59,65,66],[-11,-24,-66],[-11,-28,-65],[-11,-31,-65],[-11,-31,-66],[-24,-59,-66],[-28,-59,-65],[-31,-59,-65],[-31,-59,-66],[-29,62],[-5,7,44,47],[-21,7],[-47,5,7],[-5,-7,-47],[-62,5,11],[-5,-11,-62],[-42,57],[-57,42],[-47,62],[-62,47],[-50,65],[-65,50],[-69,14,17,33,46,61],[-70,18,19,34,35,36],[-71,12,13,16,27,41,56],[-72,20,30,43,58],[-73,22,25,29,37,39,48,52,54,63,67],[-74,38,53,68],[-75,21,23,44,59],[-76,24,26,28,31],[-28,76],[-77,15,32,40,45,49,55,60,64],[-78,69],[-78,70],[-79,71],[-79,72],[-80,78],[-80,79],[-81,73,74],[-82,73],[-82,74],[-83,76],[-83,77],[-84,75,83],[-85,75],[-85,83],[-86,81],[-86,82,85],[-86,84],[-87,85],[-88,80,87],[-88,86],[88],[-89,42,47],[-42,89],[-47,89],[-90,57,62],[-62,90],[-91,50,51],[-50,91],[-51,91],[-92,65,66],[-65,92],[-66,92],[-93,89,90],[-90,93],[-89,93],[-89,-90,94],[-92,95],[-96,91],[-91,95],[-96,92],[-91,-92,96],[-97,93,96],[-93,-96,98],[-94,-95,98],[97],[-98],[4,7,11,13,24,28,29,31,42,44,50,51,57,59,65,66],[5,7,11,21,36,44,47,59,62]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":55,\"b\":10},{\"tag\":\"incompatible\",\"a\":56,\"b\":9},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":58,\"b\":10},{\"tag\":\"incompatible\",\"a\":58,\"b\":47},{\"tag\":\"incompatible\",\"a\":58,\"b\":54},{\"tag\":\"incompatible\",\"a\":59,\"b\":56},{\"tag\":\"incompatible\",\"a\":60,\"b\":6},{\"tag\":\"incompatible\",\"a\":60,\"b\":8},{\"tag\":\"incompatible\",\"a\":60,\"b\":9},{\"tag\":\"incompatible\",\"a\":60,\"b\":44},{\"tag\":\"incompatible\",\"a\":60,\"b\":54},{\"tag\":\"incompatible\",\"a\":60,\"b\":55},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":16},{\"tag\":\"incompatible\",\"a\":61,\"b\":55},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":56},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":63,\"b\":9},{\"tag\":\"incompatible\",\"a\":63,\"b\":44},{\"tag\":\"incompatible\",\"a\":63,\"b\":54},{\"tag\":\"incompatible\",\"a\":63,\"b\":55},{\"tag\":\"incompatible\",\"a\":63,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":56},{\"tag\":\"incompatible\",\"a\":64,\"b\":58},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":49},{\"tag\":\"incompatible\",\"a\":66,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":49},{\"tag\":\"incompatible\",\"a\":67,\"b\":60},{\"tag\":\"incompatible\",\"a\":68,\"b\":56},{\"tag\":\"incompatible\",\"a\":68,\"b\":60},{\"tag\":\"incompatible\",\"a\":68,\"b\":63},{\"tag\":\"incompatible\",\"a\":72,\"b\":20},{\"tag\":\"incompatible\",\"a\":72,\"b\":58},{\"tag\":\"incompatible\",\"a\":72,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":54},{\"tag\":\"incompatible\",\"a\":74,\"b\":57},{\"tag\":\"incompatible\",\"a\":74,\"b\":69},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":71},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"incompatible\",\"a\":75,\"b\":70},{\"tag\":\"incompatible\",\"a\":75,\"b\":72},{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":77,\"b\":58},{\"tag\":\"incompatible\",\"a\":77,\"b\":70},{\"tag\":\"incompatible\",\"a\":78,\"b\":70},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":80,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":56},{\"tag\":\"incompatible\",\"a\":81,\"b\":58},{\"tag\":\"incompatible\",\"a\":81,\"b\":70},{\"tag\":\"incompatible\",\"a\":82,\"b\":54},{\"tag\":\"incompatible\",\"a\":82,\"b\":56},{\"tag\":\"incompatible\",\"a\":82,\"b\":57},{\"tag\":\"incompatible\",\"a\":82,\"b\":69},{\"tag\":\"incompatible\",\"a\":82,\"b\":71},{\"tag\":\"incompatible\",\"a\":82,\"b\":80},{\"tag\":\"incompatible\",\"a\":83,\"b\":54},{\"tag\":\"incompatible\",\"a\":83,\"b\":57},{\"tag\":\"incompatible\",\"a\":83,\"b\":60},{\"tag\":\"incompatible\",\"a\":83,\"b\":69},{\"tag\":\"incompatible\",\"a\":83,\"b\":71},{\"tag\":\"incompatible\",\"a\":83,\"b\":80},{\"tag\":\"incompatible\",\"a\":84,\"b\":74},{\"tag\":\"incompatible\",\"a\":84,\"b\":82},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"incompatible\",\"a\":86,\"b\":74},{\"tag\":\"incompatible\",\"a\":86,\"b\":82},{\"tag\":\"incompatible\",\"a\":86,\"b\":83},{\"tag\":\"incompatible\",\"a\":87,\"b\":29},{\"tag\":\"incompatible\",\"a\":87,\"b\":58},{\"tag\":\"incompatible\",\"a\":87,\"b\":84},{\"tag\":\"incompatible\",\"a\":87,\"b\":85},{\"tag\":\"incompatible\",\"a\":88,\"b\":85},{\"tag\":\"incompatible\",\"a\":89,\"b\":85},{\"tag\":\"incompatible\",\"a\":89,\"b\":87},{\"tag\":\"incompatible\",\"a\":90,\"b\":85},{\"tag\":\"incompatible\",\"a\":90,\"b\":88},{\"tag\":\"incompatible\",\"a\":92,\"b\":58},{\"tag\":\"incompatible\",\"a\":92,\"b\":85},{\"tag\":\"incompatible\",\"a\":93,\"b\":85},{\"tag\":\"incompatible\",\"a\":93,\"b\":92},{\"tag\":\"incompatible\",\"a\":94,\"b\":45},{\"tag\":\"incompatible\",\"a\":94,\"b\":50},{\"tag\":\"incompatible\",\"a\":94,\"b\":51},{\"tag\":\"incompatible\",\"a\":94,\"b\":53},{\"tag\":\"incompatible\",\"a\":94,\"b\":68},{\"tag\":\"incompatible\",\"a\":94,\"b\":74},{\"tag\":\"incompatible\",\"a\":94,\"b\":76},{\"tag\":\"incompatible\",\"a\":94,\"b\":89},{\"tag\":\"incompatible\",\"a\":94,\"b\":91},{\"tag\":\"incompatible\",\"a\":95,\"b\":74},{\"tag\":\"incompatible\",\"a\":95,\"b\":82},{\"tag\":\"incompatible\",\"a\":95,\"b\":83},{\"tag\":\"incompatible\",\"a\":96,\"b\":56},{\"tag\":\"incompatible\",\"a\":96,\"b\":58},{\"tag\":\"incompatible\",\"a\":96,\"b\":85},{\"tag\":\"incompatible\",\"a\":99,\"b\":74},{\"tag\":\"incompatible\",\"a\":99,\"b\":82},{\"tag\":\"incompatible\",\"a\":99,\"b\":83},{\"tag\":\"incompatible\",\"a\":100,\"b\":47},{\"tag\":\"incompatible\",\"a\":100,\"b\":64},{\"tag\":\"incompatible\",\"a\":100,\"b\":72},{\"tag\":\"incompatible\",\"a\":100,\"b\":77},{\"tag\":\"incompatible\",\"a\":100,\"b\":81},{\"tag\":\"incompatible\",\"a\":100,\"b\":87},{\"tag\":\"incompatible\",\"a\":100,\"b\":92},{\"tag\":\"incompatible\",\"a\":100,\"b\":96},{\"tag\":\"mate\",\"ridge\":259,\"a\":46,\"owners\":[9,16,59,62,68]},{\"tag\":\"mate\",\"ridge\":259,\"a\":48,\"owners\":[9,16,55,62,68]},{\"tag\":\"mate\",\"ridge\":259,\"a\":52,\"owners\":[9,16,55,59,68]},{\"tag\":\"mate\",\"ridge\":26,\"a\":38,\"owners\":[6,29,37,54,55,56,84,85,95,97]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[60,73,81]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[37,60,87]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[60,87,95]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[60,88,96]},{\"tag\":\"mate\",\"ridge\":138,\"a\":87,\"owners\":[8,38,62,63]},{\"tag\":\"mate\",\"ridge\":265,\"a\":27,\"owners\":[9,20,55,59,62,70,73,75]},{\"tag\":\"mate\",\"ridge\":521,\"a\":10,\"owners\":[27,74,76,82,83]},{\"tag\":\"mate\",\"ridge\":521,\"a\":56,\"owners\":[27,74,76,83]},{\"tag\":\"mate\",\"ridge\":521,\"a\":60,\"owners\":[27,74,76,82]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[27,56,83]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[27,60,82]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[27,63,82]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[27,63,83]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[56,76,83]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[60,76,82]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[63,76,82]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[63,76,83]},{\"tag\":\"mate\",\"ridge\":522,\"a\":39,\"owners\":[10,45,56,60,61,63,89,97,98]},{\"tag\":\"mate\",\"ridge\":522,\"a\":63,\"owners\":[39,89,91,97,98]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[39,56,98]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[39,60,97]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[39,63,97]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[39,63,98]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[56,91,98]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[60,91,97]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[63,91,97]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[63,91,98]},{\"tag\":\"mate\",\"ridge\":578,\"a\":61,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":769,\"a\":16,\"owners\":[27,76,79]},{\"tag\":\"mate\",\"ridge\":769,\"a\":53,\"owners\":[27]},{\"tag\":\"mate\",\"ridge\":769,\"a\":79,\"owners\":[16,27]},{\"tag\":\"three\",\"ridge\":769,\"vertices\":[16,27,79]},{\"tag\":\"mate\",\"ridge\":770,\"a\":94,\"owners\":[16,39]},{\"tag\":\"three\",\"ridge\":770,\"vertices\":[16,39,94]},{\"tag\":\"mate\",\"ridge\":588,\"a\":74,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":588,\"a\":89,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":836,\"a\":79,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":836,\"a\":94,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":600,\"a\":82,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":600,\"a\":97,\"owners\":[82]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[46,49,65,78,93],\"full_literals\":[-69,14,17,33,46,61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[50,51,66,67,68],\"full_literals\":[-70,18,19,34,35,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[44,45,48,59,73,88],\"full_literals\":[-71,12,13,16,27,41,56]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[52,62,75,90],\"full_literals\":[-72,20,30,43,58]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[54,57,61,69,71,80,84,86,95,99],\"full_literals\":[-73,22,25,29,37,39,48,52,54,63,67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[70,85,100],\"full_literals\":[-74,38,53,68]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[53,55,76,91],\"full_literals\":[-75,21,23,44,59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[56,58,60,63],\"full_literals\":[-76,24,26,28,31]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":60,\"full_literals\":[-28,76]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[47,64,72,77,81,87,92,96],\"full_literals\":[-77,15,32,40,45,49,55,60,64]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-78,69,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-79,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-80,78,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-80,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-81,73,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-82,73,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-82,false,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-83,76,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-83,false,77],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-84,75,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-85,75,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-85,false,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-86,81,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-86,82,85],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,false,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-87,false,85],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-88,80,87],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-88,false,86],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[74,79],\"full_literals\":[-89,42,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":74,\"full_literals\":[-42,89]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":79,\"full_literals\":[-47,89]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[89,94],\"full_literals\":[-90,57,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":94,\"full_literals\":[-62,90]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[82,83],\"full_literals\":[-91,50,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":82,\"full_literals\":[-50,91]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":83,\"full_literals\":[-51,91]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[97,98],\"full_literals\":[-92,65,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":97,\"full_literals\":[-65,92]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":98,\"full_literals\":[-66,92]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-93,89,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-90,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-89,false,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-89,-90,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-92,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-96,91,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-91,false,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-96,false,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-91,-92,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-97,93,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-93,-96,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-94,-95,98],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[10,27,39,45,56,60,61,63,74,76,82,83,89,91,97,98]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[16,27,39,53,68,76,79,91,94]}]}"
  "221 86 0 193 192 0\n222 81 0 221 187 0\n223 84 0 221 189 0\n224 -50 25 52 37 22 -73 29 0 66 67 78 103 109 167 0\n225 -51 22 25 -73 29 0 71 72 73 76 79 104 110 167 0\n226 22 25 -73 -96 0 218 215 206 198 150 210 225 199 65 75 224 0\n227 -22 -76 0 4 8 14 24 170 0\n228 -25 -91 0 64 69 199 0\n229 -26 -77 0 7 29 41 54 60 81 89 106 172 0\n230 -24 -66 -51 93 0 207 196 206 198 37 132 136 142 146 151 152 220 0\n231 50 -96 0 218 221 210 228 215 207 196 206 198 212 162 199 202 68 70 226 180 188 186 182 183 229 230 170 39 135 139 145 149 151 152 220 0\n232 -31 -96 0 218 231 161 215 207 196 206 198 39 134 138 144 148 151 152 220 0\n233 -96 0 218 221 210 215 206 207 198 196 228 231 62 63 161 226 180 188 186 182 183 229 232 170 38 147 133 137 143 151 152 220 0\n234 93 0 233 217 214 0\n235 -50 0 233 161 200 203 213 0\n236 -65 0 235 162 0\n237 89 62 0 234 195 205 158 197 0\n238 62 0 222 221 150 159 237 194 45 46 47 48 49 50 58 74 77 102 108 157 167 85 86 179 180 168 188 111 112 114 115 117 118 186 172 183 0\n239 -13 0 238 93 0\n240 -18 0 238 94 0\n241 -19 0 238 95 0\n242 -21 0 238 96 0\n243 -36 0 238 97 0\n244 -42 0 238 98 0\n245 -44 0 238 99 0\n246 -57 0 238 100 0\n247 -59 0 238 101 0\n248 47 0 238 160 0\n249 90 0 238 198 0\n250 89 0 248 196 0\n251 94 0 249 250 208 0\n252 -95 0 251 218 216 0\n253 -92 0 252 209 0\n254 -91 0 252 211 0\n255 -66 0 253 204 0\n256 -51 0 254 201 0\n257 76 24 -11 31 0 223 245 247 242 236 246 255 239 171 182 184 169 1 18 140 0\n258 28 24 -11 31 0 236 246 255 239 257 170 6 19 140 0\n259 -40 -28 -7 0 21 16 15 12 40 42 44 52 128 0\n260 -45 33 17 -69 -74 14 0 55 57 114 163 168 91 0\n261 -49 16 -28 0 221 242 247 245 193 239 15 169 185 190 191 178 175 188 181 16 13 61 115 123 168 165 84 0\n262 -55 -28 22 24 31 0 236 21 15 11 10 80 82 83 125 127 124 122 0\n263 -60 33 17 -69 -74 14 0 90 92 117 163 168 56 0\n264 -64 16 -28 0 221 242 247 245 193 239 15 169 185 190 191 178 175 188 181 16 13 107 118 126 168 165 43 0\n265 -38 -72 -71 16 20 30 27 12 0 239 43 51 165 166 88 0\n266 24 5 31 0 238 248 245 247 242 223 221 193 241 240 243 239 153 155 257 227 258 12 13 15 16 21 36 169 121 120 119 184 185 183 190 188 191 181 177 178 173 174 175 176 164 31 33 34 259 260 261 262 263 264 172 111 265 168 84 87 165 166 53 0\n267 -53 -72 -71 16 20 30 27 12 0 239 84 87 165 166 53 0\n268 5 31 0 243 240 241 193 221 223 242 247 245 266 2 3 5 9 20 28 30 32 59 105 169 121 120 119 184 185 183 190 188 191 181 177 178 173 174 175 176 164 265 35 260 263 267 168 111 113 116 172 0\n269 31 0 248 238 255 236 247 246 256 235 245 244 239 268 17 154 156 131 129 130 219 0\n270 11 0 255 246 247 269 236 141 0\n271 -3 0 269 22 0\n272 -12 0 269 23 0\n273 -23 0 269 25 0\n274 -27 0 269 26 0\n275 -30 0 269 27 0\n276 -5 0 270 238 156 0\n277 -75 0 273 242 247 245 169 0\n278 -20 0 273 271 276 243 274 121 0\n279 -16 0 273 271 276 243 275 120 0\n280 83 0 277 223 184 0\n281 -85 0 277 185 0\n282 77 0 280 183 0\n283 -87 0 281 190 0\n284 82 0 281 221 188 0\n285 80 0 283 193 191 0\n286 74 0 284 181 0\n287 79 0 285 178 0\n288 71 0 287 175 0\n289 72 0 287 176 0\n290 -38 0 289 288 279 278 275 274 272 265 0\n291 -53 0 289 288 279 278 275 274 272 267 0\n292 68 0 291 290 286 168 0\n293 -15 0 292 111 0\n294 -32 0 292 112 0\n295 -40 0 292 113 0\n296 -45 0 292 114 0\n297 -49 0 292 115 0\n298 -55 0 292 116 0\n299 -60 0 292 117 0\n300 -64 0 292 118 0\n301 0 293 295 300 282 294 299 298 296 297 172 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00088.record005
