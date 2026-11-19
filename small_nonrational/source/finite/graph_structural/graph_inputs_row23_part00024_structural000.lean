module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00024Frames
public import GraphInputsRow23Part00024Leaves
public import GraphInputsRow23Part00024Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3a8da8da1e4785e785c96a4e96655936725697158d5356352d8745da8da398e5334e331cd8b2ac6b86d1b26d2729c6745c570de0f43c8f13c2f470e23285a89a16079a1385893251916625496154550d074c388ca318e1314c8b12c1b81c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12492492492492492492492492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008.data.quota

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record008" 10

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record008" "{\"ridges\":[[17,292],[24,289],[42,292],[54,289],[58,292],[60,292],[63,292],[64,292],[69,289],[71,289]],\"owners\":[[24,289,[17,42,58,60,64],[54,69,71]],[54,289,[17,58,60,64],[24,42,69,71]],[69,289,[17,42,60,64],[24,54,58,71]],[71,289,[17,42,58,60,64],[24,54,69]],[17,292,[],[42,58,60,63,64]],[42,292,[],[17,58,60,63,64]],[58,292,[],[17,42,60,63,64]],[60,292,[],[17,42,58,63,64]],[63,292,[],[17,42,58,60,64]],[64,292,[],[17,42,58,60,63]]],\"edges\":[[37,[17,24,42,54,58,60,63,64,69,71]]],\"groupings\":[]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-2,1,3,5,6,8],[-4,1,5,6,8],[-9,1,3,6,8],[-10,1,3,5,6,8],[-1],[-3],[-5],[-6],[-7],[-8],[1,2,3,4,5,6,7,8,9,10]],\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71}],\"rules\":[{\"tag\":\"mate\",\"ridge\":289,\"a\":24,\"owners\":[17,42,58,60,64]},{\"tag\":\"mate\",\"ridge\":289,\"a\":54,\"owners\":[17,58,60,64]},{\"tag\":\"mate\",\"ridge\":289,\"a\":69,\"owners\":[17,42,60,64]},{\"tag\":\"mate\",\"ridge\":289,\"a\":71,\"owners\":[17,42,58,60,64]},{\"tag\":\"mate\",\"ridge\":292,\"a\":17,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":292,\"a\":42,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":292,\"a\":58,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":292,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":292,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":292,\"a\":64,\"owners\":[]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[17,24,42,54,58,60,63,64,69,71]}]}"
  "p cnf 10 11\n-2 1 3 5 6 8 0\n-4 1 5 6 8 0\n-9 1 3 6 8 0\n-10 1 3 5 6 8 0\n-1 0\n-3 0\n-5 0\n-6 0\n-7 0\n-8 0\n1 2 3 4 5 6 7 8 9 10 0\n"
  "12 -9 0 10 5 6 8 3 0\n13 -4 0 10 5 7 8 2 0\n14 -2 0 10 5 6 7 8 1 0\n15 -10 0 10 5 6 7 8 4 0\n16 0 5 14 6 13 7 8 9 10 12 15 11 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record027
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e635a2e4b86e879d1c65994e5c569565395953570d6362d1b61d474e3a4d9394c738ad2b1ad1b26c5b0ee8761e4789d2729e1725c5743c8f13c1f4b0d2868c619a0e0b9913452986519614c5494658350d0b4c318e1324c5382c2b06e0721c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "92492492492492492492492492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 66), (facetIndex 68), (facetIndex 72)]))
 (.leaf ([(facetIndex 39), (facetIndex 56), (facetIndex 65), (facetIndex 67), (facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 48), (facetIndex 57), (facetIndex 69), (facetIndex 70), (facetIndex 71)]))
 (.branch 4
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 76)]))
 (.leaf ([(facetIndex 32), (facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 58), (facetIndex 63), (facetIndex 64), (facetIndex 73), (facetIndex 77)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 52), (facetIndex 53), (facetIndex 55)]))
 (.branch 7
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 44)]))
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 51)]))))
 (.branch 9
 (.leaf ([(facetIndex 59), (facetIndex 60), (facetIndex 62)]))
 (.branch 10
 (.leaf ([(facetIndex 54)]))
 (.leaf ([(facetIndex 61)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "14333402220101448a88421595577725556666614446664z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3, 4]
def grouped2_0006 : List Nat := [5, 6, 7]
def grouped2_0007 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0008 : List Nat := [8]
def grouped2_0009 : List Nat := [8, 9, 10]
def grouped2_0010 : List Nat := [9]
def grouped2_0011 : List Nat := [9, 10]
def grouped2_0012 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record027" "{\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record027" 22

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record027" "{\"ridges\":[[19,388],[24,385],[43,388],[48,273],[54,385],[57,273],[61,388],[64,388],[67,388],[68,388],[69,273],[70,385],[71,273],[72,385]],\"owners\":[[24,385,[19,43,61,67,68],[54,70,72]],[54,385,[19,61,67,68],[24,43,70,72]],[70,385,[19,43,67,68],[24,54,61,72]],[72,385,[19,43,61,67],[24,54,68,70]],[19,388,[],[43,61,64,67,68]],[43,388,[],[19,61,64,67,68]],[61,388,[],[19,43,64,67,68]],[64,388,[],[19,43,61,67,68]],[67,388,[],[19,43,61,64,68]],[68,388,[],[19,43,61,64,67]],[48,273,[24,64,72],[20,54,57,69,71]],[57,273,[24,54,72],[20,48,64,69,71]],[69,273,[24,54,64,72],[20,48,57,71]],[71,273,[24,54,64,72],[20,48,57,69]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record027" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record027\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-2,1,3,7,9,10],[-5,1,7,9,10],[-12,1,3,9,10],[-14,1,3,7,9],[-1],[-3],[-7],[-8],[-9],[-10],[-4,2,8,14],[-6,2,5,14],[-11,2,5,8,14],[-13,2,5,8,14],[-15,4,6,11,12,13],[-16,5],[-17,15],[-18,17],[-19,16],[-20,19],[-21,20],[-22,18,21],[22]],\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"mate\",\"ridge\":385,\"a\":24,\"owners\":[19,43,61,67,68]},{\"tag\":\"mate\",\"ridge\":385,\"a\":54,\"owners\":[19,61,67,68]},{\"tag\":\"mate\",\"ridge\":385,\"a\":70,\"owners\":[19,43,67,68]},{\"tag\":\"mate\",\"ridge\":385,\"a\":72,\"owners\":[19,43,61,67]},{\"tag\":\"mate\",\"ridge\":388,\"a\":19,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":388,\"a\":43,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":388,\"a\":61,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":388,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":388,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":388,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":273,\"a\":48,\"owners\":[24,64,72]},{\"tag\":\"mate\",\"ridge\":273,\"a\":57,\"owners\":[24,54,72]},{\"tag\":\"mate\",\"ridge\":273,\"a\":69,\"owners\":[24,54,64,72]},{\"tag\":\"mate\",\"ridge\":273,\"a\":71,\"owners\":[24,54,64,72]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[48,57,69,70,71],\"full_literals\":[-15,4,6,11,12,13]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[54],\"full_literals\":[-16,5]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-17,15,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-18,false,17],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-19,16,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-20,false,19],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-21,false,20],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-22,18,21],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true}]}"
  "p cnf 22 23\n-2 1 3 7 9 10 0\n-5 1 7 9 10 0\n-12 1 3 9 10 0\n-14 1 3 7 9 0\n-1 0\n-3 0\n-7 0\n-8 0\n-9 0\n-10 0\n-4 2 8 14 0\n-6 2 5 14 0\n-11 2 5 8 14 0\n-13 2 5 8 14 0\n-15 4 6 11 12 13 0\n-16 5 0\n-17 15 0\n-18 17 0\n-19 16 0\n-20 19 0\n-21 20 0\n-22 18 21 0\n22 0\n"
  "24 -14 0 9 5 6 7 4 0\n25 -12 0 10 5 6 9 3 0\n26 -5 0 10 5 7 9 2 0\n27 -2 0 10 5 6 7 9 1 0\n28 -4 0 27 8 24 11 0\n29 -6 0 27 26 24 12 0\n30 -11 0 27 26 8 24 13 0\n31 -13 0 27 26 8 24 14 0\n32 -15 0 28 29 30 25 31 15 0\n33 -16 0 26 16 0\n34 -17 0 32 17 0\n35 -18 0 34 18 0\n36 -19 0 33 19 0\n37 -20 0 36 20 0\n38 -21 0 37 21 0\n39 -22 0 35 38 22 0\n40 0 39 23 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record027

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record046
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1f26a96a3a1e9a659996358768b92e8789e0fa69966391e5a559595354758b52d8749d0f72368e6358e9364e5334e331ce4b4ac9b0ed4731e2729e1745c3783d0f23c6c1722a1aa1a1698649866258561382e07a291a6191658549465254551342d0758388d2318e1324c5382c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "492492492492492492492492492492492492492449249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 47), (facetIndex 68), (facetIndex 73), (facetIndex 74)]))
 (.leaf ([(facetIndex 49), (facetIndex 84), (facetIndex 89), (facetIndex 90)])))
 (.branch 3
 (.leaf ([(facetIndex 48), (facetIndex 54), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62)]))
 (.branch 4
 (.leaf ([(facetIndex 50), (facetIndex 55), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66)]))
 (.leaf ([(facetIndex 70), (facetIndex 75), (facetIndex 76)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 82), (facetIndex 87), (facetIndex 88)]))
 (.leaf ([(facetIndex 46), (facetIndex 53), (facetIndex 57), (facetIndex 58), (facetIndex 67), (facetIndex 72), (facetIndex 77), (facetIndex 78), (facetIndex 81), (facetIndex 86), (facetIndex 91), (facetIndex 92), (facetIndex 95)])))
 (.branch 8
 (.leaf ([(facetIndex 56), (facetIndex 79), (facetIndex 80), (facetIndex 93), (facetIndex 94)]))
 (.branch 9
 (.leaf ([(facetIndex 45), (facetIndex 69), (facetIndex 71), (facetIndex 83), (facetIndex 85)]))
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 51), (facetIndex 52)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "67766115568185677664400684806333322226673269931206899z2b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8, 9]
def grouped2_0016 : List Nat := [8]
def grouped2_0017 : List Nat := [8, 9]
def grouped2_0018 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record046" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record046" 39

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record046" "{\"ridges\":[[31,70],[36,134],[51,70],[51,134],[82,14],[82,134],[84,262],[89,70],[90,134]],\"owners\":[[82,14,[0,30,31,44,45,84,85],[29,43,83]],[84,262,[5,36,47,52,88],[35,44,89]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record046" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record046\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-9,-6],[-10,-7],[-11,-1],[-11,-2],[-11,-7],[-11,-8],[-11,-9],[-11,-10],[-12,-10],[-13,-6],[-14,-7],[-16,-6],[-17,-12],[-18,-7],[-18,-12],[-19,-6],[-20,-7],[-20,-14],[-22,-11],[-22,-15],[-23,-6],[-23,-11],[-24,-3],[-24,-12],[-24,-17],[-24,-21],[-25,-7],[-25,-12],[-25,-23],[-19,1,3,4,7,8,20,21],[-4,-11,-24],[-5,-11,-19],[-11,-19,-25],[-20,2,5,9,12,23],[-26,9,13,15,16],[-27,10,20,24,25],[-28,14,17,18],[-29,19,22,23],[-30,6,7,11,12],[-31,26],[-31,27],[-32,28],[-33,32],[-34,31],[-34,33],[-35,29],[-36,30],[-37,36],[-38,35],[-38,37],[-39,34],[-39,38],[39]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":47,\"b\":43},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":51,\"b\":0},{\"tag\":\"incompatible\",\"a\":51,\"b\":5},{\"tag\":\"incompatible\",\"a\":51,\"b\":44},{\"tag\":\"incompatible\",\"a\":51,\"b\":45},{\"tag\":\"incompatible\",\"a\":51,\"b\":47},{\"tag\":\"incompatible\",\"a\":51,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":68,\"b\":43},{\"tag\":\"incompatible\",\"a\":70,\"b\":44},{\"tag\":\"incompatible\",\"a\":74,\"b\":43},{\"tag\":\"incompatible\",\"a\":75,\"b\":52},{\"tag\":\"incompatible\",\"a\":76,\"b\":44},{\"tag\":\"incompatible\",\"a\":76,\"b\":52},{\"tag\":\"incompatible\",\"a\":82,\"b\":43},{\"tag\":\"incompatible\",\"a\":84,\"b\":44},{\"tag\":\"incompatible\",\"a\":84,\"b\":70},{\"tag\":\"incompatible\",\"a\":87,\"b\":51},{\"tag\":\"incompatible\",\"a\":87,\"b\":73},{\"tag\":\"incompatible\",\"a\":88,\"b\":43},{\"tag\":\"incompatible\",\"a\":88,\"b\":51},{\"tag\":\"incompatible\",\"a\":89,\"b\":30},{\"tag\":\"incompatible\",\"a\":89,\"b\":52},{\"tag\":\"incompatible\",\"a\":89,\"b\":75},{\"tag\":\"incompatible\",\"a\":89,\"b\":85},{\"tag\":\"incompatible\",\"a\":90,\"b\":44},{\"tag\":\"incompatible\",\"a\":90,\"b\":52},{\"tag\":\"incompatible\",\"a\":90,\"b\":88},{\"tag\":\"mate\",\"ridge\":14,\"a\":82,\"owners\":[0,30,31,44,45,84,85]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[31,51,89]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[36,51,82]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[51,82,90]},{\"tag\":\"mate\",\"ridge\":262,\"a\":84,\"owners\":[5,36,47,52,88]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[47,68,73,74],\"full_literals\":[-26,9,13,15,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[49,84,89,90],\"full_literals\":[-27,10,20,24,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[70,75,76],\"full_literals\":[-28,14,17,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[82,87,88],\"full_literals\":[-29,19,22,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[43,44,51,52],\"full_literals\":[-30,6,7,11,12]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-31,26,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-31,false,27],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-32,false,28],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-33,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-34,31,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-34,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-36,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-38,35,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-38,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-39,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-39,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true}]}"
  "p cnf 39 53\n-9 -6 0\n-10 -7 0\n-11 -1 0\n-11 -2 0\n-11 -7 0\n-11 -8 0\n-11 -9 0\n-11 -10 0\n-12 -10 0\n-13 -6 0\n-14 -7 0\n-16 -6 0\n-17 -12 0\n-18 -7 0\n-18 -12 0\n-19 -6 0\n-20 -7 0\n-20 -14 0\n-22 -11 0\n-22 -15 0\n-23 -6 0\n-23 -11 0\n-24 -3 0\n-24 -12 0\n-24 -17 0\n-24 -21 0\n-25 -7 0\n-25 -12 0\n-25 -23 0\n-19 1 3 4 7 8 20 21 0\n-4 -11 -24 0\n-5 -11 -19 0\n-11 -19 -25 0\n-20 2 5 9 12 23 0\n-26 9 13 15 16 0\n-27 10 20 24 25 0\n-28 14 17 18 0\n-29 19 22 23 0\n-30 6 7 11 12 0\n-31 26 0\n-31 27 0\n-32 28 0\n-33 32 0\n-34 31 0\n-34 33 0\n-35 29 0\n-36 30 0\n-37 36 0\n-38 35 0\n-38 37 0\n-39 34 0\n-39 38 0\n39 0\n"
  "54 34 0 53 51 0\n55 38 0 53 52 0\n56 31 0 54 44 0\n57 33 0 54 45 0\n58 35 0 55 49 0\n59 37 0 55 50 0\n60 26 0 56 40 0\n61 27 0 56 41 0\n62 32 0 57 43 0\n63 29 0 58 46 0\n64 36 0 59 48 0\n65 28 0 62 42 0\n66 30 0 64 47 0\n67 -10 12 6 0 66 2 8 39 0\n68 -12 0 65 61 9 13 15 24 28 37 36 18 0\n69 -20 6 0 66 68 63 17 39 4 7 19 22 34 38 32 0\n70 -11 -24 20 0 63 26 23 3 5 6 19 22 31 38 30 0\n71 -24 6 0 68 66 65 69 25 70 39 11 14 37 0\n72 6 0 61 68 66 63 67 69 71 36 27 29 39 19 33 38 0\n73 -9 0 72 1 0\n74 -13 0 72 10 0\n75 -16 0 72 12 0\n76 -19 0 72 16 0\n77 -23 0 72 21 0\n78 15 0 75 60 73 74 35 0\n79 22 0 76 63 77 38 0\n80 0 79 78 20 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record046

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record096
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "bc9a9568b8ae4789e0fae1744f1aa6693a4d92e4e565555354b58b51d0f74358ce394cd31ce4b2ac6b86d1b26c5b0ed4789d2729c6725c570de0f43c8f2b09c989528a9160b81e984e1544d18a4a9264a5454952342d0764350e2318d1314e0b0ac1b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "92492492492492492492492492492492492489249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096.data.quota

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record096" "{\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record096" 11

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record096" "{\"ridges\":[[22,208],[24,193],[54,208],[56,193],[63,208],[66,193],[68,208],[69,193],[72,208],[73,208],[74,193]],\"owners\":[[24,193,[22,54,63,68,73],[56,66,69,74]],[56,193,[22,63,68,73],[24,54,66,69,74]],[66,193,[22,54,68,73],[24,56,63,69,74]],[69,193,[22,54,63,73],[24,56,66,68,74]],[74,193,[22,54,63,68,73],[24,56,66,69]],[22,208,[],[54,63,68,72,73]],[54,208,[],[22,63,68,72,73]],[63,208,[],[22,54,68,72,73]],[68,208,[],[22,54,63,72,73]],[72,208,[],[22,54,63,68,73]],[73,208,[],[22,54,63,68,72]]],\"edges\":[[39,[22,24,54,56,63,66,68,69,72,73,74]]],\"groupings\":[]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record096" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record096\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-2,1,3,5,7,10],[-4,1,5,7,10],[-6,1,3,7,10],[-8,1,3,5,10],[-11,1,3,5,7,10],[-1],[-3],[-5],[-7],[-9],[-10],[1,2,3,4,5,6,7,8,9,10,11]],\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74}],\"rules\":[{\"tag\":\"mate\",\"ridge\":193,\"a\":24,\"owners\":[22,54,63,68,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":56,\"owners\":[22,63,68,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":66,\"owners\":[22,54,68,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":69,\"owners\":[22,54,63,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":74,\"owners\":[22,54,63,68,73]},{\"tag\":\"mate\",\"ridge\":208,\"a\":22,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":208,\"a\":54,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":208,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":208,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":208,\"a\":72,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":208,\"a\":73,\"owners\":[]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[22,24,54,56,63,66,68,69,72,73,74]}]}"
  "p cnf 11 12\n-2 1 3 5 7 10 0\n-4 1 5 7 10 0\n-6 1 3 7 10 0\n-8 1 3 5 10 0\n-11 1 3 5 7 10 0\n-1 0\n-3 0\n-5 0\n-7 0\n-9 0\n-10 0\n1 2 3 4 5 6 7 8 9 10 11 0\n"
  "13 -8 0 11 6 7 8 4 0\n14 -6 0 11 6 7 9 3 0\n15 -4 0 11 6 8 9 2 0\n16 -2 0 11 6 7 8 9 1 0\n17 -11 0 11 6 7 8 9 5 0\n18 0 6 16 7 15 8 14 9 13 10 11 17 12 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00024.record096
