module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00017Frames
public import GraphInputsRow16Part00017Leaves
public import GraphInputsRow16Part00017Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00017.record034
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3c2aa99a999562b85e0fbc1aa599995552b45d0f783d0ec370da398d9394e8b62e2b46c9b16c3b91d4789ca719d170dc8f13ea2548aa1582e07aa1544a91542d0768360e4350e2328d1314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "d36924d3692492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 34), (facetIndex 37), (facetIndex 43), (facetIndex 54), (facetIndex 62)]))
 (.leaf ([(facetIndex 32), (facetIndex 40), (facetIndex 42), (facetIndex 46), (facetIndex 57), (facetIndex 65)])))
 (.branch 3
 (.leaf ([(facetIndex 27), (facetIndex 29), (facetIndex 51), (facetIndex 52)]))
 (.leaf ([(facetIndex 59), (facetIndex 60)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 28), (facetIndex 36), (facetIndex 53), (facetIndex 61)]))
 (.leaf ([(facetIndex 31), (facetIndex 33), (facetIndex 35), (facetIndex 45)])))
 (.branch 7
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 41), (facetIndex 44)]))
 (.leaf ([(facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "80236080225ffe6e071d84a29a144z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7]
def grouped2_0008 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00017.record034" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00017.record034" 20

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00017.record034" "{\"ridges\":[[12,577],[35,577],[35,578],[43,577],[45,577],[45,578],[48,577],[49,577],[58,960],[63,612],[66,960]],\"owners\":[[12,577,[55,58],[35,43,45,48,49]],[35,577,[58],[12,43,45,48,49,55]],[43,577,[55,58],[12,35,45,48,49]],[45,577,[58],[12,35,43,48,49,55]],[48,577,[55],[12,35,43,45,49,58]],[49,577,[55],[12,35,43,45,48,58]],[35,578,[66],[12,43,45,48,49,63]],[45,578,[66],[12,35,43,48,49,63]],[63,612,[55],[]],[58,960,[66],[]],[66,960,[58],[]]],\"edges\":[[41,[12,35,43,45,48,49,55,58,63,66]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00017.record034" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00017.record034\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-2],[-11,-3],[-14,-7],[-14,-8],[-14,-9],[-14,-10],[-1,11,12],[-4,12],[-5,11,12],[-6,12],[-8,11],[-9,11],[-4,14],[-6,14],[-13,11],[-12,14],[-14,12],[-15,2,3,4,6],[-16,7,8,9,10],[-17,15],[-18,16],[-19,17],[-19,18],[-20,19],[20],[1,4,5,6,8,9,11,12,13,14]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":55,\"b\":31},{\"tag\":\"incompatible\",\"a\":55,\"b\":33},{\"tag\":\"incompatible\",\"a\":66,\"b\":47},{\"tag\":\"incompatible\",\"a\":66,\"b\":48},{\"tag\":\"incompatible\",\"a\":66,\"b\":49},{\"tag\":\"incompatible\",\"a\":66,\"b\":50},{\"tag\":\"mate\",\"ridge\":577,\"a\":12,\"owners\":[55,58]},{\"tag\":\"mate\",\"ridge\":577,\"a\":35,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":577,\"a\":43,\"owners\":[55,58]},{\"tag\":\"mate\",\"ridge\":577,\"a\":45,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":577,\"a\":48,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":577,\"a\":49,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":578,\"a\":35,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":578,\"a\":45,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":612,\"a\":63,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":960,\"a\":58,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":960,\"a\":66,\"owners\":[58]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[31,33,35,45],\"full_literals\":[-15,2,3,4,6]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[47,48,49,50],\"full_literals\":[-16,7,8,9,10]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-17,false,15],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-18,false,16],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-19,17,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-19,false,18],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-20,false,19],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[12,35,43,45,48,49,55,58,63,66]}]}"
  "27 19 0 25 24 0\n28 17 0 27 22 0\n29 18 0 27 23 0\n30 15 0 28 20 0\n31 16 0 29 21 0\n32 11 12 0 7 9 11 12 15 8 10 17 26 0\n33 14 0 30 13 14 16 32 1 2 18 0\n34 -7 0 33 3 0\n35 -8 0 33 4 0\n36 -9 0 33 5 0\n37 -10 0 33 6 0\n38 0 36 34 31 35 37 19 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00017.record034

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00017.record070
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "b49aa39a564b85e0fad16a4e59552d1743de0dc3a8ce3a4cd362cab86d1b16c3b91cc749ca719e170dd0f13ec268a524a8560b81eb05a1945291542d0768360e4330d2328e1314d0b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "49a4924d2492492492492492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 42), (facetIndex 43), (facetIndex 55), (facetIndex 62)]))
 (.leaf ([(facetIndex 37), (facetIndex 44), (facetIndex 45), (facetIndex 56), (facetIndex 63)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 38), (facetIndex 50), (facetIndex 52)]))
 (.leaf ([(facetIndex 29), (facetIndex 31), (facetIndex 32), (facetIndex 39), (facetIndex 51), (facetIndex 58)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 57), (facetIndex 59)]))
 (.leaf ([(facetIndex 40), (facetIndex 41)])))
 (.branch 7
 (.leaf ([(facetIndex 34), (facetIndex 36), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49)]))
 (.branch 8
 (.leaf ([(facetIndex 33)]))
 (.leaf ([(facetIndex 53), (facetIndex 60)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "10084341008232666611005532160673323z1d;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 1
 (.leaf ([(facetIndex 54)]))
 (.leaf ([(facetIndex 61)])))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨1, 2305843009213693952⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 2
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
def grouped3_0019 : List Nat := [1]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070_matrix_checked

def leafCount : Nat := 4
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 6), (facetIndex 20), (facetIndex 28), (facetIndex 41), (facetIndex 49), (facetIndex 51), (facetIndex 52), (facetIndex 54), (facetIndex 56), (facetIndex 57), (facetIndex 60), (facetIndex 61), (facetIndex 62)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 6), (facetIndex 21), (facetIndex 27), (facetIndex 41), (facetIndex 49), (facetIndex 50), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 58), (facetIndex 59), (facetIndex 61), (facetIndex 63)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 8), (facetIndex 21), (facetIndex 27), (facetIndex 40), (facetIndex 49), (facetIndex 50), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 58), (facetIndex 59), (facetIndex 61), (facetIndex 63)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 8), (facetIndex 20), (facetIndex 28), (facetIndex 40), (facetIndex 49), (facetIndex 51), (facetIndex 52), (facetIndex 54), (facetIndex 56), (facetIndex 57), (facetIndex 60), (facetIndex 61), (facetIndex 62)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf (leaf0000))
 (.leaf (leaf0001)))
 (.branch 3
 (.leaf (leaf0002))
 (.leaf (leaf0003))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00017.record070" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00017.record070" 69

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00017.record070" "{\"ridges\":[[20,161],[21,193],[27,162],[28,194],[29,69],[29,70],[31,37],[37,69],[37,70],[40,19],[47,161],[47,162],[48,193],[48,194],[49,642],[51,69],[52,37],[52,265],[52,289],[53,69],[54,37],[54,69],[54,161],[54,193],[55,161],[56,193],[58,70],[59,266],[59,290],[60,70],[61,70],[61,162],[61,194],[62,162],[63,194],[63,704]],\"owners\":[[40,19,[1,7,8,31,44,45],[4,38]],[52,265,[6,40,43],[18,30,55]],[59,266,[6,40,43],[25,30,62]],[52,289,[10,20],[18,35]],[59,290,[10,27],[25,35]],[49,642,[28,63],[14,45,47]],[63,704,[21],[28,56]]],\"edges\":[[42,[13,20,27,43,48,49,55,62]],[43,[14,21,28,45,47,49,56,63]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00017.record070" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00017.record070\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-18,-5],[-20,-12],[-20,-15],[-22,-20],[-30,-6],[-30,-7],[-30,-26],[-31,-7],[-31,-26],[-31,-28],[-31,-30],[-32,-7],[-32,-25],[-32,-26],[-32,-27],[-32,-28],[-33,-14],[-34,-1],[-34,-33],[-35,-18],[-36,-3],[-36,-15],[-36,-22],[-36,-34],[-37,-16],[-37,-17],[-37,-19],[-37,-29],[-38,-5],[-38,-35],[-39,-36],[-40,-13],[-40,-21],[-41,-1],[-41,-40],[-42,-13],[-42,-18],[-42,-21],[-42,-35],[-43,-3],[-43,-15],[-43,-22],[-43,-41],[-45,-5],[-45,-42],[-46,-43],[-23,1,3,4,14,27,28],[-14,-35,-37],[-12,-36,-37],[-20,-34,-37],[-12,-43,-44],[-20,-41,-44],[-35,2,23,26],[-42,2,23,26],[-8,-30,-37],[-30,-37,-38],[-10,-30,-44],[-30,-44,-45],[-35,5,8],[-42,5,10],[-9,-31,-37],[-31,-37,-39],[-11,-31,-44],[-31,-44,-46],[-32,11,46],[-46,9],[-47,18,25,26,38,45],[-48,20,27,28,39,46],[-49,13,21,33,35],[-50,12,14,15,22,34,41],[-51,40,42],[-52,23,24],[-53,17,19,29,30,31,32],[-54,16],[-55,36,43],[-56,47],[-56,48],[-57,49],[-57,50],[-58,56],[-58,57],[-59,51],[-59,52],[-60,54,55],[-61,54],[-62,53,61],[-62,60],[-63,61],[-64,59,63],[-64,62],[-65,63],[-66,58,65],[-66,64],[66],[-67,37],[-68,44],[-69,67],[-69,68],[69],[-2,-8,-11,-24,-32,-34,-35,-37,-39,-40,-43,-44,-45],[-2,-9,-10,-24,-32,-33,-36,-37,-38,-41,-42,-44,-46],[-4,-9,-10,-23,-32,-33,-36,-37,-38,-41,-42,-44,-46],[-4,-8,-11,-23,-32,-34,-35,-37,-39,-40,-43,-44,-45],[6,8,10,26,31,32,38,45],[7,9,11,28,30,32,39,46]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":35,\"b\":10},{\"tag\":\"incompatible\",\"a\":37,\"b\":29},{\"tag\":\"incompatible\",\"a\":37,\"b\":32},{\"tag\":\"incompatible\",\"a\":39,\"b\":37},{\"tag\":\"incompatible\",\"a\":47,\"b\":13},{\"tag\":\"incompatible\",\"a\":47,\"b\":14},{\"tag\":\"incompatible\",\"a\":47,\"b\":43},{\"tag\":\"incompatible\",\"a\":48,\"b\":14},{\"tag\":\"incompatible\",\"a\":48,\"b\":43},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":14},{\"tag\":\"incompatible\",\"a\":49,\"b\":42},{\"tag\":\"incompatible\",\"a\":49,\"b\":43},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":31},{\"tag\":\"incompatible\",\"a\":51,\"b\":1},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":35},{\"tag\":\"incompatible\",\"a\":53,\"b\":7},{\"tag\":\"incompatible\",\"a\":53,\"b\":32},{\"tag\":\"incompatible\",\"a\":53,\"b\":39},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":33},{\"tag\":\"incompatible\",\"a\":54,\"b\":34},{\"tag\":\"incompatible\",\"a\":54,\"b\":36},{\"tag\":\"incompatible\",\"a\":54,\"b\":46},{\"tag\":\"incompatible\",\"a\":55,\"b\":10},{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":30},{\"tag\":\"incompatible\",\"a\":57,\"b\":38},{\"tag\":\"incompatible\",\"a\":58,\"b\":1},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":30},{\"tag\":\"incompatible\",\"a\":59,\"b\":35},{\"tag\":\"incompatible\",\"a\":59,\"b\":38},{\"tag\":\"incompatible\",\"a\":59,\"b\":52},{\"tag\":\"incompatible\",\"a\":60,\"b\":7},{\"tag\":\"incompatible\",\"a\":60,\"b\":32},{\"tag\":\"incompatible\",\"a\":60,\"b\":39},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":10},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":60},{\"tag\":\"mate\",\"ridge\":19,\"a\":40,\"owners\":[1,7,8,31,44,45]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[31,52,54]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[29,53,54]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[37,51,54]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[29,60,61]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[37,58,61]},{\"tag\":\"mate\",\"ridge\":265,\"a\":52,\"owners\":[6,40,43]},{\"tag\":\"mate\",\"ridge\":266,\"a\":59,\"owners\":[6,40,43]},{\"tag\":\"three\",\"ridge\":161,\"vertices\":[20,47,54]},{\"tag\":\"three\",\"ridge\":161,\"vertices\":[47,54,55]},{\"tag\":\"three\",\"ridge\":162,\"vertices\":[27,47,61]},{\"tag\":\"three\",\"ridge\":162,\"vertices\":[47,61,62]},{\"tag\":\"mate\",\"ridge\":289,\"a\":52,\"owners\":[10,20]},{\"tag\":\"mate\",\"ridge\":290,\"a\":59,\"owners\":[10,27]},{\"tag\":\"three\",\"ridge\":193,\"vertices\":[21,48,54]},{\"tag\":\"three\",\"ridge\":193,\"vertices\":[48,54,56]},{\"tag\":\"three\",\"ridge\":194,\"vertices\":[28,48,61]},{\"tag\":\"three\",\"ridge\":194,\"vertices\":[48,61,63]},{\"tag\":\"mate\",\"ridge\":642,\"a\":49,\"owners\":[28,63]},{\"tag\":\"mate\",\"ridge\":704,\"a\":63,\"owners\":[21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[35,42,43,55,62],\"full_literals\":[-47,18,25,26,38,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[37,44,45,56,63],\"full_literals\":[-48,20,27,28,39,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[30,38,50,52],\"full_literals\":[-49,13,21,33,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[29,31,32,39,51,58],\"full_literals\":[-50,12,14,15,22,34,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[57,59],\"full_literals\":[-51,40,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[40,41],\"full_literals\":[-52,23,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[34,36,46,47,48,49],\"full_literals\":[-53,17,19,29,30,31,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[33],\"full_literals\":[-54,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[53,60],\"full_literals\":[-55,36,43]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-58,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,54,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,53,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-64,59,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-66,58,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-66,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[54],\"full_literals\":[-67,37]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[61],\"full_literals\":[-68,44]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,67,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-69,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[6,20,28,41,49,51,52,54,56,57,60,61,62]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[6,21,27,41,49,50,53,54,55,58,59,61,63]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[8,21,27,40,49,50,53,54,55,58,59,61,63]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[8,20,28,40,49,51,52,54,56,57,60,61,62]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[13,20,27,43,48,49,55,62]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[14,21,28,45,47,49,56,63]}]}"
  "106 64 0 94 93 0\n107 62 0 106 90 0\n108 60 0 107 87 0\n109 67 0 99 97 0\n110 68 0 99 98 0\n111 37 0 109 95 0\n112 44 0 110 96 0\n113 -16 0 111 25 0\n114 -17 0 111 26 0\n115 -19 0 111 27 0\n116 -29 0 111 28 0\n117 -54 0 113 74 0\n118 55 0 117 108 84 0\n119 -61 0 117 85 0\n120 -63 0 119 88 0\n121 53 0 119 107 86 0\n122 -65 0 120 91 0\n123 59 0 120 106 89 0\n124 58 0 122 94 92 0\n125 51 0 123 82 0\n126 52 0 123 83 0\n127 56 0 124 80 0\n128 57 0 124 81 0\n129 47 0 127 76 0\n130 48 0 127 77 0\n131 49 0 128 78 0\n132 50 0 128 79 0\n133 -2 -8 -11 -24 -32 -34 -35 -39 -40 -43 -45 0 111 112 100 0\n134 -2 -9 -10 -24 -32 -33 -36 -38 -41 -42 -46 0 111 112 101 0\n135 -4 -9 -10 -23 -32 -33 -36 -38 -41 -42 -46 0 111 112 102 0\n136 -4 -8 -11 -23 -32 -34 -35 -39 -40 -43 -45 0 111 112 103 0\n137 -7 0 121 114 116 115 6 8 12 73 0\n138 -42 33 35 0 131 36 38 69 0\n139 33 35 0 131 125 138 71 32 33 69 0\n140 -26 30 0 121 114 116 115 9 14 73 0\n141 31 32 26 0 121 114 116 115 111 112 73 5 55 56 57 58 104 0\n142 32 26 0 137 112 111 141 10 11 61 62 63 64 105 0\n143 -20 14 0 111 112 132 2 3 4 50 52 70 0\n144 23 -8 -34 -39 -11 26 0 118 129 125 126 19 139 39 71 20 142 13 30 67 31 75 72 53 133 0\n145 46 5 14 26 0 130 118 112 132 129 125 143 142 16 15 13 65 68 31 75 40 41 42 43 51 70 18 19 139 20 30 39 59 67 71 144 47 136 0\n146 -23 -38 -10 -46 14 -32 0 132 111 118 125 46 75 23 22 49 24 70 35 71 39 139 34 21 66 16 15 47 135 0\n147 5 14 26 0 118 111 132 125 129 126 142 13 145 46 66 75 22 23 24 49 70 35 71 37 39 45 60 139 67 146 72 54 134 0\n148 -5 26 0 129 142 13 1 29 44 67 0\n149 -14 0 111 17 48 139 0\n150 26 0 149 148 147 0\n151 -30 0 150 7 0\n152 0 150 151 140 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070.l) :=
(.branch 2
 (.branch 1
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨0, by decide⟩)))
 (.branch 3
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨0, by decide⟩))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070.g)) :=
(.branch 2
 (.branch 1
 (.leaf ([]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 3
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00017.record070
