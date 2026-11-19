module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00005Frames
public import GraphInputsRow26Part00005Leaves
public import GraphInputsRow26Part00005Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00005.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "15cf08f2e2aaa718e61db0e5385ef04f1e26a96a559715a5395551d70d5352d4745de0f43b0dc3a8ce334cb31cf0ba2d8b52e2b2ae1b16f0761d4731ca719e0f43c4f0f03a158360b81ee05c1c2439514550d50d0b41da0cc328c530ce0b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6d36934db4da4924934924924da493692492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004.data.quota

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00005.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00005.record004" 32

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00005.record004" "{\"ridges\":[[14,268],[17,321],[17,324],[19,265],[19,776],[20,321],[20,448],[21,896],[29,268],[34,324],[35,390],[36,774],[41,330],[42,265],[42,394],[44,776],[50,448],[52,321],[53,896],[55,268],[56,268],[57,324],[58,268],[58,776],[60,324],[62,420],[63,324],[64,265],[64,344],[65,424],[67,776],[69,448],[69,896],[72,774],[77,394],[77,776],[79,448],[79,834],[80,324],[80,344]],\"owners\":[[14,268,[71,72,80],[29,55,56,57,58]],[29,268,[80],[14,55,56,57,58,71,72]],[55,268,[71,72],[14,29,56,57,58,80]],[56,268,[71,72,80],[14,29,55,57,58]],[58,268,[71,80],[14,29,55,56,57,72]],[20,321,[17,34,41,52,57,60,64],[50,69]],[17,324,[71,75,80],[34,57,60,63]],[34,324,[80],[17,57,60,63,71,75]],[57,324,[75],[17,34,60,63,71,80]],[60,324,[71,75],[17,34,57,63,80]],[63,324,[71,80],[17,34,57,60,75]],[80,324,[17,34,63,75],[57,60,71]],[19,776,[72,77],[44,58,67]],[44,776,[],[19,58,67,72,77]],[58,776,[77],[19,44,67,72]],[67,776,[72],[19,44,58,77]],[77,776,[19,58],[44,67,72]],[20,448,[75,79],[50,63,69]],[50,448,[],[20,63,69,75,79]],[69,448,[75],[20,50,63,79]],[79,448,[20,63],[50,69,75]],[21,896,[77,79],[53,67,69]],[53,896,[],[21,67,69,77,79]],[69,896,[77],[21,53,67,79]],[35,390,[75],[]],[36,774,[72],[]],[72,774,[36],[]],[41,330,[71],[]],[42,394,[77],[]],[77,394,[42],[]],[79,834,[52],[]],[62,420,[],[]],[64,344,[80],[]],[80,344,[64],[]],[65,424,[],[]]],\"edges\":[[22,[14,17,29,34,35,36,55,56,57,58,60,62,63,71,72,75,80]],[40,[17,20,34,41,50,52,57,60,63,64,69,71,75,79,80]],[42,[20,21,35,42,50,53,62,63,65,67,69,75,77,79]],[44,[19,21,36,44,52,53,58,67,69,72,77,79]]],\"groupings\":[]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00005.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00005.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-23,-19],[-23,-22],[-25,-9],[-27,-9],[-27,-14],[-28,-14],[-28,-27],[-29,-9],[-29,-14],[-29,-28],[-30,-27],[-30,-29],[-31,-7],[-31,-27],[-31,-28],[-31,-29],[-3,-11,-23],[-1,27,28,32],[-6,32],[-16,27,28],[-17,27,28,32],[-19,27,32],[-4,2,7,10,14,18,20,23],[-2,-4,-14],[-2,27,29,32],[-7,32],[-18,29],[-20,27,29],[-22,27,32],[-32,2,7,22,29],[-3,28,30],[-12],[-19,30],[-25,28],[-30,3,19],[-4,29,31],[-13],[-26,29],[-31,4,22],[-5,30,31],[-15],[-26,30],[-8,29],[-9,28],[-28,9],[-10,27],[-11,30],[-30,11],[-31,14],[-21],[-23,32],[-32,23],[-24],[1,2,6,7,8,9,16,17,18,19,20,21,22,27,28,29,32],[2,4,7,10,13,14,18,20,22,23,26,27,29,31,32],[4,5,8,11,13,15,21,22,24,25,26,29,30,31],[3,5,9,12,14,15,19,25,26,28,30,31]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80}],\"rules\":[{\"tag\":\"incompatible\",\"a\":64,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":67,\"b\":36},{\"tag\":\"incompatible\",\"a\":71,\"b\":36},{\"tag\":\"incompatible\",\"a\":71,\"b\":52},{\"tag\":\"incompatible\",\"a\":72,\"b\":52},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":75,\"b\":36},{\"tag\":\"incompatible\",\"a\":75,\"b\":52},{\"tag\":\"incompatible\",\"a\":75,\"b\":72},{\"tag\":\"incompatible\",\"a\":77,\"b\":71},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":79,\"b\":34},{\"tag\":\"incompatible\",\"a\":79,\"b\":71},{\"tag\":\"incompatible\",\"a\":79,\"b\":72},{\"tag\":\"incompatible\",\"a\":79,\"b\":75},{\"tag\":\"three\",\"ridge\":265,\"vertices\":[19,42,64]},{\"tag\":\"mate\",\"ridge\":268,\"a\":14,\"owners\":[71,72,80]},{\"tag\":\"mate\",\"ridge\":268,\"a\":29,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":268,\"a\":55,\"owners\":[71,72]},{\"tag\":\"mate\",\"ridge\":268,\"a\":56,\"owners\":[71,72,80]},{\"tag\":\"mate\",\"ridge\":268,\"a\":58,\"owners\":[71,80]},{\"tag\":\"mate\",\"ridge\":321,\"a\":20,\"owners\":[17,34,41,52,57,60,64]},{\"tag\":\"three\",\"ridge\":321,\"vertices\":[17,20,52]},{\"tag\":\"mate\",\"ridge\":324,\"a\":17,\"owners\":[71,75,80]},{\"tag\":\"mate\",\"ridge\":324,\"a\":34,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":324,\"a\":57,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":324,\"a\":60,\"owners\":[71,75]},{\"tag\":\"mate\",\"ridge\":324,\"a\":63,\"owners\":[71,80]},{\"tag\":\"mate\",\"ridge\":324,\"a\":80,\"owners\":[17,34,63,75]},{\"tag\":\"mate\",\"ridge\":776,\"a\":19,\"owners\":[72,77]},{\"tag\":\"mate\",\"ridge\":776,\"a\":44,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":776,\"a\":58,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":776,\"a\":67,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":776,\"a\":77,\"owners\":[19,58]},{\"tag\":\"mate\",\"ridge\":448,\"a\":20,\"owners\":[75,79]},{\"tag\":\"mate\",\"ridge\":448,\"a\":50,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":448,\"a\":69,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":448,\"a\":79,\"owners\":[20,63]},{\"tag\":\"mate\",\"ridge\":896,\"a\":21,\"owners\":[77,79]},{\"tag\":\"mate\",\"ridge\":896,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":896,\"a\":69,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":390,\"a\":35,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":774,\"a\":36,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":774,\"a\":72,\"owners\":[36]},{\"tag\":\"mate\",\"ridge\":330,\"a\":41,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":394,\"a\":42,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":394,\"a\":77,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":834,\"a\":79,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":420,\"a\":62,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":344,\"a\":64,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":344,\"a\":80,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":424,\"a\":65,\"owners\":[]},{\"tag\":\"edge\",\"edge\":22,\"owners\":[14,17,29,34,35,36,55,56,57,58,60,62,63,71,72,75,80]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[17,20,34,41,50,52,57,60,63,64,69,71,75,79,80]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[20,21,35,42,50,53,62,63,65,67,69,75,77,79]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[19,21,36,44,52,53,58,67,69,72,77,79]}]}"
  "p cnf 32 57\n-23 -19 0\n-23 -22 0\n-25 -9 0\n-27 -9 0\n-27 -14 0\n-28 -14 0\n-28 -27 0\n-29 -9 0\n-29 -14 0\n-29 -28 0\n-30 -27 0\n-30 -29 0\n-31 -7 0\n-31 -27 0\n-31 -28 0\n-31 -29 0\n-3 -11 -23 0\n-1 27 28 32 0\n-6 32 0\n-16 27 28 0\n-17 27 28 32 0\n-19 27 32 0\n-4 2 7 10 14 18 20 23 0\n-2 -4 -14 0\n-2 27 29 32 0\n-7 32 0\n-18 29 0\n-20 27 29 0\n-22 27 32 0\n-32 2 7 22 29 0\n-3 28 30 0\n-12 0\n-19 30 0\n-25 28 0\n-30 3 19 0\n-4 29 31 0\n-13 0\n-26 29 0\n-31 4 22 0\n-5 30 31 0\n-15 0\n-26 30 0\n-8 29 0\n-9 28 0\n-28 9 0\n-10 27 0\n-11 30 0\n-30 11 0\n-31 14 0\n-21 0\n-23 32 0\n-32 23 0\n-24 0\n1 2 6 7 8 9 16 17 18 19 20 21 22 27 28 29 32 0\n2 4 7 10 13 14 18 20 22 23 26 27 29 31 32 0\n4 5 8 11 13 15 21 22 24 25 26 29 30 31 0\n3 5 9 12 14 15 19 25 26 28 30 31 0\n"
  "58 1 2 6 7 8 9 16 17 18 19 20 22 27 28 29 32 0 50 54 0\n59 2 4 7 10 14 18 20 22 23 26 27 29 31 32 0 37 55 0\n60 4 5 8 11 22 25 26 29 30 31 0 37 41 50 53 56 0\n61 3 5 9 14 19 25 26 28 30 31 0 32 41 57 0\n62 -25 0 3 34 45 0\n63 14 31 2 10 7 18 20 22 23 26 27 29 32 0 59 23 0\n64 -28 27 32 29 0 29 28 25 46 51 26 38 27 6 15 63 0\n65 27 32 29 0 26 19 43 27 22 25 28 29 64 44 18 20 21 58 0\n66 -27 26 0 62 4 5 7 11 14 33 31 40 61 0\n67 30 31 29 0 62 36 38 66 65 52 2 43 47 40 60 0\n68 -30 -23 0 1 35 48 17 0\n69 27 29 0 65 52 2 68 67 13 39 49 30 24 0\n70 29 0 38 66 69 0\n71 -9 0 70 8 0\n72 -14 0 70 9 0\n73 -28 0 70 10 0\n74 -30 0 70 12 0\n75 -31 0 70 16 0\n76 -19 0 74 33 0\n77 -26 0 74 42 0\n78 -3 0 74 73 31 0\n79 -5 0 75 74 40 0\n80 0 79 78 72 71 76 62 77 73 74 75 61 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00005.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00005.record055
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "354e334c9707ce4ab2aaa3a1eb86c5876a386e8785e0f9e1e45b15c789724e91e785c5475c368d6354d1b61d1743de0f13a4d932cc73a2c6b86c5b0ef07a1d8719e1745c570de0f23c4f0bc1fc5154a28aa85a0e544712a469515151544d28c3322c2b05c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "26db6d36d34d36db4da4d26da4d36db4926d36da492492249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 23), (facetIndex 37), (facetIndex 67), (facetIndex 73)]))
 (.branch 2
 (.leaf ([(facetIndex 27), (facetIndex 53), (facetIndex 69), (facetIndex 80)]))
 (.leaf ([(facetIndex 25), (facetIndex 33), (facetIndex 38), (facetIndex 39)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 22), (facetIndex 26), (facetIndex 45), (facetIndex 48)]))
 (.leaf ([(facetIndex 21), (facetIndex 36), (facetIndex 47), (facetIndex 56)])))
 (.branch 6
 (.leaf ([(facetIndex 52), (facetIndex 55), (facetIndex 59)]))
 (.leaf ([(facetIndex 20), (facetIndex 24), (facetIndex 28), (facetIndex 65)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1000000008030000a04a0d0038180004840100062d60e6000000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 57), (facetIndex 62)]))
 (.branch 2
 (.leaf ([(facetIndex 29), (facetIndex 34), (facetIndex 44)]))
 (.leaf ([(facetIndex 63), (facetIndex 64), (facetIndex 66)]))))
 (.branch 4
 (.leaf ([(facetIndex 68), (facetIndex 71), (facetIndex 76)]))
 (.branch 5
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 60), (facetIndex 74)]))
 (.leaf ([(facetIndex 77), (facetIndex 78)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 30), (facetIndex 32), (facetIndex 75)]))
 (.branch 8
 (.leaf ([(facetIndex 31), (facetIndex 49), (facetIndex 70)]))
 (.leaf ([(facetIndex 35), (facetIndex 72)]))))
 (.branch 10
 (.leaf ([(facetIndex 42), (facetIndex 46), (facetIndex 50), (facetIndex 51), (facetIndex 61)]))
 (.branch 11
 (.leaf ([(facetIndex 54), (facetIndex 58), (facetIndex 79)]))
 (.leaf ([(facetIndex 43)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "a55364083703020220940a000a0099700901b94400008106761z1d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [1, 2]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [3, 4, 5, 6]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6]
def grouped2_0010 : List Nat := [6]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1, 2]
def grouped3_0013 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [1, 2]
def grouped3_0017 : List Nat := [2]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [3, 4, 5]
def grouped3_0020 : List Nat := [4]
def grouped3_0021 : List Nat := [4, 5]
def grouped3_0022 : List Nat := [5]
def grouped3_0023 : List Nat := [6]
def grouped3_0024 : List Nat := [6, 7, 8]
def grouped3_0025 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0026 : List Nat := [7]
def grouped3_0027 : List Nat := [7, 8]
def grouped3_0028 : List Nat := [8]
def grouped3_0029 : List Nat := [9]
def grouped3_0030 : List Nat := [9, 10, 11]
def grouped3_0031 : List Nat := [10]
def grouped3_0032 : List Nat := [10, 11]
def grouped3_0033 : List Nat := [11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00005.record055" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0032\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0032\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00005.record055" 89

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00005.record055" "{\"ridges\":[[6,76],[10,97],[10,104],[12,112],[14,524],[17,648],[22,76],[24,524],[30,390],[36,104],[37,648],[38,112],[40,402],[43,385],[43,896],[45,76],[47,76],[47,104],[48,76],[49,396],[52,112],[53,772],[53,784],[54,385],[55,104],[55,112],[56,97],[56,104],[57,456],[58,896],[59,112],[60,432],[61,657],[62,480],[65,524],[67,524],[69,784],[71,90],[72,568],[73,648],[74,688],[75,402],[76,60],[77,600],[78,840],[79,396],[79,896],[80,772],[80,784]],\"owners\":[[6,76,[64,66,76,77,78],[22,45,47,48]],[22,76,[76,77,78],[6,45,47,48,64,66]],[45,76,[66,78],[6,22,47,48,64,76,77]],[47,76,[64,77,78],[6,22,45,48,66,76]],[48,76,[64,66,76,77],[6,22,45,47,78]],[10,97,[12,29,38,52,59,62],[36,47,56]],[56,97,[12,29,38,52,59],[10,36,47,62]],[10,104,[66,71,76],[36,47,55,56]],[36,104,[76],[10,47,55,56,66,71]],[47,104,[71],[10,36,55,56,66,76]],[55,104,[66],[10,36,47,56,71,76]],[56,104,[66,71,76],[10,36,47,55]],[12,112,[68,71,76],[38,52,55,59]],[38,112,[76],[12,52,55,59,68,71]],[52,112,[71],[12,38,55,59,68,76]],[55,112,[68],[12,38,52,59,71,76]],[59,112,[68,71,76],[12,38,52,55]],[14,524,[46,50,51,77,78,79],[24,65,67]],[24,524,[77,78,79],[14,46,50,51,65,67]],[65,524,[50,51,78,79],[14,24,46,67,77]],[67,524,[46,51,77,78],[14,24,50,65,79]],[17,648,[50,58,79],[37,67,73]],[37,648,[79],[17,50,58,67,73]],[73,648,[50,58,79],[17,37,67]],[53,772,[70,78,79],[19,32,51,54,69,80]],[80,772,[32,51,54,70,79],[19,53,69,78]],[53,784,[75],[19,42,61,69,80]],[69,784,[61],[19,42,53,75,80]],[80,784,[42,61,75],[19,53,69]],[43,385,[49,57,60,62],[30,40,54,58,61]],[54,385,[40,57,60,62],[30,43,49,58,61]],[30,390,[70],[]],[71,90,[34,64],[]],[40,402,[75],[]],[75,402,[40],[]],[61,657,[41],[]],[43,896,[79],[54,58,61,70,75]],[58,896,[70,75],[43,54,61,79]],[79,896,[43,61,75],[54,58,70]],[76,60,[44,63],[]],[49,396,[79],[]],[79,396,[49],[]],[57,456,[],[]],[60,432,[],[]],[62,480,[],[]],[72,568,[],[]],[74,688,[],[]],[77,600,[],[]],[78,840,[],[]]],\"edges\":[[26,[6,10,22,34,36,45,47,48,55,56,57,64,66,71,76,77,78]],[29,[14,17,24,35,37,46,50,51,58,65,67,72,73,77,78,79]],[35,[10,12,29,36,38,47,52,55,56,59,62,66,68,71,76]],[42,[30,40,43,49,54,57,58,60,61,62,70,75,79]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00005.record055" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00005.record055\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-17,-8],[-17,-11],[-18,-13],[-20,-8],[-23,-18],[-27,-18],[-28,-18],[-30,-20],[-35,-18],[-46,-20],[-47,-8],[-47,-17],[-47,-19],[-52,-20],[-1,41,43,53,54,55],[-6,53,54,55],[-22,43,55],[-24,41,54,55],[-25,41,43,53,54],[-2,3,9,16,29,36,39],[-33,3,9,16,29,36],[-2,43,48,53],[-14,53],[-24,48],[-32,43],[-33,43,48,53],[-3,45,48,53],[-16,53],[-29,48],[-32,45],[-36,45,48,53],[-4,23,27,28,54,55,56],[-7,54,55,56],[-42,27,28,55,56],[-44,23,28,54,55],[-5,27,35,56],[-15,56],[-50,27,35,56],[-30,47,55,56],[-57,11,28,31,47,56],[-30,52],[-46,38],[-57,19,38,52],[-20,26,34,37,39],[-31,17,34,37,39],[-10,47],[-48,12,41],[-17,52],[-52,17],[-38,18],[-20,56],[-35,47,52],[-56,20,38,52],[-53,21,40],[-26,56],[-56,26],[-34],[-37],[-39],[-49],[-51],[-54],[-55],[-58,8,30,46,57],[-59,29,32,36],[-60,58],[-61,60],[-62,59],[-63,62],[-64,61],[-64,63],[64],[-9,65],[-12,65],[-21,65],[-40,66],[-41,66],[-43,66],[-45,67],[-48,67],[-53,67],[-68,17,18,37,51],[-17,68],[-18,68],[-52,69],[-26,70],[-19,71],[-28,71],[-38,71],[-31,72],[-56,72],[-73,20],[-20,73],[-66,74],[-65,74],[-74,75],[-68,76],[-67,77],[-67,-76,78],[-77,79],[-75,79],[-75,-78,80],[-70,81],[-81,82],[-69,82],[-72,83],[-84,73],[-72,-73,84],[-83,85],[-71,85],[-86,84],[-71,-84,86],[-82,-85,87],[-82,-86,88],[-79,-88,89],[-80,-87,89],[-89],[1,2,6,12,14,22,24,25,32,33,34,41,43,48,53,54,55],[4,5,7,13,15,23,27,28,35,42,44,49,50,54,55,56],[2,3,9,14,16,24,29,32,33,36,39,43,45,48,53],[10,17,20,26,31,34,35,37,38,39,47,52,56]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":40,\"b\":27},{\"tag\":\"incompatible\",\"a\":40,\"b\":32},{\"tag\":\"incompatible\",\"a\":41,\"b\":35},{\"tag\":\"incompatible\",\"a\":43,\"b\":27},{\"tag\":\"incompatible\",\"a\":46,\"b\":41},{\"tag\":\"incompatible\",\"a\":50,\"b\":41},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":53,\"b\":43},{\"tag\":\"incompatible\",\"a\":58,\"b\":41},{\"tag\":\"incompatible\",\"a\":69,\"b\":43},{\"tag\":\"incompatible\",\"a\":70,\"b\":27},{\"tag\":\"incompatible\",\"a\":70,\"b\":40},{\"tag\":\"incompatible\",\"a\":70,\"b\":42},{\"tag\":\"incompatible\",\"a\":75,\"b\":43},{\"tag\":\"mate\",\"ridge\":76,\"a\":6,\"owners\":[64,66,76,77,78]},{\"tag\":\"mate\",\"ridge\":76,\"a\":22,\"owners\":[76,77,78]},{\"tag\":\"mate\",\"ridge\":76,\"a\":45,\"owners\":[66,78]},{\"tag\":\"mate\",\"ridge\":76,\"a\":47,\"owners\":[64,77,78]},{\"tag\":\"mate\",\"ridge\":76,\"a\":48,\"owners\":[64,66,76,77]},{\"tag\":\"mate\",\"ridge\":97,\"a\":10,\"owners\":[12,29,38,52,59,62]},{\"tag\":\"mate\",\"ridge\":97,\"a\":56,\"owners\":[12,29,38,52,59]},{\"tag\":\"mate\",\"ridge\":104,\"a\":10,\"owners\":[66,71,76]},{\"tag\":\"mate\",\"ridge\":104,\"a\":36,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":104,\"a\":47,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":104,\"a\":55,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":104,\"a\":56,\"owners\":[66,71,76]},{\"tag\":\"mate\",\"ridge\":112,\"a\":12,\"owners\":[68,71,76]},{\"tag\":\"mate\",\"ridge\":112,\"a\":38,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":112,\"a\":52,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":112,\"a\":55,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":112,\"a\":59,\"owners\":[68,71,76]},{\"tag\":\"mate\",\"ridge\":524,\"a\":14,\"owners\":[46,50,51,77,78,79]},{\"tag\":\"mate\",\"ridge\":524,\"a\":24,\"owners\":[77,78,79]},{\"tag\":\"mate\",\"ridge\":524,\"a\":65,\"owners\":[50,51,78,79]},{\"tag\":\"mate\",\"ridge\":524,\"a\":67,\"owners\":[46,51,77,78]},{\"tag\":\"mate\",\"ridge\":648,\"a\":17,\"owners\":[50,58,79]},{\"tag\":\"mate\",\"ridge\":648,\"a\":37,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":648,\"a\":73,\"owners\":[50,58,79]},{\"tag\":\"mate\",\"ridge\":772,\"a\":53,\"owners\":[70,78,79]},{\"tag\":\"mate\",\"ridge\":772,\"a\":80,\"owners\":[32,51,54,70,79]},{\"tag\":\"mate\",\"ridge\":784,\"a\":53,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":784,\"a\":69,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":784,\"a\":80,\"owners\":[42,61,75]},{\"tag\":\"mate\",\"ridge\":385,\"a\":43,\"owners\":[49,57,60,62]},{\"tag\":\"mate\",\"ridge\":385,\"a\":54,\"owners\":[40,57,60,62]},{\"tag\":\"mate\",\"ridge\":390,\"a\":30,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":90,\"a\":71,\"owners\":[34,64]},{\"tag\":\"mate\",\"ridge\":402,\"a\":40,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":402,\"a\":75,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":657,\"a\":61,\"owners\":[41]},{\"tag\":\"mate\",\"ridge\":896,\"a\":43,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":896,\"a\":58,\"owners\":[70,75]},{\"tag\":\"mate\",\"ridge\":896,\"a\":79,\"owners\":[43,61,75]},{\"tag\":\"mate\",\"ridge\":60,\"a\":76,\"owners\":[44,63]},{\"tag\":\"mate\",\"ridge\":396,\"a\":49,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":396,\"a\":79,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":456,\"a\":57,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":432,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":480,\"a\":62,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":568,\"a\":72,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":688,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":600,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":840,\"a\":78,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[27,53,69,80],\"full_literals\":[-58,8,30,46,57]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[52,55,59],\"full_literals\":[-59,29,32,36]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-64,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-64,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":29,\"full_literals\":[-9,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":34,\"full_literals\":[-12,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":44,\"full_literals\":[-21,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":63,\"full_literals\":[-40,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":64,\"full_literals\":[-41,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-43,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":68,\"full_literals\":[-45,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-48,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-53,67]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[40,41,60,74],\"full_literals\":[-68,17,18,37,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":40,\"full_literals\":[-17,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":41,\"full_literals\":[-18,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-52,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":49,\"full_literals\":[-26,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":42,\"full_literals\":[-19,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":51,\"full_literals\":[-28,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":61,\"full_literals\":[-38,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":54,\"full_literals\":[-31,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":79,\"full_literals\":[-56,72]},{\"tag\":\"group_or\",\"kind\":3,\"index\":11,\"members\":[43],\"full_literals\":[-73,20]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":43,\"full_literals\":[-20,73]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-67,-76,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-75,-78,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-81,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0033\",\"joined_name\":\"grouped3_0032\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0033\",\"joined_name\":\"grouped3_0032\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-84,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0033\",\"joined_name\":\"grouped3_0032\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-72,-73,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,false,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-71,-84,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-82,-85,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-82,-86,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-79,-88,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-80,-87,89],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":26,\"owners\":[6,10,22,34,36,45,47,48,55,56,57,64,66,71,76,77,78]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[14,17,24,35,37,46,50,51,58,65,67,72,73,77,78,79]},{\"tag\":\"edge\",\"edge\":35,\"owners\":[10,12,29,36,38,47,52,55,56,59,62,66,68,71,76]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[30,40,43,49,54,57,58,60,61,62,70,75,79]}]}"
  "p cnf 89 121\n-17 -8 0\n-17 -11 0\n-18 -13 0\n-20 -8 0\n-23 -18 0\n-27 -18 0\n-28 -18 0\n-30 -20 0\n-35 -18 0\n-46 -20 0\n-47 -8 0\n-47 -17 0\n-47 -19 0\n-52 -20 0\n-1 41 43 53 54 55 0\n-6 53 54 55 0\n-22 43 55 0\n-24 41 54 55 0\n-25 41 43 53 54 0\n-2 3 9 16 29 36 39 0\n-33 3 9 16 29 36 0\n-2 43 48 53 0\n-14 53 0\n-24 48 0\n-32 43 0\n-33 43 48 53 0\n-3 45 48 53 0\n-16 53 0\n-29 48 0\n-32 45 0\n-36 45 48 53 0\n-4 23 27 28 54 55 56 0\n-7 54 55 56 0\n-42 27 28 55 56 0\n-44 23 28 54 55 0\n-5 27 35 56 0\n-15 56 0\n-50 27 35 56 0\n-30 47 55 56 0\n-57 11 28 31 47 56 0\n-30 52 0\n-46 38 0\n-57 19 38 52 0\n-20 26 34 37 39 0\n-31 17 34 37 39 0\n-10 47 0\n-48 12 41 0\n-17 52 0\n-52 17 0\n-38 18 0\n-20 56 0\n-35 47 52 0\n-56 20 38 52 0\n-53 21 40 0\n-26 56 0\n-56 26 0\n-34 0\n-37 0\n-39 0\n-49 0\n-51 0\n-54 0\n-55 0\n-58 8 30 46 57 0\n-59 29 32 36 0\n-60 58 0\n-61 60 0\n-62 59 0\n-63 62 0\n-64 61 0\n-64 63 0\n64 0\n-9 65 0\n-12 65 0\n-21 65 0\n-40 66 0\n-41 66 0\n-43 66 0\n-45 67 0\n-48 67 0\n-53 67 0\n-68 17 18 37 51 0\n-17 68 0\n-18 68 0\n-52 69 0\n-26 70 0\n-19 71 0\n-28 71 0\n-38 71 0\n-31 72 0\n-56 72 0\n-73 20 0\n-20 73 0\n-66 74 0\n-65 74 0\n-74 75 0\n-68 76 0\n-67 77 0\n-67 -76 78 0\n-77 79 0\n-75 79 0\n-75 -78 80 0\n-70 81 0\n-81 82 0\n-69 82 0\n-72 83 0\n-84 73 0\n-72 -73 84 0\n-83 85 0\n-71 85 0\n-86 84 0\n-71 -84 86 0\n-82 -85 87 0\n-82 -86 88 0\n-79 -88 89 0\n-80 -87 89 0\n-89 0\n1 2 6 12 14 22 24 25 32 33 34 41 43 48 53 54 55 0\n4 5 7 13 15 23 27 28 35 42 44 49 50 54 55 56 0\n2 3 9 14 16 24 29 32 33 36 39 43 45 48 53 0\n10 17 20 26 31 34 35 37 38 39 47 52 56 0\n"
  "122 61 0 72 70 0\n123 63 0 72 71 0\n124 60 0 122 67 0\n125 62 0 123 69 0\n126 58 0 124 66 0\n127 59 0 125 68 0\n128 -68 17 18 0 58 61 82 0\n129 1 2 6 12 14 22 24 25 32 33 41 43 48 53 0 57 62 63 118 0\n130 4 5 7 13 15 23 27 28 35 42 44 50 56 0 60 62 63 119 0\n131 2 3 9 14 16 24 29 32 33 36 43 45 48 53 0 59 120 0\n132 10 17 20 26 31 35 38 47 52 56 0 57 58 59 121 0\n133 79 0 59 100 101 98 96 79 80 81 94 95 27 30 31 24 29 23 28 78 73 20 21 131 0\n134 -88 0 133 117 115 0\n135 -86 0 134 59 58 57 111 114 107 104 92 103 44 86 0\n136 -84 0 135 126 107 112 92 87 89 4 8 10 14 43 64 0\n137 67 0 127 79 80 81 30 31 29 65 0\n138 74 0 63 62 94 95 76 77 78 74 75 54 18 47 17 22 25 26 15 19 16 23 129 0\n139 75 0 138 96 0\n140 47 56 10 26 20 17 38 31 52 0 132 52 0\n141 47 56 68 0 57 58 59 55 51 84 50 83 49 45 46 140 0\n142 -47 68 0 126 84 50 42 83 49 41 11 13 64 43 0\n143 -56 52 38 0 136 53 91 93 108 0\n144 68 0 83 84 49 50 142 141 143 0\n145 76 0 144 97 0\n146 78 0 145 137 99 0\n147 80 0 146 139 102 0\n148 -87 0 147 117 116 0\n149 -56 0 148 56 91 86 106 103 109 104 113 0\n150 -15 0 149 37 0\n151 -7 0 149 62 63 33 0\n152 -18 0 63 62 149 150 151 3 5 6 7 9 32 34 38 36 35 130 0\n153 -38 0 152 50 0\n154 17 0 152 144 128 0\n155 -46 0 153 42 0\n156 -8 0 154 1 0\n157 -11 0 154 2 0\n158 -47 0 154 12 0\n159 52 0 154 48 0\n160 -30 0 158 63 149 39 0\n161 69 0 159 85 0\n162 57 0 160 126 155 156 64 0\n163 82 0 161 105 0\n164 -85 0 163 148 113 0\n165 -83 0 164 109 0\n166 -71 0 164 110 0\n167 -72 0 165 106 0\n168 -28 0 166 88 0\n169 -31 0 167 90 0\n170 0 168 169 157 162 158 149 40 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00005.record055
