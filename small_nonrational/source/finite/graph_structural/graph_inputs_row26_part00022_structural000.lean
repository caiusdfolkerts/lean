module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00022Frames
public import GraphInputsRow26Part00022Leaves
public import GraphInputsRow26Part00022Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00022.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "6d34ccb31c4f32a3ab1a3693a2eac6c98e6c58d64d8b6c3a4e8b92e1ba1e4785e0f9b1d24e9365392e745694e5654d54d4b5c364d5352d1b51d1743d38cd34ccb3c2e4b32d2b2ac6b46c9b16c3bc1e4749c6745c570de0f43c4f0bc1f92a46318a625929464c5494a54549530ca324c4b0ac1b21c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6da69a69a6db6db6da6d24926da69b49a69249249a4924da489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 24), (facetIndex 32), (facetIndex 42), (facetIndex 76)]))
 (.leaf ([(facetIndex 78), (facetIndex 80), (facetIndex 82), (facetIndex 84)])))
 (.branch 3
 (.leaf ([(facetIndex 56), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 37), (facetIndex 38), (facetIndex 40)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 50), (facetIndex 52), (facetIndex 57), (facetIndex 64)]))
 (.leaf ([(facetIndex 36), (facetIndex 39), (facetIndex 41), (facetIndex 44), (facetIndex 46), (facetIndex 47)])))
 (.branch 7
 (.leaf ([(facetIndex 27), (facetIndex 28), (facetIndex 29), (facetIndex 30), (facetIndex 31)]))
 (.leaf ([(facetIndex 22), (facetIndex 23)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "10410400000000040124a2004100b4502badd6c0db6c00fcz10;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00022.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00022.record003" 35

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00022.record003" "{\"ridges\":[[32,580],[37,280],[40,296],[42,584],[76,580],[76,584],[94,332]],\"owners\":[[37,280,[91,92],[15,50,64,71,86,88]],[40,296,[91,93],[16,52,64,74,86,90]],[32,580,[94],[20,54,62,76,84]],[76,580,[62],[20,32,54,84,94]],[42,584,[94],[21,54,67,76]],[76,584,[67],[21,42,54,94]],[94,332,[53],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00022.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00022.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-3,-1],[-3,-2],[-5,-1],[-5,-2],[-5,-3],[-6,-1],[-6,-2],[-6,-3],[-8,-1],[-8,-2],[-8,-3],[-14,-13],[-15,-14],[-16,-13],[-17,-16],[-18,-1],[-18,-2],[-18,-11],[-18,-12],[-19,-1],[-19,-2],[-19,-3],[-20,-1],[-20,-2],[-20,-3],[-21,-1],[-21,-2],[-21,-3],[-22,-1],[-22,-2],[-22,-11],[-22,-12],[-7,19,20],[-9,19,21],[-4,22],[-18,15],[-10,22],[-18,17],[-22,13],[-23,3,4,10,18],[-24,5,6,7,8,9],[-25,11,12,14,16],[-26,1,2],[-27,23],[-28,24],[-29,27,28],[-30,27],[-30,28],[-31,25],[-32,26],[-33,31,32],[-34,32],[-35,29],[-35,30,34],[-35,33],[35]],\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":24,\"b\":22},{\"tag\":\"incompatible\",\"a\":24,\"b\":23},{\"tag\":\"incompatible\",\"a\":34,\"b\":22},{\"tag\":\"incompatible\",\"a\":34,\"b\":23},{\"tag\":\"incompatible\",\"a\":34,\"b\":24},{\"tag\":\"incompatible\",\"a\":35,\"b\":22},{\"tag\":\"incompatible\",\"a\":35,\"b\":23},{\"tag\":\"incompatible\",\"a\":35,\"b\":24},{\"tag\":\"incompatible\",\"a\":38,\"b\":22},{\"tag\":\"incompatible\",\"a\":38,\"b\":23},{\"tag\":\"incompatible\",\"a\":38,\"b\":24},{\"tag\":\"incompatible\",\"a\":57,\"b\":53},{\"tag\":\"incompatible\",\"a\":62,\"b\":57},{\"tag\":\"incompatible\",\"a\":64,\"b\":53},{\"tag\":\"incompatible\",\"a\":67,\"b\":64},{\"tag\":\"incompatible\",\"a\":76,\"b\":22},{\"tag\":\"incompatible\",\"a\":76,\"b\":23},{\"tag\":\"incompatible\",\"a\":76,\"b\":50},{\"tag\":\"incompatible\",\"a\":76,\"b\":52},{\"tag\":\"incompatible\",\"a\":91,\"b\":22},{\"tag\":\"incompatible\",\"a\":91,\"b\":23},{\"tag\":\"incompatible\",\"a\":91,\"b\":24},{\"tag\":\"incompatible\",\"a\":92,\"b\":22},{\"tag\":\"incompatible\",\"a\":92,\"b\":23},{\"tag\":\"incompatible\",\"a\":92,\"b\":24},{\"tag\":\"incompatible\",\"a\":93,\"b\":22},{\"tag\":\"incompatible\",\"a\":93,\"b\":23},{\"tag\":\"incompatible\",\"a\":93,\"b\":24},{\"tag\":\"incompatible\",\"a\":94,\"b\":22},{\"tag\":\"incompatible\",\"a\":94,\"b\":23},{\"tag\":\"incompatible\",\"a\":94,\"b\":50},{\"tag\":\"incompatible\",\"a\":94,\"b\":52},{\"tag\":\"mate\",\"ridge\":280,\"a\":37,\"owners\":[91,92]},{\"tag\":\"mate\",\"ridge\":296,\"a\":40,\"owners\":[91,93]},{\"tag\":\"mate\",\"ridge\":580,\"a\":32,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":580,\"a\":76,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":584,\"a\":42,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":584,\"a\":76,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":332,\"a\":94,\"owners\":[53]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[24,32,42,76],\"full_literals\":[-23,3,4,10,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[34,35,37,38,40],\"full_literals\":[-24,5,6,7,8,9]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[50,52,57,64],\"full_literals\":[-25,11,12,14,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[22,23],\"full_literals\":[-26,1,2]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-27,23,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-28,false,24],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-29,27,28],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-30,27,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-30,false,28],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-31,25,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-32,false,26],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-33,31,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-34,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-35,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-35,30,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-35,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true}]}"
  "p cnf 35 56\n-3 -1 0\n-3 -2 0\n-5 -1 0\n-5 -2 0\n-5 -3 0\n-6 -1 0\n-6 -2 0\n-6 -3 0\n-8 -1 0\n-8 -2 0\n-8 -3 0\n-14 -13 0\n-15 -14 0\n-16 -13 0\n-17 -16 0\n-18 -1 0\n-18 -2 0\n-18 -11 0\n-18 -12 0\n-19 -1 0\n-19 -2 0\n-19 -3 0\n-20 -1 0\n-20 -2 0\n-20 -3 0\n-21 -1 0\n-21 -2 0\n-21 -3 0\n-22 -1 0\n-22 -2 0\n-22 -11 0\n-22 -12 0\n-7 19 20 0\n-9 19 21 0\n-4 22 0\n-18 15 0\n-10 22 0\n-18 17 0\n-22 13 0\n-23 3 4 10 18 0\n-24 5 6 7 8 9 0\n-25 11 12 14 16 0\n-26 1 2 0\n-27 23 0\n-28 24 0\n-29 27 28 0\n-30 27 0\n-30 28 0\n-31 25 0\n-32 26 0\n-33 31 32 0\n-34 32 0\n-35 29 0\n-35 30 34 0\n-35 33 0\n35 0\n"
  "57 29 0 56 53 0\n58 33 0 56 55 0\n59 -22 -26 0 29 30 43 0\n60 -22 0 58 31 32 39 59 12 14 50 42 51 49 0\n61 -4 0 60 35 0\n62 -10 0 60 37 0\n63 -3 -24 0 5 8 11 22 25 28 33 34 41 0\n64 32 0 58 56 62 61 52 51 54 49 47 48 44 45 63 40 18 19 36 38 13 15 42 0\n65 26 0 64 50 0\n66 -18 0 65 16 17 43 0\n67 -3 0 65 1 2 43 0\n68 -23 0 67 66 61 62 40 0\n69 -27 0 68 44 0\n70 28 0 69 57 46 0\n71 24 0 70 45 0\n72 -5 0 65 3 4 43 0\n73 -6 0 65 6 7 43 0\n74 -8 0 65 9 10 43 0\n75 19 20 21 0 74 73 72 71 34 33 41 0\n76 -19 0 65 20 21 43 0\n77 -20 0 65 23 24 43 0\n78 21 0 77 76 75 0\n79 -1 0 78 26 0\n80 -2 0 78 27 0\n81 0 80 79 65 43 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00022.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00022.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1b86d1ac3b19c3713c2f34a3a8da4e8bad1b2639b16359362d94e3392e2b86e4789e1783e3a4d94e4b9b172539715355352d4cd4b4ad1b51d2745d0f72338f1334d332cf0b92ccb4acab1ad1b26c5b0ef0731e2749ca719e1745c9715c3743c8f13c2f07d2a46b0691926458c92a499914c52949590c4b0ac1b81c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db6d349a69b69b4db49a4d34d269b4db6db6d249249249249249b491249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 36), (facetIndex 82), (facetIndex 84), (facetIndex 86), (facetIndex 87)]))
 (.leaf ([(facetIndex 23), (facetIndex 37), (facetIndex 38), (facetIndex 41), (facetIndex 44), (facetIndex 45)])))
 (.branch 3
 (.leaf ([(facetIndex 35), (facetIndex 60), (facetIndex 61), (facetIndex 63), (facetIndex 65), (facetIndex 67)]))
 (.leaf ([(facetIndex 43), (facetIndex 78), (facetIndex 89)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 39), (facetIndex 42), (facetIndex 68), (facetIndex 70), (facetIndex 71)]))
 (.leaf ([(facetIndex 29), (facetIndex 33), (facetIndex 40)])))
 (.branch 7
 (.leaf ([(facetIndex 26), (facetIndex 27), (facetIndex 28), (facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 34)]))
 (.leaf ([(facetIndex 21), (facetIndex 22), (facetIndex 55), (facetIndex 58), (facetIndex 75)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "180000000c0e009044104121c0e0000000970d8485aedaed803f8000000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

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

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00022.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00022.record009" 34

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00022.record009" "{\"ridges\":[[18,772],[36,772],[46,777],[50,785],[52,801],[64,785],[66,801],[84,772],[86,772],[87,772],[89,280],[92,840]],\"owners\":[[18,772,[64,66],[36,84,86,87]],[36,772,[],[18,64,66,84,86,87]],[84,772,[66],[18,36,64,86,87]],[86,772,[64],[18,36,66,84,87]],[87,772,[64,66],[18,36,84,86]],[89,280,[56,96],[19,40,69,75,94,100]],[46,777,[],[]],[50,785,[64],[]],[64,785,[50],[]],[52,801,[66],[]],[66,801,[52],[]],[92,840,[],[]]],\"edges\":[[44,[18,36,46,50,52,64,66,84,86,87,92]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00022.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00022.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-2],[-11,-3],[-15,-4],[-15,-5],[-15,-7],[-15,-8],[-15,-13],[-16,-4],[-16,-5],[-16,-7],[-16,-8],[-16,-13],[-17,-10],[-18,-3],[-18,-11],[-18,-12],[-18,-14],[-22,-17],[-24,-2],[-24,-3],[-24,-12],[-24,-14],[-1,15,16],[-6],[-19,16],[-20,15],[-21,15,16],[-22,13,24],[-9],[-10,15],[-15,10],[-11,16],[-16,11],[-23],[-25,8,18,22],[-26,4,5,7],[-27,2,3,12,14,17],[-28,25],[-29,28],[-30,26],[-31,27],[-32,30,31],[-33,30],[-34,29,33],[-34,32],[34],[1,6,9,10,11,15,16,19,20,21,23]],\"atoms\":[{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":50,\"b\":21},{\"tag\":\"incompatible\",\"a\":52,\"b\":22},{\"tag\":\"incompatible\",\"a\":64,\"b\":29},{\"tag\":\"incompatible\",\"a\":64,\"b\":33},{\"tag\":\"incompatible\",\"a\":64,\"b\":40},{\"tag\":\"incompatible\",\"a\":64,\"b\":43},{\"tag\":\"incompatible\",\"a\":64,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":29},{\"tag\":\"incompatible\",\"a\":66,\"b\":33},{\"tag\":\"incompatible\",\"a\":66,\"b\":40},{\"tag\":\"incompatible\",\"a\":66,\"b\":43},{\"tag\":\"incompatible\",\"a\":66,\"b\":56},{\"tag\":\"incompatible\",\"a\":75,\"b\":50},{\"tag\":\"incompatible\",\"a\":78,\"b\":22},{\"tag\":\"incompatible\",\"a\":78,\"b\":52},{\"tag\":\"incompatible\",\"a\":78,\"b\":55},{\"tag\":\"incompatible\",\"a\":78,\"b\":58},{\"tag\":\"incompatible\",\"a\":89,\"b\":75},{\"tag\":\"incompatible\",\"a\":96,\"b\":21},{\"tag\":\"incompatible\",\"a\":96,\"b\":22},{\"tag\":\"incompatible\",\"a\":96,\"b\":55},{\"tag\":\"incompatible\",\"a\":96,\"b\":58},{\"tag\":\"mate\",\"ridge\":772,\"a\":18,\"owners\":[64,66]},{\"tag\":\"mate\",\"ridge\":772,\"a\":36,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":772,\"a\":84,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":772,\"a\":86,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":772,\"a\":87,\"owners\":[64,66]},{\"tag\":\"mate\",\"ridge\":280,\"a\":89,\"owners\":[56,96]},{\"tag\":\"mate\",\"ridge\":777,\"a\":46,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":785,\"a\":50,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":785,\"a\":64,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":801,\"a\":52,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":801,\"a\":66,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":840,\"a\":92,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[43,78,89],\"full_literals\":[-25,8,18,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[29,33,40],\"full_literals\":[-26,4,5,7]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[21,22,55,58,75],\"full_literals\":[-27,2,3,12,14,17]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-28,false,25],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-29,false,28],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-30,false,26],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-31,false,27],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-32,30,31],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-33,30,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-34,29,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-34,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":44,\"owners\":[18,36,46,50,52,64,66,84,86,87,92]}]}"
  "p cnf 34 47\n-10 -2 0\n-11 -3 0\n-15 -4 0\n-15 -5 0\n-15 -7 0\n-15 -8 0\n-15 -13 0\n-16 -4 0\n-16 -5 0\n-16 -7 0\n-16 -8 0\n-16 -13 0\n-17 -10 0\n-18 -3 0\n-18 -11 0\n-18 -12 0\n-18 -14 0\n-22 -17 0\n-24 -2 0\n-24 -3 0\n-24 -12 0\n-24 -14 0\n-1 15 16 0\n-6 0\n-19 16 0\n-20 15 0\n-21 15 16 0\n-22 13 24 0\n-9 0\n-10 15 0\n-15 10 0\n-11 16 0\n-16 11 0\n-23 0\n-25 8 18 22 0\n-26 4 5 7 0\n-27 2 3 12 14 17 0\n-28 25 0\n-29 28 0\n-30 26 0\n-31 27 0\n-32 30 31 0\n-33 30 0\n-34 29 33 0\n-34 32 0\n34 0\n1 6 9 10 11 15 16 19 20 21 23 0\n"
  "48 32 0 46 45 0\n49 1 10 11 15 16 19 20 21 0 24 29 34 47 0\n50 15 16 0 32 25 26 27 30 23 49 0\n51 -16 0 48 46 8 9 10 11 12 33 36 2 15 40 42 43 41 44 39 38 35 18 28 19 21 22 37 0\n52 15 0 51 50 0\n53 -4 0 52 3 0\n54 -5 0 52 4 0\n55 -7 0 52 5 0\n56 -8 0 52 6 0\n57 -13 0 52 7 0\n58 10 0 52 31 0\n59 -26 0 55 53 54 36 0\n60 -2 0 58 1 0\n61 -17 0 58 13 0\n62 -30 0 59 40 0\n63 31 0 62 48 42 0\n64 -33 0 62 43 0\n65 27 0 63 41 0\n66 29 0 64 46 44 0\n67 28 0 66 39 0\n68 25 0 67 38 0\n69 -24 0 61 65 60 20 21 22 37 0\n70 -22 0 69 57 28 0\n71 18 0 70 68 56 35 0\n72 -3 0 71 14 0\n73 -12 0 71 16 0\n74 -14 0 71 17 0\n75 0 74 73 60 72 65 61 37 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00022.record009
