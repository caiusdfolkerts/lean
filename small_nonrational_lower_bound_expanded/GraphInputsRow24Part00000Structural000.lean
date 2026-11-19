module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00000Frames
public import GraphInputsRow24Part00000Leaves
public import GraphInputsRow24Part00000Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record025
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e93949b15cf0b929a8bae1b46a9a66c5a96659562da4e8b86e1783ef07a1564b9e1745c96a569665655552d54d1b51d1743de0f43b0dc3a8e6364d532ccab1ac9b16c3bc1e8761e4751e2729c6745c9715c37d12a291a261382e07991515151342d074a324c4b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6926db69249b6da6db49a4926db4d349249b692492489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 24), (facetIndex 25), (facetIndex 41), (facetIndex 55)]))
 (.leaf ([(facetIndex 27), (facetIndex 28), (facetIndex 43), (facetIndex 77)])))
 (.branch 3
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 38)]))
 (.leaf ([(facetIndex 22), (facetIndex 39), (facetIndex 48), (facetIndex 66)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 26), (facetIndex 51), (facetIndex 68), (facetIndex 76)]))
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 60), (facetIndex 78)])))
 (.branch 7
 (.leaf ([(facetIndex 23), (facetIndex 49), (facetIndex 50), (facetIndex 52), (facetIndex 54)]))
 (.leaf ([(facetIndex 67), (facetIndex 69), (facetIndex 70)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "14c0001fcec00050001869b3000200692480169300ccz10;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record025" "{\"atoms\":[{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record025" 41

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record025" "{\"ridges\":[[55,276],[55,400],[60,832],[77,548],[77,672],[78,832]],\"owners\":[[55,276,[72,75,84],[12,25,50,54,73,86]],[55,400,[82],[14,41,73,86]],[77,548,[56,59,85],[18,28,58,69,76,87]],[77,672,[64],[20,43,58,87]],[60,832,[83],[21,46,65,78]],[78,832,[65],[21,46,60,83]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record025" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record025\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-4,-2],[-6,-1],[-6,-3],[-7,-5],[-8,-6],[-9,-7],[-10,-6],[-11,-2],[-12,-6],[-13,-6],[-17,-5],[-17,-9],[-18,-7],[-18,-17],[-19,-5],[-19,-9],[-19,-16],[-20,-7],[-21,-4],[-22,-7],[-23,-17],[-26,-3],[-26,-8],[-26,-15],[-27,-6],[-27,-26],[-28,-3],[-28,-8],[-28,-24],[-29,-17],[-30,-26],[-14,23,24,29],[-14,27],[-25,15,16,30],[-25,18],[-17,28],[-26,19],[-31,2,3,8,14],[-32,4,5,9,25],[-33,6,7,17,26],[-34,1,10,11,12,13],[-35,20,21,22],[-36,31],[-36,32],[-37,36],[-38,33],[-39,34],[-39,35],[-40,38],[-40,39],[-41,37],[-41,40],[41]],\"atoms\":[{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":27,\"b\":24},{\"tag\":\"incompatible\",\"a\":29,\"b\":23},{\"tag\":\"incompatible\",\"a\":29,\"b\":25},{\"tag\":\"incompatible\",\"a\":30,\"b\":28},{\"tag\":\"incompatible\",\"a\":41,\"b\":29},{\"tag\":\"incompatible\",\"a\":43,\"b\":30},{\"tag\":\"incompatible\",\"a\":49,\"b\":29},{\"tag\":\"incompatible\",\"a\":50,\"b\":24},{\"tag\":\"incompatible\",\"a\":52,\"b\":29},{\"tag\":\"incompatible\",\"a\":54,\"b\":29},{\"tag\":\"incompatible\",\"a\":60,\"b\":28},{\"tag\":\"incompatible\",\"a\":60,\"b\":43},{\"tag\":\"incompatible\",\"a\":64,\"b\":30},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":65,\"b\":28},{\"tag\":\"incompatible\",\"a\":65,\"b\":43},{\"tag\":\"incompatible\",\"a\":65,\"b\":59},{\"tag\":\"incompatible\",\"a\":67,\"b\":30},{\"tag\":\"incompatible\",\"a\":69,\"b\":27},{\"tag\":\"incompatible\",\"a\":70,\"b\":30},{\"tag\":\"incompatible\",\"a\":72,\"b\":60},{\"tag\":\"incompatible\",\"a\":78,\"b\":25},{\"tag\":\"incompatible\",\"a\":78,\"b\":41},{\"tag\":\"incompatible\",\"a\":78,\"b\":56},{\"tag\":\"incompatible\",\"a\":82,\"b\":29},{\"tag\":\"incompatible\",\"a\":82,\"b\":78},{\"tag\":\"incompatible\",\"a\":83,\"b\":25},{\"tag\":\"incompatible\",\"a\":83,\"b\":41},{\"tag\":\"incompatible\",\"a\":83,\"b\":75},{\"tag\":\"incompatible\",\"a\":84,\"b\":60},{\"tag\":\"incompatible\",\"a\":85,\"b\":78},{\"tag\":\"mate\",\"ridge\":276,\"a\":55,\"owners\":[72,75,84]},{\"tag\":\"mate\",\"ridge\":400,\"a\":55,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":548,\"a\":77,\"owners\":[56,59,85]},{\"tag\":\"mate\",\"ridge\":672,\"a\":77,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":832,\"a\":60,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":832,\"a\":78,\"owners\":[65]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[24,25,41,55],\"full_literals\":[-31,2,3,8,14]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[27,28,43,77],\"full_literals\":[-32,4,5,9,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[29,30,60,78],\"full_literals\":[-33,6,7,17,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[23,49,50,52,54],\"full_literals\":[-34,1,10,11,12,13]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[67,69,70],\"full_literals\":[-35,20,21,22]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-36,31,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-36,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-37,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-39,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-40,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-41,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-41,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "54 37 0 53 51 0\n55 40 0 53 52 0\n56 36 0 54 45 0\n57 38 0 55 49 0\n58 39 0 55 50 0\n59 31 0 56 43 0\n60 32 0 56 44 0\n61 33 0 57 46 0\n62 34 0 58 47 0\n63 35 0 58 48 0\n64 -17 0 60 59 11 12 14 21 30 36 35 27 28 29 39 32 1 38 0\n65 -7 0 63 60 4 6 13 18 20 35 42 39 19 0\n66 -6 0 62 59 2 3 5 7 9 10 25 41 33 8 38 0\n67 26 0 66 61 64 65 40 0\n68 -3 0 67 22 0\n69 -8 0 67 23 0\n70 -15 0 67 24 0\n71 -27 0 67 26 0\n72 -30 0 67 31 0\n73 19 0 67 37 0\n74 -14 0 71 33 0\n75 -5 0 73 15 0\n76 -9 0 73 16 0\n77 -16 0 73 17 0\n78 2 0 74 59 68 69 38 0\n79 -25 0 77 70 72 34 0\n80 -4 0 78 1 0\n81 0 79 80 60 76 75 39 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record025

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record029
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e9354ab3c2d4aaae1b46a9a66c5a5655a8e8b8ae1783ef07a166785d1725a95a59958d2b51d1743de0f43b0dc3a8e6364d5326c5b0ef07a1d8791d4789ca719d170dc8f13f44552a22aa46898560b81e544a9515151542d074a314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "69b69a49a4d249b6d36db4926db4da4936d2492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 59)]))
 (.branch 2
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 52), (facetIndex 54), (facetIndex 66)]))
 (.leaf ([(facetIndex 36), (facetIndex 44), (facetIndex 69), (facetIndex 73)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 46), (facetIndex 75), (facetIndex 76)]))
 (.leaf ([(facetIndex 55), (facetIndex 77), (facetIndex 79)])))
 (.branch 6
 (.leaf ([(facetIndex 42), (facetIndex 45), (facetIndex 47), (facetIndex 56), (facetIndex 58)]))
 (.leaf ([(facetIndex 53), (facetIndex 60), (facetIndex 61)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "823610010040036145871000aea14000224z19;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [3, 4, 5, 6]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record029" "{\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record029" 49

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record029" "{\"ridges\":[[20,578],[22,672],[24,832],[33,578],[34,385],[35,645],[41,402],[42,609],[43,672],[44,450],[45,705],[47,385],[47,896],[52,396],[53,609],[54,420],[57,832],[58,385],[58,896],[59,408],[60,385],[60,801],[61,385],[61,705],[66,652],[68,578],[70,578],[71,672],[72,832],[73,896],[74,672],[76,450],[76,896],[78,832],[79,420]],\"owners\":[[20,578,[42,45,46,75,76],[33,68,70,72]],[33,578,[75,76],[20,42,45,46,68,70,72]],[68,578,[42,45,46,76],[20,33,70,72,75]],[70,578,[45,46,75,76],[20,33,42,68,72]],[22,672,[55,60,77,79],[43,71,74]],[43,672,[77,79],[22,55,60,71,74]],[71,672,[60],[22,43,55,74,77,79]],[74,672,[55,60,79],[22,43,71,77]],[24,832,[46,61,75,76],[57,72,78]],[57,832,[75,76],[24,46,61,72,78]],[72,832,[61],[24,46,57,75,76,78]],[78,832,[46,61,76],[24,57,72,75]],[34,385,[59,60,61],[41,44,47,52,54,58]],[47,385,[52,54,59],[34,41,44,58,60,61]],[58,385,[41,44,59],[34,47,52,54,60,61]],[60,385,[34,41,44,52,59],[47,54,58,61]],[61,385,[34,41,52,54,59],[44,47,58,60]],[35,645,[55,58],[]],[41,402,[],[]],[42,609,[53],[]],[53,609,[42],[]],[44,450,[76],[]],[76,450,[44],[]],[45,705,[61],[]],[61,705,[45],[]],[47,896,[79],[58,60,61,73,76]],[58,896,[76],[47,60,61,73,79]],[73,896,[60,61],[47,58,76,79]],[76,896,[58,60,79],[47,61,73]],[52,396,[],[]],[54,420,[79],[]],[79,420,[54],[]],[60,801,[56],[]],[59,408,[],[]],[66,652,[77],[]]],\"edges\":[[41,[20,24,33,42,45,46,53,57,61,68,70,72,75,76,78]],[42,[34,41,44,47,52,54,58,59,60,61,73,76,79]],[43,[22,35,43,45,47,55,58,60,61,66,71,73,74,76,77,79]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record029" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record029\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,8,11,12,31,32],[-4,31,32],[-25,8,11,12,32],[-26,11,12,31,32],[-2,17,22,33,35],[-9,33,35],[-27,22],[-30,17,22,35],[-3,12,23,31,32],[-19,31,32],[-28,23],[-34,12,23,32],[-5,21,22,23],[-13,14,16,21],[-20,7,10,21],[-22,5,7,10,14,21],[-23,5,7,14,16,21],[-6,17,20],[-7],[-8,15],[-15,8],[-10,32],[-32,10],[-11,23],[-23,11],[-13,35],[-20,32],[-29,22,23],[-32,20,22,35],[-14],[-16,35],[-35,16],[-22,18],[-21],[-24,33],[-5,36],[-16,36],[-10,37],[-29,37],[-12,38],[-31,38],[-32,38],[-17,39],[-33,39],[-35,39],[-8,40],[-11,40],[-13,40],[-18,40],[-20,40],[-41,15,22,23],[-15,41],[-22,41],[-23,41],[-37,42],[-36,42],[-42,43],[-39,44],[-38,44],[-38,-39,45],[-40,46],[-40,-41,47],[-47,48],[-44,-46,48],[-45,48],[-43,-48,49],[-49],[1,3,4,8,11,12,15,19,23,25,26,28,31,32,34],[5,7,10,13,14,16,20,21,22,23,29,32,35],[2,6,9,11,13,17,20,22,23,24,27,29,30,32,33,35]],\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":578,\"a\":20,\"owners\":[42,45,46,75,76]},{\"tag\":\"mate\",\"ridge\":578,\"a\":33,\"owners\":[75,76]},{\"tag\":\"mate\",\"ridge\":578,\"a\":68,\"owners\":[42,45,46,76]},{\"tag\":\"mate\",\"ridge\":578,\"a\":70,\"owners\":[45,46,75,76]},{\"tag\":\"mate\",\"ridge\":672,\"a\":22,\"owners\":[55,60,77,79]},{\"tag\":\"mate\",\"ridge\":672,\"a\":43,\"owners\":[77,79]},{\"tag\":\"mate\",\"ridge\":672,\"a\":71,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":672,\"a\":74,\"owners\":[55,60,79]},{\"tag\":\"mate\",\"ridge\":832,\"a\":24,\"owners\":[46,61,75,76]},{\"tag\":\"mate\",\"ridge\":832,\"a\":57,\"owners\":[75,76]},{\"tag\":\"mate\",\"ridge\":832,\"a\":72,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":832,\"a\":78,\"owners\":[46,61,76]},{\"tag\":\"mate\",\"ridge\":385,\"a\":34,\"owners\":[59,60,61]},{\"tag\":\"mate\",\"ridge\":385,\"a\":47,\"owners\":[52,54,59]},{\"tag\":\"mate\",\"ridge\":385,\"a\":58,\"owners\":[41,44,59]},{\"tag\":\"mate\",\"ridge\":385,\"a\":60,\"owners\":[34,41,44,52,59]},{\"tag\":\"mate\",\"ridge\":385,\"a\":61,\"owners\":[34,41,52,54,59]},{\"tag\":\"mate\",\"ridge\":645,\"a\":35,\"owners\":[55,58]},{\"tag\":\"mate\",\"ridge\":402,\"a\":41,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":609,\"a\":42,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":609,\"a\":53,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":450,\"a\":44,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":450,\"a\":76,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":705,\"a\":45,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":705,\"a\":61,\"owners\":[45]},{\"tag\":\"mate\",\"ridge\":896,\"a\":47,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":896,\"a\":58,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":896,\"a\":73,\"owners\":[60,61]},{\"tag\":\"mate\",\"ridge\":896,\"a\":76,\"owners\":[58,60,79]},{\"tag\":\"mate\",\"ridge\":396,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":420,\"a\":54,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":420,\"a\":79,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":801,\"a\":60,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":408,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":652,\"a\":66,\"owners\":[77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":34,\"full_literals\":[-5,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":54,\"full_literals\":[-16,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":44,\"full_literals\":[-10,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":73,\"full_literals\":[-29,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":46,\"full_literals\":[-12,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":75,\"full_literals\":[-31,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-32,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":55,\"full_literals\":[-17,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":77,\"full_literals\":[-33,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":79,\"full_literals\":[-35,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":42,\"full_literals\":[-8,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":45,\"full_literals\":[-11,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":47,\"full_literals\":[-13,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":56,\"full_literals\":[-18,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":58,\"full_literals\":[-20,40]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[53,60,61],\"full_literals\":[-41,15,22,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":53,\"full_literals\":[-15,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":60,\"full_literals\":[-22,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":61,\"full_literals\":[-23,41]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-38,-39,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-41,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-46,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-43,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[20,24,33,42,45,46,53,57,61,68,70,72,75,76,78]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[34,41,44,47,52,54,58,59,60,61,73,76,79]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[22,35,43,45,47,55,58,60,61,66,71,73,74,76,77,79]}]}"
  "71 5 10 13 16 20 22 23 29 32 35 0 19 30 34 69 0\n72 42 0 34 30 19 55 56 38 39 36 37 15 23 16 14 32 17 71 0\n73 43 0 72 57 0\n74 -48 0 73 67 66 0\n75 -47 0 74 63 0\n76 -45 0 74 65 0\n77 -41 0 75 62 46 47 49 21 25 33 51 0\n78 -15 0 77 52 0\n79 -22 0 77 53 0\n80 -23 0 77 54 0\n81 -8 0 78 20 0\n82 -27 0 79 7 0\n83 -29 0 79 80 28 0\n84 -5 0 79 34 80 13 0\n85 -28 0 80 11 0\n86 -11 0 80 24 0\n87 44 0 80 83 79 84 58 59 45 42 26 31 22 27 71 0\n88 -46 0 87 74 64 0\n89 -40 0 88 61 0\n90 -13 0 89 48 0\n91 -20 0 89 50 0\n92 39 0 83 82 86 80 79 91 90 43 44 45 8 18 6 35 5 29 70 0\n93 -38 0 92 76 60 0\n94 -12 0 93 40 0\n95 -31 0 93 41 0\n96 -32 0 93 42 0\n97 -34 0 94 80 96 12 0\n98 -26 0 94 86 95 96 4 0\n99 -1 0 94 81 86 95 96 1 0\n100 -25 0 94 81 86 96 3 0\n101 -4 0 95 96 2 0\n102 -19 0 95 96 10 0\n103 -3 0 95 94 80 96 9 0\n104 0 103 97 101 81 99 94 78 102 80 100 98 85 95 96 86 68 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record029

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record030
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "d52acf0ba266b46a9a66558ae1783ef07a1d46a966745a9665c56555568d8b4ad1743de0f43b0dc3c8ea368e6364d8b46c9b16c3bc1e8791d4789ca719d170dc8f13d522a8560b81ee0741a85512a645894550b41d60d4328d1314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db49249269269349249a69349249b492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 64), (facetIndex 66)]))
 (.leaf ([(facetIndex 28), (facetIndex 38), (facetIndex 68), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 39), (facetIndex 69), (facetIndex 71)]))
 (.leaf ([(facetIndex 31), (facetIndex 35), (facetIndex 58), (facetIndex 60)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 34), (facetIndex 50), (facetIndex 57), (facetIndex 62), (facetIndex 65)]))
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 43)])))
 (.branch 7
 (.leaf ([(facetIndex 27), (facetIndex 29), (facetIndex 52), (facetIndex 53)]))
 (.branch 8
 (.leaf ([(facetIndex 48), (facetIndex 51), (facetIndex 67)]))
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 54), (facetIndex 55), (facetIndex 61)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "212170400483034088667407000055552100348832616z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 63)]))
 (.leaf ([(facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 56)]))
 (.leaf ([(facetIndex 37), (facetIndex 59)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 73), (facetIndex 78)]))
 (.leaf ([(facetIndex 74), (facetIndex 79)])))
 (.branch 7
 (.leaf ([(facetIndex 44), (facetIndex 47), (facetIndex 49)]))
 (.leaf ([(facetIndex 72), (facetIndex 76), (facetIndex 77)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "b3f367000000000602000030c0600001az1b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
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
def grouped3_0025 : List Nat := [4, 5, 6, 7]
def grouped3_0026 : List Nat := [5]
def grouped3_0027 : List Nat := [6]
def grouped3_0028 : List Nat := [6, 7]
def grouped3_0029 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record030" "{\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record030" 66

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record030" "{\"ridges\":[[15,517],[20,832],[21,896],[33,548],[36,517],[45,386],[46,672],[47,802],[48,386],[51,896],[55,548],[56,517],[59,517],[61,548],[62,580],[64,545],[64,672],[65,832],[66,672],[66,896],[67,832],[67,896],[73,646],[74,774],[76,802],[77,706],[78,548],[78,652],[79,788]],\"owners\":[[45,386,[75,77],[11,42,43,48,51,76]],[48,386,[75,76],[11,42,43,45,51,77]],[64,545,[15,33,44,47,60],[19,46,55,66]],[33,548,[78],[15,55,60,61,72,73]],[55,548,[72,73],[15,33,60,61,78]],[61,548,[72],[15,33,55,60,73,78]],[78,548,[15,33,60,72],[55,61,73]],[62,580,[72],[16,35,58,60,74,79]],[46,672,[78],[19,61,64,66,73,76]],[64,672,[73,76],[19,46,61,66,78]],[66,672,[73,78],[19,46,61,64,76]],[20,832,[74,77,79],[50,62,65,67]],[65,832,[74,77],[20,50,62,67,79]],[67,832,[74,79],[20,50,62,65,77]],[21,896,[76,77],[51,66,67]],[51,896,[],[21,66,67,76,77]],[66,896,[77],[21,51,67,76]],[67,896,[76],[21,51,66,77]],[73,646,[36],[]],[74,774,[37],[]],[47,802,[76],[]],[76,802,[47],[]],[77,706,[49],[]],[78,652,[56],[]],[79,788,[59],[]]],\"edges\":[[44,[20,21,37,47,50,51,59,62,65,66,67,74,76,77,79]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record030" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record030\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-8],[-13,-10],[-13,-11],[-14,-5],[-14,-7],[-15,-4],[-16,-9],[-16,-10],[-16,-11],[-16,-13],[-16,-15],[-17,-13],[-18,-14],[-24,-6],[-24,-22],[-27,-20],[-29,-17],[-31,-14],[-32,-7],[-32,-12],[-32,-18],[-32,-31],[-33,-14],[-33,-32],[-34,-8],[-34,-9],[-35,-13],[-35,-31],[-36,-14],[-36,-32],[-37,-27],[-13,34,36],[-16,34,35],[-1,-6,-23],[-1,-22,-23],[-27,1,5,12,15,24],[-5,37],[-21,31,32],[-25,31],[-37,1,5,24,31],[-26,31],[-14,37],[-27,32,35],[-29,32,37],[-2,33,36,38],[-28,33,36],[-30,33,38],[-3,35,36],[-19],[-29,36],[-30,35],[-32,6],[-33,7],[-15,35],[-35,15],[-36,17],[-37,22],[-38,23],[-39,13,14,27,29],[-40,8,9,10,11],[-41,16,19,30],[-42,4,5,20,21,25],[-43,39],[-44,43],[-45,40],[-46,41,42],[-47,41],[-48,46],[-49,47],[-50,45,49],[-51,45],[-50,48],[-51,49],[-52,44,51],[-52,50],[52],[-34,53],[-6,54],[-22,54],[-7,55],[-23,55],[-32,56],[-37,56],[-38,57],[-15,58],[-35,59],[-53,60],[-55,61],[-54,61],[-61,62],[-60,62],[-56,-57,63],[-58,-59,64],[-64,65],[-63,65],[-62,-65,66],[-66],[2,3,7,15,18,19,23,26,28,29,30,33,35,36,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":45,\"b\":40},{\"tag\":\"incompatible\",\"a\":45,\"b\":42},{\"tag\":\"incompatible\",\"a\":45,\"b\":43},{\"tag\":\"incompatible\",\"a\":46,\"b\":33},{\"tag\":\"incompatible\",\"a\":46,\"b\":37},{\"tag\":\"incompatible\",\"a\":47,\"b\":32},{\"tag\":\"incompatible\",\"a\":48,\"b\":41},{\"tag\":\"incompatible\",\"a\":48,\"b\":42},{\"tag\":\"incompatible\",\"a\":48,\"b\":43},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":60,\"b\":36},{\"tag\":\"incompatible\",\"a\":60,\"b\":56},{\"tag\":\"incompatible\",\"a\":64,\"b\":54},{\"tag\":\"incompatible\",\"a\":66,\"b\":49},{\"tag\":\"incompatible\",\"a\":72,\"b\":46},{\"tag\":\"incompatible\",\"a\":73,\"b\":37},{\"tag\":\"incompatible\",\"a\":73,\"b\":44},{\"tag\":\"incompatible\",\"a\":73,\"b\":50},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":46},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":40},{\"tag\":\"incompatible\",\"a\":75,\"b\":41},{\"tag\":\"incompatible\",\"a\":76,\"b\":45},{\"tag\":\"incompatible\",\"a\":76,\"b\":72},{\"tag\":\"incompatible\",\"a\":77,\"b\":46},{\"tag\":\"incompatible\",\"a\":77,\"b\":73},{\"tag\":\"incompatible\",\"a\":78,\"b\":64},{\"tag\":\"mate\",\"ridge\":386,\"a\":45,\"owners\":[75,77]},{\"tag\":\"mate\",\"ridge\":386,\"a\":48,\"owners\":[75,76]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[15,36,59]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[15,56,59]},{\"tag\":\"mate\",\"ridge\":545,\"a\":64,\"owners\":[15,33,44,47,60]},{\"tag\":\"mate\",\"ridge\":548,\"a\":33,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":548,\"a\":55,\"owners\":[72,73]},{\"tag\":\"mate\",\"ridge\":548,\"a\":61,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":548,\"a\":78,\"owners\":[15,33,60,72]},{\"tag\":\"mate\",\"ridge\":580,\"a\":62,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":672,\"a\":46,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":672,\"a\":64,\"owners\":[73,76]},{\"tag\":\"mate\",\"ridge\":672,\"a\":66,\"owners\":[73,78]},{\"tag\":\"mate\",\"ridge\":832,\"a\":20,\"owners\":[74,77,79]},{\"tag\":\"mate\",\"ridge\":832,\"a\":65,\"owners\":[74,77]},{\"tag\":\"mate\",\"ridge\":832,\"a\":67,\"owners\":[74,79]},{\"tag\":\"mate\",\"ridge\":896,\"a\":21,\"owners\":[76,77]},{\"tag\":\"mate\",\"ridge\":896,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":896,\"a\":66,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":896,\"a\":67,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":646,\"a\":73,\"owners\":[36]},{\"tag\":\"mate\",\"ridge\":774,\"a\":74,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":802,\"a\":47,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":802,\"a\":76,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":706,\"a\":77,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":652,\"a\":78,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":788,\"a\":79,\"owners\":[59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[45,46,64,66],\"full_literals\":[-39,13,14,27,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[40,41,42,43],\"full_literals\":[-40,8,9,10,11]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[48,51,67],\"full_literals\":[-41,16,19,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[32,33,54,55,61],\"full_literals\":[-42,4,5,20,21,25]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-44,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,41,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-50,45,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-51,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-51,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-52,44,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-52,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":75,\"full_literals\":[-34,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":36,\"full_literals\":[-6,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":56,\"full_literals\":[-22,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":37,\"full_literals\":[-7,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":59,\"full_literals\":[-23,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":73,\"full_literals\":[-32,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":78,\"full_literals\":[-37,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-38,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":47,\"full_literals\":[-15,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":76,\"full_literals\":[-35,59]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-57,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-59,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-62,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":44,\"owners\":[20,21,37,47,50,51,59,62,65,66,67,74,76,77,79]}]}"
  "99 -41 16 30 0 49 61 0\n100 50 0 76 75 0\n101 48 0 100 72 0\n102 46 0 101 68 0\n103 2 3 7 15 18 23 26 28 29 30 33 35 36 38 0 49 98 0\n104 -16 34 0 11 33 55 0\n105 -35 62 0 102 76 90 88 80 53 81 58 47 91 87 77 104 99 67 69 73 74 64 63 66 89 78 52 79 57 44 42 37 27 28 55 59 38 39 6 16 62 0\n106 62 0 76 90 91 88 89 87 80 81 78 79 77 53 58 52 57 47 42 44 104 99 67 69 73 74 64 63 105 43 59 12 32 56 0\n107 -65 0 106 97 96 0\n108 -64 0 107 94 0\n109 -63 0 107 95 0\n110 -13 30 0 100 1 2 3 10 12 99 56 67 32 69 26 70 60 65 0\n111 -29 0 17 50 56 0\n112 -14 35 0 109 111 54 51 4 5 13 18 23 29 42 41 46 48 57 83 15 92 40 84 35 45 103 0\n113 -27 35 0 109 111 54 51 31 43 37 19 20 21 22 24 30 52 82 41 46 48 14 92 36 84 34 45 103 0\n114 35 0 111 76 51 110 112 113 59 63 64 74 71 73 65 69 67 99 7 8 9 33 60 25 0\n115 15 0 114 55 0\n116 59 0 114 86 0\n117 58 0 115 85 0\n118 0 117 116 108 93 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00000.record030
