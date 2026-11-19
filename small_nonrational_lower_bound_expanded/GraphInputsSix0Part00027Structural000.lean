module
prelude
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsSix0Part00027Frames
public import GraphInputsSix0Part00027Leaves
public import GraphInputsSix0Part00027Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00027.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ea72bb55ad5ad2f3acdd33cbd1ec3fec370ea398e538cab26cc729c67362d4b326ca725cb2a6aa6ac699a99b1665a56c398e93a2e2b86e8791e279b19c4f16a66966665396553564d8b4ad1b61d275a364d332cc7362d2b2ac6b46c9b29c6725c8f13c2f07f286a2544a8562a4951548d18c530ac4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9249249246d36db6db6db6936db69b6db6db6d36da4da6d36da6926da492449249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 17), (facetIndex 20), (facetIndex 24), (facetIndex 28)]))
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 58)])))
 (.branch 3
 (.leaf ([(facetIndex 26), (facetIndex 45), (facetIndex 65), (facetIndex 66), (facetIndex 81)]))
 (.branch 4
 (.leaf ([(facetIndex 15), (facetIndex 18), (facetIndex 19), (facetIndex 33)]))
 (.leaf ([(facetIndex 16), (facetIndex 25), (facetIndex 36)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "100000000000900000400000000100012040180000a00006c4600000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 5
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers4 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 1
 (.leaf ([(facetIndex 89), (facetIndex 93), (facetIndex 94), (facetIndex 95)]))
 (.branch 2
 (.leaf ([(facetIndex 84), (facetIndex 85), (facetIndex 86), (facetIndex 87), (facetIndex 88)]))
 (.leaf ([(facetIndex 90), (facetIndex 91), (facetIndex 92)]))))
def groupColors4 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "2a155z2a;"⟩
def grouping4 : FacetSat.Grouping data.count where
  count := 3
  members := fun g => groupMembers4.get g
  color := fun c => groupColors4.get c.val
def groupKind4 : List Nat := List.range grouping4.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [2]
def grouped2_0005 : List Nat := [2, 3, 4]
def grouped2_0006 : List Nat := [3]
def grouped2_0007 : List Nat := [3, 4]
def grouped2_0008 : List Nat := [4]
def grouped4_0009 : List Nat := [0]
def grouped4_0011 : List Nat := [1]
def grouped4_0012 : List Nat := [1, 2]
def grouped4_0013 : List Nat := [2]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3, 4]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00027.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":4,\"index\":0},{\"tag\":\"group\",\"kind\":4,\"index\":1},{\"tag\":\"group\",\"kind\":4,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":4,\"threshold\":1,\"list_name\":\"grouped4_0012\"},{\"tag\":\"group_totalizer\",\"kind\":4,\"threshold\":1,\"list_name\":\"groupKind4\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00027.record009" 59

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00027.record009" "{\"ridges\":[[4,82],[8,21],[17,70],[20,97],[24,97],[25,161],[34,537],[40,580],[41,228],[46,240],[47,561],[55,586],[58,82],[58,592],[61,608],[64,608],[67,82],[82,368],[87,133],[89,161],[92,161],[93,81],[95,416]],\"owners\":[[8,21,[1,7,15,34,40,84],[33,86]],[17,70,[10,58,61],[2,20,52,55,87]],[93,81,[4,28,85],[7,39,40,46,47,88]],[20,97,[44,46,47],[5,24,28,35,41,42,85,89,91]],[24,97,[41,42,46,47],[5,20,28,35,44,85,89,91]],[87,133,[8],[6,18,19,21,36,39,41,92,93]],[25,161,[41,46,48],[9,21,29,32,36,45,86,89,92,95]],[89,161,[48],[9,21,25,29,32,36,41,45,46,86,92,95]],[92,161,[29,46],[9,21,25,32,36,41,45,48,86,89,95]],[40,580,[55,61,76],[12,38,42,58,93]],[58,592,[47,82],[12,40,68,71,93]],[95,416,[69],[13,32,45,48,65,81,83,92]],[34,537,[],[]],[41,228,[],[]],[61,608,[44,47,82],[42,64,68,72,76]],[64,608,[42,47,82],[44,61,68,72,76]],[46,240,[],[]],[47,561,[],[]],[55,586,[64],[]],[82,368,[67],[]]],\"edges\":[],\"groupings\":[2,4]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00027.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00027.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-8,-7],[-9,-7],[-13,-9],[-18,-9],[-19,-6],[-19,-10],[-19,-16],[-20,-5],[-22,-20],[-23,-20],[-26,-14],[-28,-3],[-28,-20],[-29,-18],[-33,-7],[-33,-18],[-34,-14],[-34,-15],[-34,-26],[-34,-32],[-35,-34],[-36,-34],[-37,-34],[-38,-1],[-38,-6],[-39,-28],[-41,-7],[-41,-18],[-42,-34],[-45,-28],[-4,1,3,6,17,20,35],[-8,5,28,29],[-44,2,14,36],[-2,-28,-31],[-11,23,24,25],[-12,21,22,24,25],[-38,4],[-13,21,24,26],[-40,26],[-43,15,24],[-20,27,29,33],[-28,25,34],[-46,32],[-17],[-21],[-29,23,25,34],[-30,22,25,34],[-24],[-25],[-27,30],[-34,31],[-47,8,11,12,14],[-48,19,20,28],[-49,6,9,10,16],[-50,7,13,18],[-51,47],[-51,48],[-52,49],[-52,50],[-53,52],[-54,51],[-54,53],[54],[-55,40,44,45,46],[-56,35,36,37,38,39],[-57,41,42,43],[-58,56,57],[-59,55,58],[59]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":4},{\"tag\":\"group\",\"index\":1,\"kind\":4},{\"tag\":\"group\",\"index\":2,\"kind\":4},{\"tag\":\"group_totalizer\",\"kind\":4},{\"tag\":\"group_totalizer\",\"kind\":4}],\"rules\":[{\"tag\":\"incompatible\",\"a\":17,\"b\":16},{\"tag\":\"incompatible\",\"a\":18,\"b\":16},{\"tag\":\"incompatible\",\"a\":25,\"b\":18},{\"tag\":\"incompatible\",\"a\":36,\"b\":18},{\"tag\":\"incompatible\",\"a\":39,\"b\":15},{\"tag\":\"incompatible\",\"a\":39,\"b\":19},{\"tag\":\"incompatible\",\"a\":39,\"b\":33},{\"tag\":\"incompatible\",\"a\":40,\"b\":10},{\"tag\":\"incompatible\",\"a\":42,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":40},{\"tag\":\"incompatible\",\"a\":48,\"b\":28},{\"tag\":\"incompatible\",\"a\":58,\"b\":7},{\"tag\":\"incompatible\",\"a\":58,\"b\":40},{\"tag\":\"incompatible\",\"a\":61,\"b\":36},{\"tag\":\"incompatible\",\"a\":76,\"b\":16},{\"tag\":\"incompatible\",\"a\":76,\"b\":36},{\"tag\":\"incompatible\",\"a\":82,\"b\":28},{\"tag\":\"incompatible\",\"a\":82,\"b\":29},{\"tag\":\"incompatible\",\"a\":82,\"b\":48},{\"tag\":\"incompatible\",\"a\":82,\"b\":69},{\"tag\":\"incompatible\",\"a\":84,\"b\":82},{\"tag\":\"incompatible\",\"a\":85,\"b\":82},{\"tag\":\"incompatible\",\"a\":86,\"b\":82},{\"tag\":\"incompatible\",\"a\":87,\"b\":1},{\"tag\":\"incompatible\",\"a\":87,\"b\":15},{\"tag\":\"incompatible\",\"a\":88,\"b\":58},{\"tag\":\"incompatible\",\"a\":90,\"b\":16},{\"tag\":\"incompatible\",\"a\":90,\"b\":36},{\"tag\":\"incompatible\",\"a\":91,\"b\":82},{\"tag\":\"incompatible\",\"a\":94,\"b\":58},{\"tag\":\"mate\",\"ridge\":21,\"a\":8,\"owners\":[1,7,15,34,40,84]},{\"tag\":\"mate\",\"ridge\":70,\"a\":17,\"owners\":[10,58,61]},{\"tag\":\"mate\",\"ridge\":81,\"a\":93,\"owners\":[4,28,85]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[4,58,67]},{\"tag\":\"mate\",\"ridge\":97,\"a\":20,\"owners\":[44,46,47]},{\"tag\":\"mate\",\"ridge\":97,\"a\":24,\"owners\":[41,42,46,47]},{\"tag\":\"mate\",\"ridge\":133,\"a\":87,\"owners\":[8]},{\"tag\":\"mate\",\"ridge\":161,\"a\":25,\"owners\":[41,46,48]},{\"tag\":\"mate\",\"ridge\":161,\"a\":89,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":161,\"a\":92,\"owners\":[29,46]},{\"tag\":\"mate\",\"ridge\":580,\"a\":40,\"owners\":[55,61,76]},{\"tag\":\"mate\",\"ridge\":592,\"a\":58,\"owners\":[47,82]},{\"tag\":\"mate\",\"ridge\":416,\"a\":95,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":537,\"a\":34,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":228,\"a\":41,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":608,\"a\":61,\"owners\":[44,47,82]},{\"tag\":\"mate\",\"ridge\":608,\"a\":64,\"owners\":[42,47,82]},{\"tag\":\"mate\",\"ridge\":240,\"a\":46,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":561,\"a\":47,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":586,\"a\":55,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":368,\"a\":82,\"owners\":[67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[17,20,24,28],\"full_literals\":[-47,8,11,12,14]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[39,40,58],\"full_literals\":[-48,19,20,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[15,18,19,33],\"full_literals\":[-49,6,9,10,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[16,25,36],\"full_literals\":[-50,7,13,18]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0005\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"groupKind2\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-54,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-54,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":5,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":4,\"index\":0,\"members\":[89,93,94,95],\"full_literals\":[-55,40,44,45,46]},{\"tag\":\"group_or\",\"kind\":4,\"index\":1,\"members\":[84,85,86,87,88],\"full_literals\":[-56,35,36,37,38,39]},{\"tag\":\"group_or\",\"kind\":4,\"index\":2,\"members\":[90,91,92],\"full_literals\":[-57,41,42,43]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped4_0011\",\"right_name\":\"grouped4_0013\",\"joined_name\":\"grouped4_0012\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,56,57],\"grouped\":true,\"kind\":4},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped4_0009\",\"right_name\":\"grouped4_0012\",\"joined_name\":\"groupKind4\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,55,58],\"grouped\":true,\"kind\":4},{\"tag\":\"quota_lower\",\"kind\":4,\"quota\":1,\"grouped\":true}]}"
  "70 51 0 63 61 0\n71 53 0 63 62 0\n72 47 0 70 56 0\n73 48 0 70 57 0\n74 52 0 71 60 0\n75 49 0 74 58 0\n76 50 0 74 59 0\n77 -9 0 76 2 3 4 55 0\n78 -19 0 77 75 5 6 7 54 0\n79 34 0 78 73 49 72 76 48 45 42 53 8 9 10 36 47 35 46 50 32 41 52 15 16 11 55 38 0\n80 -14 0 79 17 0\n81 -15 0 79 18 0\n82 -26 0 79 19 0\n83 -32 0 79 20 0\n84 -35 0 79 21 0\n85 -36 0 79 22 0\n86 -37 0 79 23 0\n87 -42 0 79 29 0\n88 31 0 79 51 0\n89 -43 0 81 48 40 0\n90 -13 0 82 45 48 38 0\n91 28 0 78 73 45 49 48 80 72 90 76 53 8 9 10 36 35 52 1 32 55 14 0\n92 -3 0 91 12 0\n93 -20 0 91 13 0\n94 -39 0 91 26 0\n95 -2 0 91 88 34 0\n96 -38 0 84 93 44 92 24 25 37 31 0\n97 -56 0 96 85 86 84 94 65 0\n98 -41 0 90 76 27 28 55 0\n99 -44 0 80 95 85 33 0\n100 -40 0 82 39 0\n101 -46 0 83 43 0\n102 -45 0 91 30 0\n103 -57 0 98 87 89 66 0\n104 -55 0 100 99 102 101 64 0\n105 -58 0 103 97 67 0\n106 0 104 105 69 68 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009 Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00027.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00027.record009
