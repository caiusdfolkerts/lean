module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00111Frames
public import GraphInputsRow24Part00111Leaves
public import GraphInputsRow24Part00111Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2e2749aa96a66399963598e93a2e2b91e1783eb85d16a659994e5654d56364d8b4ad4745d0f6c370ea368e6338d9394d5334f0b62e4b4acab86c5b0ed8791e2719d1725c3783d0f23c4f8a91a318a61582e07a29464c5294550b41d60e4330e2328d1314e0b42c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db4d369249b6da69b492492492492492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 64), (facetIndex 70)]))
 (.leaf ([(facetIndex 65), (facetIndex 71)])))
 (.branch 3
 (.leaf ([(facetIndex 67), (facetIndex 72)]))
 (.leaf ([(facetIndex 69), (facetIndex 73)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 79), (facetIndex 85)]))
 (.leaf ([(facetIndex 80), (facetIndex 86)])))
 (.branch 7
 (.leaf ([(facetIndex 82), (facetIndex 87)]))
 (.leaf ([(facetIndex 84), (facetIndex 88)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "7d6718580001a218408z30;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record003" 43

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record003" "{\"ridges\":[[14,578],[15,385],[15,386],[39,578],[40,385],[40,386],[46,578],[47,385],[47,386],[51,578],[52,385],[52,386],[54,578],[55,385],[55,386],[57,385],[57,386],[58,578],[64,588],[65,396],[67,404],[69,612],[70,600],[71,424],[72,464],[73,736],[80,396],[82,404],[86,424],[87,464]],\"owners\":[[14,578,[79,84,85,88],[39,46,51,54,58]],[39,578,[85,88],[14,46,51,54,58,79,84]],[46,578,[84,88],[14,39,51,54,58,79,85]],[51,578,[79,84,88],[14,39,46,54,58,85]],[54,578,[79,85],[14,39,46,51,58,84,88]],[58,578,[79,84,85],[14,39,46,51,54,88]],[15,385,[65,67,71,72],[40,47,52,55,57]],[40,385,[71,72],[15,47,52,55,57,65,67]],[47,385,[67,72],[15,40,52,55,57,65,71]],[52,385,[65,71],[15,40,47,55,57,67,72]],[55,385,[65,67,72],[15,40,47,52,57,71]],[57,385,[65,67,71],[15,40,47,52,55,72]],[15,386,[80,82,86,87],[40,47,52,55,57]],[40,386,[86,87],[15,47,52,55,57,80,82]],[47,386,[82,87],[15,40,52,55,57,80,86]],[52,386,[80,86],[15,40,47,55,57,82,87]],[55,386,[80,82,87],[15,40,47,52,57,86]],[57,386,[80,82,86],[15,40,47,52,55,87]],[64,588,[79],[]],[65,396,[80],[]],[80,396,[65],[]],[67,404,[82],[]],[82,404,[67],[]],[69,612,[84],[]],[70,600,[85],[]],[71,424,[86],[]],[86,424,[71],[]],[72,464,[87],[]],[87,464,[72],[]],[73,736,[88],[]]],\"edges\":[[41,[14,39,46,51,54,58,64,69,70,73,79,84,85,88]],[42,[15,40,47,52,55,57,65,67,71,72,80,82,86,87]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,21,24,25,28],[-3,25,28],[-5,24,28],[-7,21,24,28],[-9,21,25],[-12,21,24,25],[-2,14,15,18,19],[-4,18,19],[-6,15,19],[-8,14,18],[-10,14,15,19],[-11,14,15,18],[-2,22,23,26,27],[-4,26,27],[-6,23,27],[-8,22,26],[-10,22,23,27],[-11,22,23,26],[-13,21],[-14,22],[-22,14],[-15,23],[-23,15],[-16,24],[-17,25],[-18,26],[-26,18],[-19,27],[-27,19],[-20,28],[-14,29],[-18,29],[-15,30],[-19,30],[-21,31],[-25,31],[-22,32],[-26,32],[-23,33],[-27,33],[-24,34],[-28,34],[-29,35],[-30,36],[-36,37],[-35,37],[-32,38],[-31,38],[-31,-32,39],[-34,40],[-33,40],[-33,-34,41],[-41,42],[-38,-40,42],[-39,42],[-37,-42,43],[-43],[1,3,5,7,9,12,13,16,17,20,21,24,25,28],[2,4,6,8,10,11,14,15,18,19,22,23,26,27]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":578,\"a\":14,\"owners\":[79,84,85,88]},{\"tag\":\"mate\",\"ridge\":578,\"a\":39,\"owners\":[85,88]},{\"tag\":\"mate\",\"ridge\":578,\"a\":46,\"owners\":[84,88]},{\"tag\":\"mate\",\"ridge\":578,\"a\":51,\"owners\":[79,84,88]},{\"tag\":\"mate\",\"ridge\":578,\"a\":54,\"owners\":[79,85]},{\"tag\":\"mate\",\"ridge\":578,\"a\":58,\"owners\":[79,84,85]},{\"tag\":\"mate\",\"ridge\":385,\"a\":15,\"owners\":[65,67,71,72]},{\"tag\":\"mate\",\"ridge\":385,\"a\":40,\"owners\":[71,72]},{\"tag\":\"mate\",\"ridge\":385,\"a\":47,\"owners\":[67,72]},{\"tag\":\"mate\",\"ridge\":385,\"a\":52,\"owners\":[65,71]},{\"tag\":\"mate\",\"ridge\":385,\"a\":55,\"owners\":[65,67,72]},{\"tag\":\"mate\",\"ridge\":385,\"a\":57,\"owners\":[65,67,71]},{\"tag\":\"mate\",\"ridge\":386,\"a\":15,\"owners\":[80,82,86,87]},{\"tag\":\"mate\",\"ridge\":386,\"a\":40,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":386,\"a\":47,\"owners\":[82,87]},{\"tag\":\"mate\",\"ridge\":386,\"a\":52,\"owners\":[80,86]},{\"tag\":\"mate\",\"ridge\":386,\"a\":55,\"owners\":[80,82,87]},{\"tag\":\"mate\",\"ridge\":386,\"a\":57,\"owners\":[80,82,86]},{\"tag\":\"mate\",\"ridge\":588,\"a\":64,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":396,\"a\":65,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":396,\"a\":80,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":404,\"a\":67,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":404,\"a\":82,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":612,\"a\":69,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":600,\"a\":70,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":424,\"a\":71,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":424,\"a\":86,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":464,\"a\":72,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":464,\"a\":87,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":736,\"a\":73,\"owners\":[88]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":65,\"full_literals\":[-14,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":71,\"full_literals\":[-18,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-15,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":72,\"full_literals\":[-19,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":79,\"full_literals\":[-21,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":85,\"full_literals\":[-25,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":80,\"full_literals\":[-22,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":86,\"full_literals\":[-26,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-23,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-27,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-24,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":88,\"full_literals\":[-28,34]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-30,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-32,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-33,-34,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-38,-40,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-37,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[14,39,46,51,54,58,64,69,70,73,79,84,85,88]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[15,40,47,52,55,57,65,67,71,72,80,82,86,87]}]}"
  "60 37 0 45 46 44 43 33 34 31 32 9 23 29 7 10 11 12 21 8 27 59 0\n61 -42 0 60 57 56 0\n62 -41 0 61 53 0\n63 -39 0 61 55 0\n64 34 31 0 36 25 35 19 5 41 42 3 24 1 4 6 30 2 58 0\n65 38 0 62 47 48 37 38 20 26 16 64 52 39 40 22 13 18 28 17 15 14 59 0\n66 -40 0 65 61 54 0\n67 -34 0 66 50 0\n68 -33 0 66 51 0\n69 31 0 67 64 0\n70 -23 0 68 39 0\n71 -27 0 68 40 0\n72 -32 0 69 63 49 0\n73 -15 0 70 22 0\n74 -19 0 71 28 0\n75 -6 0 71 70 15 0\n76 -22 0 72 37 0\n77 -26 0 72 38 0\n78 -14 0 76 20 0\n79 -2 0 76 70 77 71 13 0\n80 -10 0 76 70 71 17 0\n81 -18 0 77 26 0\n82 -8 0 77 76 16 0\n83 -11 0 77 70 76 18 0\n84 -4 0 77 71 14 0\n85 0 79 77 84 82 80 83 75 73 81 74 76 70 78 71 59 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "971d2668da719a6998e65598e938ce8b8ae4785e0fae1746c9aa599964d9715a5994e5955556364d334ad8751d1743d70da398ce364d5334d8b92ccb8ad1b26c5b0ed8791d4731e2749ca719c3783d0f23c4f8b0aa458560b81e8a4a991625454558342d0758330ca344c5322c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6d36d24936d36db4d269a49249a492692492492492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 53), (facetIndex 66), (facetIndex 76)]))
 (.leaf ([(facetIndex 47), (facetIndex 87)])))
 (.branch 3
 (.leaf ([(facetIndex 70), (facetIndex 72), (facetIndex 75)]))
 (.leaf ([(facetIndex 90), (facetIndex 91), (facetIndex 92)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 61), (facetIndex 71), (facetIndex 74), (facetIndex 83)]))
 (.leaf ([(facetIndex 82), (facetIndex 93)])))
 (.branch 7
 (.leaf ([(facetIndex 63), (facetIndex 68), (facetIndex 69), (facetIndex 86)]))
 (.leaf ([(facetIndex 84), (facetIndex 88), (facetIndex 89)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2b6ff3879400005028b6000c200000000002z23;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record004" 53

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record004" "{\"ridges\":[[12,385],[12,386],[19,580],[39,580],[40,386],[48,385],[48,386],[51,385],[51,386],[54,385],[54,386],[55,385],[55,386],[61,204],[62,580],[63,396],[65,580],[67,580],[68,420],[69,452],[71,600],[72,408],[74,712],[75,464],[76,736],[82,204],[83,586],[84,396],[88,420],[89,452],[91,408],[92,464],[93,600]],\"owners\":[[12,385,[63,68,69,72,75],[40,48,51,54,55]],[48,385,[68,69,75],[12,40,51,54,55,63,72]],[51,385,[63,68,69],[12,40,48,54,55,72,75]],[54,385,[63,69,72,75],[12,40,48,51,55,68]],[55,385,[63,68,72],[12,40,48,51,54,69,75]],[12,386,[84,88,89,91,92],[40,48,51,54,55]],[40,386,[91,92],[12,48,51,54,55,84,88,89]],[48,386,[88,89,92],[12,40,51,54,55,84,91]],[51,386,[84,88,89],[12,40,48,54,55,91,92]],[54,386,[84,89,91,92],[12,40,48,51,55,88]],[55,386,[84,88,91],[12,40,48,51,54,89,92]],[19,580,[83,87,93],[39,62,65,67]],[39,580,[93],[19,62,65,67,83,87]],[62,580,[87],[19,39,65,67,83,93]],[65,580,[83,87],[19,39,62,67,93]],[67,580,[83,93],[19,39,62,65,87]],[83,586,[47],[]],[61,204,[82],[]],[82,204,[61],[]],[63,396,[84],[]],[84,396,[63],[]],[68,420,[88],[]],[88,420,[68],[]],[69,452,[89],[]],[89,452,[69],[]],[71,600,[93],[]],[93,600,[71],[]],[72,408,[91],[]],[91,408,[72],[]],[74,712,[],[]],[75,464,[92],[]],[92,464,[75],[]],[76,736,[],[]]],\"edges\":[[41,[19,39,47,53,62,65,67,71,74,76,83,87,93]],[42,[12,40,48,51,54,55,63,68,69,72,75,84,88,89,91,92]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,13,16,17,19,21],[-6,16,17,21],[-7,13,16,17],[-9,13,17,19,21],[-10,13,16,19],[-1,25,27,28,29,30],[-4,29,30],[-6,27,28,30],[-7,25,27,28],[-9,25,28,29,30],[-10,25,27,29],[-2,24,26,31],[-3,31],[-12,26],[-14,24,26],[-15,24,31],[-24,5],[-11,23],[-23,11],[-13,25],[-25,13],[-16,27],[-27,16],[-17,28],[-28,17],[-18,31],[-31,18],[-19,29],[-29,19],[-20],[-21,30],[-30,21],[-22],[-8,32],[-5,33],[-26,33],[-19,34],[-21,34],[-29,35],[-30,35],[-36,11,18,20,24],[-11,36],[-18,36],[-37,23,31],[-23,37],[-31,37],[-13,38],[-16,38],[-17,38],[-25,39],[-27,39],[-28,39],[-33,40],[-32,40],[-35,41],[-34,41],[-34,-35,42],[-41,43],[-40,43],[-40,-41,44],[-40,-42,45],[-46,36,37],[-37,46],[-36,46],[-36,-37,47],[-39,48],[-38,48],[-38,-39,49],[-48,50],[-49,51],[-47,51],[-47,-48,52],[-52,53],[-43,-51,53],[-44,-50,53],[-45,53],[-53],[2,3,5,8,12,14,15,18,20,22,24,26,31],[1,4,6,7,9,10,13,16,17,19,21,25,27,28,29,30]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":385,\"a\":12,\"owners\":[63,68,69,72,75]},{\"tag\":\"mate\",\"ridge\":385,\"a\":48,\"owners\":[68,69,75]},{\"tag\":\"mate\",\"ridge\":385,\"a\":51,\"owners\":[63,68,69]},{\"tag\":\"mate\",\"ridge\":385,\"a\":54,\"owners\":[63,69,72,75]},{\"tag\":\"mate\",\"ridge\":385,\"a\":55,\"owners\":[63,68,72]},{\"tag\":\"mate\",\"ridge\":386,\"a\":12,\"owners\":[84,88,89,91,92]},{\"tag\":\"mate\",\"ridge\":386,\"a\":40,\"owners\":[91,92]},{\"tag\":\"mate\",\"ridge\":386,\"a\":48,\"owners\":[88,89,92]},{\"tag\":\"mate\",\"ridge\":386,\"a\":51,\"owners\":[84,88,89]},{\"tag\":\"mate\",\"ridge\":386,\"a\":54,\"owners\":[84,89,91,92]},{\"tag\":\"mate\",\"ridge\":386,\"a\":55,\"owners\":[84,88,91]},{\"tag\":\"mate\",\"ridge\":580,\"a\":19,\"owners\":[83,87,93]},{\"tag\":\"mate\",\"ridge\":580,\"a\":39,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":580,\"a\":62,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":580,\"a\":65,\"owners\":[83,87]},{\"tag\":\"mate\",\"ridge\":580,\"a\":67,\"owners\":[83,93]},{\"tag\":\"mate\",\"ridge\":586,\"a\":83,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":204,\"a\":61,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":204,\"a\":82,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":396,\"a\":63,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":396,\"a\":84,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":420,\"a\":68,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":420,\"a\":88,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":452,\"a\":69,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":452,\"a\":89,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":600,\"a\":71,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":600,\"a\":93,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":408,\"a\":72,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":408,\"a\":91,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":712,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":464,\"a\":75,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":464,\"a\":92,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":736,\"a\":76,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":53,\"full_literals\":[-8,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":47,\"full_literals\":[-5,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-26,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":72,\"full_literals\":[-19,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-21,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":91,\"full_literals\":[-29,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":92,\"full_literals\":[-30,35]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[61,71,74,83],\"full_literals\":[-36,11,18,20,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":61,\"full_literals\":[-11,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":71,\"full_literals\":[-18,36]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[82,93],\"full_literals\":[-37,23,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-23,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":93,\"full_literals\":[-31,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":63,\"full_literals\":[-13,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":68,\"full_literals\":[-16,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":69,\"full_literals\":[-17,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-25,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":88,\"full_literals\":[-27,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":89,\"full_literals\":[-28,39]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-34,-35,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-41,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-40,-42,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-37,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-38,-39,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-48,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-43,-51,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-50,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[19,39,47,53,62,65,67,71,74,76,83,87,93]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[12,40,48,51,54,55,63,68,69,72,75,84,88,89,91,92]}]}"
  "80 -36 11 18 24 0 30 41 0\n81 -52 0 77 73 0\n82 -45 0 77 76 0\n83 2 3 5 8 12 14 15 18 24 26 31 0 30 33 78 0\n84 46 40 0 53 35 17 36 15 14 54 34 63 64 46 43 13 12 16 83 0\n85 37 40 0 84 53 35 17 45 46 62 18 26 80 0\n86 48 41 0 55 40 39 7 56 38 37 66 67 50 51 52 47 48 49 6 9 11 8 10 79 0\n87 47 -37 0 65 42 43 19 27 44 0\n88 43 0 81 58 59 85 86 72 87 0\n89 -51 0 88 77 74 0\n90 -49 0 89 70 0\n91 -47 0 89 71 0\n92 -37 0 91 87 0\n93 40 0 92 85 0\n94 -42 0 93 82 61 0\n95 39 41 0 55 40 39 7 56 38 37 50 51 52 6 9 11 20 8 22 24 10 79 0\n96 41 0 90 55 56 39 40 37 38 7 95 68 47 48 49 1 3 5 21 2 23 25 4 79 0\n97 44 0 96 93 60 0\n98 -50 0 97 77 75 0\n99 -48 0 98 69 0\n100 -39 0 99 66 0\n101 -38 0 99 67 0\n102 -25 0 100 50 0\n103 -27 0 100 51 0\n104 -28 0 100 52 0\n105 -13 0 101 47 0\n106 -16 0 101 48 0\n107 -17 0 101 49 0\n108 -7 0 102 103 104 9 0\n109 29 30 0 104 103 102 107 106 105 108 8 31 7 28 6 11 10 79 0\n110 -29 0 94 29 39 37 57 0\n111 30 0 110 109 0\n112 21 0 111 32 0\n113 35 0 111 40 0\n114 34 0 112 38 0\n115 0 114 113 94 57 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "b89d2b2aaa66a5a369c669a663995663a4e33a2e2b91e1783eb85d1b26a966659365c569665395556364d3362d2b51d1743db0dc3a8da398ce364e5354cd3a2d8b92ccb86d1b26c5b0ed8791d4731e2749ca719c3783d0f23c4f8a8aa458560b81e8a4a9454550b41d60e4330e2328d1314e0b22c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6da6db6da6da4926da6db6da6da492492492492492492492492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 79)]))
 (.leaf ([(facetIndex 73), (facetIndex 75), (facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 89), (facetIndex 90), (facetIndex 99)]))
 (.leaf ([(facetIndex 93), (facetIndex 95), (facetIndex 98)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 65), (facetIndex 67), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 66), (facetIndex 74), (facetIndex 77), (facetIndex 85)])))
 (.branch 7
 (.leaf ([(facetIndex 87), (facetIndex 91), (facetIndex 92)]))
 (.leaf ([(facetIndex 86), (facetIndex 94), (facetIndex 97)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4f87dec90de800006834c80096z31;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record005" 66

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record005" "{\"ridges\":[[13,193],[14,577],[14,578],[15,386],[37,193],[39,577],[39,578],[40,386],[46,193],[47,577],[47,578],[48,385],[48,386],[50,193],[52,577],[52,578],[53,385],[53,386],[54,193],[55,577],[55,578],[56,386],[58,193],[58,194],[58,386],[59,193],[59,577],[59,578],[65,204],[66,588],[67,396],[69,228],[71,420],[72,452],[73,216],[74,600],[77,712],[78,464],[79,736],[85,204],[86,588],[89,228],[92,452],[93,216],[94,600],[97,712],[98,464],[99,736]],\"owners\":[[13,193,[65,69,72,73,77,78,79],[37,46,50,54,58,59]],[37,193,[73,77,78,79],[13,46,50,54,58,59,65,69,72]],[46,193,[69,72,78,79],[13,37,50,54,58,59,65,73,77]],[50,193,[65,69,72,77,79],[13,37,46,54,58,59,73,78]],[54,193,[65,72,73,77,78],[13,37,46,50,58,59,69,79]],[58,193,[65,69,73,77,79],[13,37,46,50,54,59,72,78]],[59,193,[65,69,72,73,78],[13,37,46,50,54,58,77,79]],[58,194,[85,89,93,97,99],[13,37,46,50,54,59,92,98]],[14,577,[66,70,74,77,79],[39,47,52,55,59]],[39,577,[74,77,79],[14,47,52,55,59,66,70]],[47,577,[70,79],[14,39,52,55,59,66,74,77]],[52,577,[66,70,77,79],[14,39,47,55,59,74]],[55,577,[66,74,77],[14,39,47,52,59,70,79]],[59,577,[66,70,74],[14,39,47,52,55,77,79]],[14,578,[86,90,94,97,99],[39,47,52,55,59]],[39,578,[94,97,99],[14,47,52,55,59,86,90]],[47,578,[90,99],[14,39,52,55,59,86,94,97]],[52,578,[86,90,97,99],[14,39,47,55,59,94]],[55,578,[86,94,97],[14,39,47,52,59,90,99]],[59,578,[86,90,94],[14,39,47,52,55,97,99]],[48,385,[71,72,78],[15,40,53,56,58,67,75]],[53,385,[67,71,72],[15,40,48,56,58,75,78]],[15,386,[87,91,92,95,98],[40,48,53,56,58]],[40,386,[95,98],[15,48,53,56,58,87,91,92]],[48,386,[91,92,98],[15,40,53,56,58,87,95]],[53,386,[87,91,92],[15,40,48,56,58,95,98]],[56,386,[87,92,95,98],[15,40,48,53,58,91]],[58,386,[87,91,95],[15,40,48,53,56,92,98]],[65,204,[85],[]],[85,204,[65],[]],[66,588,[86],[]],[86,588,[66],[]],[67,396,[87],[]],[69,228,[89],[]],[89,228,[69],[]],[71,420,[91],[]],[72,452,[92],[]],[92,452,[72],[]],[73,216,[93],[]],[93,216,[73],[]],[74,600,[94],[]],[94,600,[74],[]],[77,712,[97],[]],[97,712,[77],[]],[78,464,[98],[]],[98,464,[78],[]],[79,736,[99],[]],[99,736,[79],[]]],\"edges\":[[39,[13,37,46,50,54,58,59,65,69,72,73,77,78,79,85,89,92,93,97,98,99]],[41,[14,39,47,52,55,59,66,70,74,77,79,86,90,94,97,99]],[42,[15,40,48,53,56,58,67,71,72,75,78,87,91,92,95,98]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-19,-18],[-21,-6],[-21,-20],[-23,-21],[-25,-8],[-25,-19],[-26,-18],[-26,-25],[-32,-25],[-33,-21],[-36,-21],[-39,-25],[-1,18,21,24,25,28,29,30],[-4,25,28,29,30],[-7,21,24,29,30],[-10,18,21,24,28,30],[-13,18,24,25,28,29],[-16,18,21,25,28,30],[-17,18,21,24,25,29],[-16,31,34,38,41,43],[-2,19,22,26,28,30],[-5,26,28,30],[-8,22,30],[-11,19,22,28,30],[-14,19,26,28],[-17,19,22,26],[-2,32,35,39,41,43],[-5,39,41,43],[-8,35,43],[-11,32,35,41,43],[-14,32,39,41],[-17,32,35,39],[-9,23,24,29],[-12,20,23,24],[-3,33,36,37,40,42],[-6,40,42],[-9,36,37,42],[-12,33,36,37],[-15,33,37,40,42],[-16,33,36,40],[-18,31],[-31,18],[-19,32],[-32,19],[-20,33],[-21,34],[-34,21],[-23,36],[-24,37],[-37,24],[-25,38],[-38,25],[-26,39],[-39,26],[-28,41],[-41,28],[-29,42],[-42,29],[-30,43],[-43,30],[-21,44],[-22,44],[-30,44],[-25,45],[-27,45],[-29,45],[-34,46],[-35,46],[-43,46],[-38,47],[-40,47],[-42,47],[-18,48],[-20,48],[-23,48],[-24,48],[-19,49],[-26,49],[-28,49],[-31,49],[-33,50],[-36,50],[-37,50],[-32,51],[-39,51],[-41,51],[-45,52],[-44,52],[-44,-45,53],[-47,54],[-46,54],[-46,-47,55],[-54,56],[-52,56],[-52,-54,57],[-52,-55,58],[-53,-54,58],[-49,59],[-48,59],[-48,-49,60],[-51,61],[-50,61],[-50,-51,62],[-61,63],[-59,63],[-59,-61,64],[-59,-62,65],[-60,64],[-65,66],[-56,-64,66],[-57,-63,66],[-58,66],[-66],[1,4,7,10,13,16,17,18,21,24,25,28,29,30,31,34,37,38,41,42,43],[2,5,8,11,14,17,19,22,26,28,30,32,35,39,41,43],[3,6,9,12,15,16,20,23,24,27,29,33,36,37,40,42]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":69,\"b\":40},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":71,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":47},{\"tag\":\"incompatible\",\"a\":73,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":65},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":86,\"b\":73},{\"tag\":\"incompatible\",\"a\":87,\"b\":69},{\"tag\":\"incompatible\",\"a\":91,\"b\":69},{\"tag\":\"incompatible\",\"a\":94,\"b\":73},{\"tag\":\"mate\",\"ridge\":193,\"a\":13,\"owners\":[65,69,72,73,77,78,79]},{\"tag\":\"mate\",\"ridge\":193,\"a\":37,\"owners\":[73,77,78,79]},{\"tag\":\"mate\",\"ridge\":193,\"a\":46,\"owners\":[69,72,78,79]},{\"tag\":\"mate\",\"ridge\":193,\"a\":50,\"owners\":[65,69,72,77,79]},{\"tag\":\"mate\",\"ridge\":193,\"a\":54,\"owners\":[65,72,73,77,78]},{\"tag\":\"mate\",\"ridge\":193,\"a\":58,\"owners\":[65,69,73,77,79]},{\"tag\":\"mate\",\"ridge\":193,\"a\":59,\"owners\":[65,69,72,73,78]},{\"tag\":\"mate\",\"ridge\":194,\"a\":58,\"owners\":[85,89,93,97,99]},{\"tag\":\"mate\",\"ridge\":577,\"a\":14,\"owners\":[66,70,74,77,79]},{\"tag\":\"mate\",\"ridge\":577,\"a\":39,\"owners\":[74,77,79]},{\"tag\":\"mate\",\"ridge\":577,\"a\":47,\"owners\":[70,79]},{\"tag\":\"mate\",\"ridge\":577,\"a\":52,\"owners\":[66,70,77,79]},{\"tag\":\"mate\",\"ridge\":577,\"a\":55,\"owners\":[66,74,77]},{\"tag\":\"mate\",\"ridge\":577,\"a\":59,\"owners\":[66,70,74]},{\"tag\":\"mate\",\"ridge\":578,\"a\":14,\"owners\":[86,90,94,97,99]},{\"tag\":\"mate\",\"ridge\":578,\"a\":39,\"owners\":[94,97,99]},{\"tag\":\"mate\",\"ridge\":578,\"a\":47,\"owners\":[90,99]},{\"tag\":\"mate\",\"ridge\":578,\"a\":52,\"owners\":[86,90,97,99]},{\"tag\":\"mate\",\"ridge\":578,\"a\":55,\"owners\":[86,94,97]},{\"tag\":\"mate\",\"ridge\":578,\"a\":59,\"owners\":[86,90,94]},{\"tag\":\"mate\",\"ridge\":385,\"a\":48,\"owners\":[71,72,78]},{\"tag\":\"mate\",\"ridge\":385,\"a\":53,\"owners\":[67,71,72]},{\"tag\":\"mate\",\"ridge\":386,\"a\":15,\"owners\":[87,91,92,95,98]},{\"tag\":\"mate\",\"ridge\":386,\"a\":40,\"owners\":[95,98]},{\"tag\":\"mate\",\"ridge\":386,\"a\":48,\"owners\":[91,92,98]},{\"tag\":\"mate\",\"ridge\":386,\"a\":53,\"owners\":[87,91,92]},{\"tag\":\"mate\",\"ridge\":386,\"a\":56,\"owners\":[87,92,95,98]},{\"tag\":\"mate\",\"ridge\":386,\"a\":58,\"owners\":[87,91,95]},{\"tag\":\"mate\",\"ridge\":204,\"a\":65,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":204,\"a\":85,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":588,\"a\":66,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":588,\"a\":86,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":396,\"a\":67,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":228,\"a\":69,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":228,\"a\":89,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":420,\"a\":71,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":452,\"a\":72,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":452,\"a\":92,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":216,\"a\":73,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":216,\"a\":93,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":600,\"a\":74,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":600,\"a\":94,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":712,\"a\":77,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":712,\"a\":97,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":464,\"a\":78,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":464,\"a\":98,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":736,\"a\":79,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":736,\"a\":99,\"owners\":[79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":69,\"full_literals\":[-21,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-22,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":79,\"full_literals\":[-30,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-25,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":75,\"full_literals\":[-27,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-29,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":89,\"full_literals\":[-34,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":90,\"full_literals\":[-35,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":99,\"full_literals\":[-43,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":93,\"full_literals\":[-38,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":95,\"full_literals\":[-40,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":98,\"full_literals\":[-42,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":65,\"full_literals\":[-18,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":67,\"full_literals\":[-20,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":71,\"full_literals\":[-23,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":72,\"full_literals\":[-24,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":66,\"full_literals\":[-19,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-26,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":77,\"full_literals\":[-28,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-31,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-33,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":91,\"full_literals\":[-36,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":92,\"full_literals\":[-37,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-32,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":94,\"full_literals\":[-39,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":97,\"full_literals\":[-41,51]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-45,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-47,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-54,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-52,-55,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-54,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-48,-49,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-51,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-61,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-59,-62,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-56,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-63,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[13,37,46,50,54,58,59,65,69,72,73,77,78,79,85,89,92,93,97,98,99]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[14,39,47,52,55,59,66,70,74,77,79,86,90,94,97,99]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[15,40,48,53,56,58,67,71,72,75,78,87,91,92,95,98]}]}"
  "117 -65 0 113 109 0\n118 -58 0 113 112 0\n119 59 56 0 94 88 63 62 61 87 66 64 93 91 69 67 90 72 70 98 99 77 78 79 80 73 76 26 56 14 20 13 17 16 50 15 114 0\n120 19 26 41 56 0 54 94 88 63 55 22 93 91 69 68 29 62 21 24 25 26 44 115 0\n121 -19 28 56 0 117 119 107 93 90 72 71 36 94 88 63 61 87 66 65 64 1 43 18 84 103 81 82 83 35 39 45 37 48 38 49 116 0\n122 41 56 0 117 119 107 93 90 72 71 36 94 88 63 61 87 66 65 64 55 121 120 7 53 18 85 103 81 82 83 35 39 45 37 48 38 49 116 0\n123 56 0 117 93 94 90 87 71 72 65 66 36 119 107 122 86 103 81 82 83 35 39 40 45 37 48 38 49 116 0\n124 -64 0 123 113 110 0\n125 -60 0 124 108 0\n126 -41 0 124 56 86 79 101 98 106 0\n127 -28 0 126 55 0\n128 18 21 25 37 42 30 0 126 127 57 49 15 47 14 52 60 18 42 13 19 17 16 114 0\n129 -18 0 125 41 73 80 100 0\n130 -21 37 42 0 118 49 57 2 3 4 10 11 46 61 33 34 67 88 91 96 97 92 89 71 65 35 39 40 116 0\n131 -25 30 0 118 126 127 60 5 6 8 9 12 51 64 25 22 70 87 90 96 97 92 89 68 62 30 32 27 115 0\n132 37 42 30 0 129 131 130 128 0\n133 -37 0 124 50 83 76 102 99 106 0\n134 -24 0 133 49 0\n135 30 0 133 118 113 126 127 60 132 58 72 66 90 87 95 97 96 111 89 92 104 105 62 68 101 98 23 84 85 77 78 31 30 32 28 27 115 0\n136 43 0 135 59 0\n137 44 0 135 63 0\n138 46 0 136 69 0\n139 52 0 137 88 0\n140 54 0 138 91 0\n141 -55 0 139 118 96 0\n142 57 0 140 139 95 0\n143 -53 0 140 118 97 0\n144 -47 0 141 138 92 0\n145 -63 0 142 113 111 0\n146 -45 0 143 137 89 0\n147 -40 0 144 71 0\n148 -42 0 144 72 0\n149 -61 0 145 104 0\n150 -59 0 145 105 0\n151 -27 0 146 65 0\n152 -29 0 146 66 0\n153 -6 0 147 148 36 0\n154 -50 0 149 102 0\n155 -48 0 150 99 0\n156 -33 0 154 81 0\n157 -36 0 154 82 0\n158 -20 0 155 74 0\n159 -23 0 155 75 0\n160 -16 0 156 157 147 40 0\n161 -3 0 156 157 133 147 148 35 0\n162 -15 0 156 133 147 148 39 0\n163 -9 0 157 133 148 37 0\n164 -12 0 157 156 133 38 0\n165 0 161 162 153 163 164 160 158 159 134 151 152 156 157 133 147 148 116 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "25c6a99a2e9c669a6639996358b693a2e4b91e1783eb85a9666592e5c56966539595954d52d70d9352d8751d1743d70da398ce364cb362e4b8ad2b2ad1b26c5b0ed8791d4731e2749ca719d1725c3783c4f8b0d21590e0b81e34629916251560d4342d0758330ca324c5342c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db4da4926db6da6d269249249a493492492492492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 72)]))
 (.leaf ([(facetIndex 81), (facetIndex 92)])))
 (.branch 3
 (.leaf ([(facetIndex 53), (facetIndex 67), (facetIndex 75)]))
 (.leaf ([(facetIndex 71), (facetIndex 73), (facetIndex 74)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 89), (facetIndex 90), (facetIndex 91)]))
 (.leaf ([(facetIndex 63), (facetIndex 66), (facetIndex 69), (facetIndex 70), (facetIndex 85)])))
 (.branch 7
 (.leaf ([(facetIndex 82), (facetIndex 84), (facetIndex 87), (facetIndex 88)]))
 (.leaf ([(facetIndex 86)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1926dee1880004d8768540a0000001z28;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record007" 56

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record007" "{\"ridges\":[[10,162],[12,385],[19,580],[34,162],[39,580],[40,385],[45,162],[49,386],[50,162],[51,385],[52,162],[53,610],[54,162],[54,385],[55,385],[61,577],[61,580],[65,580],[66,404],[67,228],[68,580],[69,420],[70,452],[71,184],[74,424],[75,736],[82,180],[86,610],[87,420],[90,408],[91,424]],\"owners\":[[10,162,[82,85,87,89,91],[34,45,50,52,54]],[34,162,[89,91],[10,45,50,52,54,82,85,87]],[45,162,[82,85,87],[10,34,50,52,54,89,91]],[50,162,[85,87,91],[10,34,45,52,54,82,89]],[52,162,[82,87,89,91],[10,34,45,50,54,85]],[54,162,[82,85,89],[10,34,45,50,52,87,91]],[12,385,[66,69,70,73,74],[40,49,51,54,55]],[40,385,[73,74],[12,49,51,54,55,66,69,70]],[51,385,[69,70,74],[12,40,49,54,55,66,73]],[54,385,[66,70,73],[12,40,49,51,55,69,74]],[55,385,[66,69,73,74],[12,40,49,51,54,70]],[49,386,[84,87,88],[12,40,51,54,55,90,91]],[61,577,[53,75],[19,39,48,65,68,72]],[19,580,[81,86,92],[39,61,65,68]],[39,580,[92],[19,61,65,68,81,86]],[61,580,[86],[19,39,65,68,81,92]],[65,580,[81,86],[19,39,61,68,92]],[68,580,[81,92],[19,39,61,65,86]],[53,610,[86],[]],[86,610,[53],[]],[82,180,[63],[]],[66,404,[84],[]],[67,228,[85],[]],[69,420,[87],[]],[87,420,[69],[]],[70,452,[88],[]],[71,184,[89],[]],[90,408,[73],[]],[74,424,[91],[]],[91,424,[74],[]],[75,736,[],[]]],\"edges\":[[36,[10,34,45,50,52,54,63,67,69,71,74,75,82,85,87,89,91]],[41,[19,39,48,53,61,65,68,72,75,81,86,92]],[42,[12,40,49,51,54,55,66,69,70,73,74,84,87,88,90,91]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,30,32,34,36,38],[-4,36,38],[-7,30,32,34],[-10,32,34,38],[-12,30,34,36,38],[-14,30,32,36],[-2,19,22,23,26,27],[-6,26,27],[-11,22,23,27],[-14,19,23,26],[-15,19,22,26,27],[-9,31,34,35],[-16,13,28],[-3,29,33,39],[-5,39],[-16,33],[-18,29,33],[-21,29,39],[-13,33],[-33,13],[-30,17],[-19,31],[-20,32],[-22,34],[-34,22],[-23,35],[-24,36],[-37,26],[-27,38],[-38,27],[-28],[-8,40],[-25,40],[-29,41],[-39,41],[-13,42],[-26,43],[-27,43],[-36,44],[-38,44],[-17,45],[-22,45],[-32,45],[-31,46],[-34,46],[-35,46],[-33,47],[-41,48],[-40,48],[-43,49],[-42,49],[-49,50],[-48,50],[-48,-49,51],[-45,52],[-44,52],[-47,53],[-46,53],[-52,54],[-52,-53,55],[-50,-55,56],[-51,-54,56],[-56],[1,4,7,10,12,14,17,20,22,24,27,28,30,32,34,36,38],[3,5,8,13,16,18,21,25,28,29,33,39],[2,6,9,11,14,15,19,22,23,26,27,31,34,35,37,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":162,\"a\":10,\"owners\":[82,85,87,89,91]},{\"tag\":\"mate\",\"ridge\":162,\"a\":34,\"owners\":[89,91]},{\"tag\":\"mate\",\"ridge\":162,\"a\":45,\"owners\":[82,85,87]},{\"tag\":\"mate\",\"ridge\":162,\"a\":50,\"owners\":[85,87,91]},{\"tag\":\"mate\",\"ridge\":162,\"a\":52,\"owners\":[82,87,89,91]},{\"tag\":\"mate\",\"ridge\":162,\"a\":54,\"owners\":[82,85,89]},{\"tag\":\"mate\",\"ridge\":385,\"a\":12,\"owners\":[66,69,70,73,74]},{\"tag\":\"mate\",\"ridge\":385,\"a\":40,\"owners\":[73,74]},{\"tag\":\"mate\",\"ridge\":385,\"a\":51,\"owners\":[69,70,74]},{\"tag\":\"mate\",\"ridge\":385,\"a\":54,\"owners\":[66,70,73]},{\"tag\":\"mate\",\"ridge\":385,\"a\":55,\"owners\":[66,69,73,74]},{\"tag\":\"mate\",\"ridge\":386,\"a\":49,\"owners\":[84,87,88]},{\"tag\":\"mate\",\"ridge\":577,\"a\":61,\"owners\":[53,75]},{\"tag\":\"mate\",\"ridge\":580,\"a\":19,\"owners\":[81,86,92]},{\"tag\":\"mate\",\"ridge\":580,\"a\":39,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":580,\"a\":61,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":580,\"a\":65,\"owners\":[81,86]},{\"tag\":\"mate\",\"ridge\":580,\"a\":68,\"owners\":[81,92]},{\"tag\":\"mate\",\"ridge\":610,\"a\":53,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":610,\"a\":86,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":180,\"a\":82,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":404,\"a\":66,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":228,\"a\":67,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":420,\"a\":69,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":420,\"a\":87,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":452,\"a\":70,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":184,\"a\":71,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":408,\"a\":90,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":424,\"a\":74,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":424,\"a\":91,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":736,\"a\":75,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":48,\"full_literals\":[-8,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":72,\"full_literals\":[-25,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":81,\"full_literals\":[-29,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":92,\"full_literals\":[-39,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":53,\"full_literals\":[-13,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-26,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":74,\"full_literals\":[-27,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":89,\"full_literals\":[-36,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":91,\"full_literals\":[-38,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":63,\"full_literals\":[-17,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":69,\"full_literals\":[-22,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-32,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-31,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-34,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-35,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-33,47]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-48,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-53,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-50,-55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":36,\"owners\":[10,34,45,50,52,54,63,67,69,71,74,75,82,85,87,89,91]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[19,39,48,53,61,65,68,72,75,81,86,92]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[12,40,49,51,54,55,66,69,70,73,74,84,87,88,90,91]}]}"
  "67 1 4 7 10 12 14 17 20 22 24 27 30 32 34 36 38 0 31 64 0\n68 3 5 8 13 16 18 21 25 29 33 39 0 31 65 0\n69 50 0 31 52 53 51 48 49 36 34 35 32 33 13 20 14 17 18 15 68 0\n70 -55 0 69 63 61 0\n71 52 0 55 56 41 42 43 39 40 21 25 4 23 2 27 1 29 3 5 6 67 0\n72 54 0 71 59 0\n73 -53 0 71 70 60 0\n74 -51 0 72 63 62 0\n75 -47 0 73 57 0\n76 -46 0 73 58 0\n77 -33 0 75 47 0\n78 -31 0 76 44 0\n79 -34 0 76 45 0\n80 -35 0 76 46 0\n81 -16 0 77 16 0\n82 -13 0 77 19 0\n83 -9 0 78 79 80 12 0\n84 -19 0 78 22 0\n85 -22 0 79 24 0\n86 -23 0 80 26 0\n87 43 0 80 79 78 86 85 84 83 37 38 28 7 10 11 30 8 9 66 0\n88 49 0 87 50 0\n89 -48 0 88 74 54 0\n90 -41 0 89 48 0\n91 -40 0 89 49 0\n92 -29 0 90 34 0\n93 -39 0 90 35 0\n94 -8 0 91 32 0\n95 -25 0 91 33 0\n96 -3 0 92 77 93 14 0\n97 -18 0 92 77 17 0\n98 -21 0 92 93 18 0\n99 -5 0 93 15 0\n100 0 94 97 96 82 81 99 98 95 92 77 93 68 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "b89aa66a5a2e9c669a6639996358b693a2e4b91e1783eb85a9666592e5c56966539595354b59362d4b51d1743db0dc3a8da398ce364e532cf0b62e4b4acab86d1b26c5b0ed8791d4731e2749ca719d1725c3783c4f34a2a1590e0b81e346291550d0b41d60e4330e2328c9314e0b42c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6d369249b6db6db4da492492492492492492492492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 65), (facetIndex 74)]))
 (.leaf ([(facetIndex 83), (facetIndex 92)])))
 (.branch 3
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 77)]))
 (.leaf ([(facetIndex 87), (facetIndex 88), (facetIndex 95)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 73), (facetIndex 75), (facetIndex 76)]))
 (.leaf ([(facetIndex 91), (facetIndex 93), (facetIndex 94)])))
 (.branch 7
 (.leaf ([(facetIndex 66), (facetIndex 68), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 84), (facetIndex 86), (facetIndex 89), (facetIndex 90)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "769bfb7c7200014826c9618z31;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record008" 49

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record008" "{\"ridges\":[[14,578],[15,386],[39,578],[40,386],[48,578],[49,386],[52,578],[53,386],[55,578],[56,386],[58,386],[59,578],[68,404],[71,420],[72,452],[75,408],[76,424],[84,180],[86,404],[89,420],[90,452],[91,184],[93,408],[94,424]],\"owners\":[[14,578,[83,88,92,95],[39,48,52,55,59]],[39,578,[92,95],[14,48,52,55,59,83,88]],[48,578,[88,95],[14,39,52,55,59,83,92]],[52,578,[83,88,95],[14,39,48,55,59,92]],[55,578,[83,92],[14,39,48,52,59,88,95]],[59,578,[83,88,92],[14,39,48,52,55,95]],[15,386,[86,89,90,93,94],[40,49,53,56,58]],[40,386,[93,94],[15,49,53,56,58,86,89,90]],[49,386,[86,89,90],[15,40,53,56,58,93,94]],[53,386,[89,90,94],[15,40,49,56,58,86,93]],[56,386,[86,90,93],[15,40,49,53,58,89,94]],[58,386,[86,89,93,94],[15,40,49,53,56,90]],[84,180,[66],[]],[68,404,[86],[]],[86,404,[68],[]],[71,420,[89],[]],[89,420,[71],[]],[72,452,[90],[]],[90,452,[72],[]],[91,184,[73],[]],[75,408,[93],[]],[93,408,[75],[]],[76,424,[94],[]],[94,424,[76],[]]],\"edges\":[[41,[14,39,48,52,55,59,65,70,74,77,83,88,92,95]],[42,[15,40,49,53,56,58,68,71,72,75,76,86,89,90,93,94]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,24,27,31,34],[-3,31,34],[-5,27,34],[-7,24,27,34],[-9,24,31],[-12,24,27,31],[-2,26,28,29,32,33],[-4,32,33],[-6,26,28,29],[-8,28,29,33],[-10,26,29,32],[-11,26,28,32,33],[-25,14],[-15,26],[-26,15],[-17,28],[-28,17],[-18,29],[-29,18],[-30,19],[-21,32],[-32,21],[-22,33],[-33,22],[-13,35],[-20,35],[-24,36],[-31,36],[-16,37],[-23,37],[-27,38],[-34,38],[-19,39],[-21,39],[-22,39],[-40,30,32,33],[-32,40],[-33,40],[-14,41],[-15,41],[-17,41],[-18,41],[-42,25,26,28,29],[-26,42],[-28,42],[-29,42],[-36,43],[-35,43],[-38,44],[-37,44],[-44,45],[-43,45],[-39,-40,46],[-41,-42,47],[-47,48],[-46,48],[-45,-48,49],[-49],[1,3,5,7,9,12,13,16,20,23,24,27,31,34],[2,4,6,8,10,11,15,17,18,21,22,26,28,29,32,33]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":578,\"a\":14,\"owners\":[83,88,92,95]},{\"tag\":\"mate\",\"ridge\":578,\"a\":39,\"owners\":[92,95]},{\"tag\":\"mate\",\"ridge\":578,\"a\":48,\"owners\":[88,95]},{\"tag\":\"mate\",\"ridge\":578,\"a\":52,\"owners\":[83,88,95]},{\"tag\":\"mate\",\"ridge\":578,\"a\":55,\"owners\":[83,92]},{\"tag\":\"mate\",\"ridge\":578,\"a\":59,\"owners\":[83,88,92]},{\"tag\":\"mate\",\"ridge\":386,\"a\":15,\"owners\":[86,89,90,93,94]},{\"tag\":\"mate\",\"ridge\":386,\"a\":40,\"owners\":[93,94]},{\"tag\":\"mate\",\"ridge\":386,\"a\":49,\"owners\":[86,89,90]},{\"tag\":\"mate\",\"ridge\":386,\"a\":53,\"owners\":[89,90,94]},{\"tag\":\"mate\",\"ridge\":386,\"a\":56,\"owners\":[86,90,93]},{\"tag\":\"mate\",\"ridge\":386,\"a\":58,\"owners\":[86,89,93,94]},{\"tag\":\"mate\",\"ridge\":180,\"a\":84,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":404,\"a\":68,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":404,\"a\":86,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":420,\"a\":71,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":420,\"a\":89,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":452,\"a\":72,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":452,\"a\":90,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":184,\"a\":91,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":408,\"a\":75,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":408,\"a\":93,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":424,\"a\":76,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":424,\"a\":94,\"owners\":[76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":65,\"full_literals\":[-13,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":74,\"full_literals\":[-20,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-24,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":92,\"full_literals\":[-31,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":70,\"full_literals\":[-16,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":77,\"full_literals\":[-23,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":88,\"full_literals\":[-27,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":95,\"full_literals\":[-34,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":73,\"full_literals\":[-19,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":75,\"full_literals\":[-21,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-22,39]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[91,93,94],\"full_literals\":[-40,30,32,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":93,\"full_literals\":[-32,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":94,\"full_literals\":[-33,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":66,\"full_literals\":[-14,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":68,\"full_literals\":[-15,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":71,\"full_literals\":[-17,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":72,\"full_literals\":[-18,41]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[84,86,89,90],\"full_literals\":[-42,25,26,28,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-26,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":89,\"full_literals\":[-28,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":90,\"full_literals\":[-29,42]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-40,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-42,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-45,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[14,39,48,52,55,59,65,70,74,77,83,88,92,95]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[15,40,49,53,56,58,68,71,72,75,76,86,89,90,93,94]}]}"
  "61 45 0 51 52 49 50 47 48 31 32 29 30 27 28 25 26 3 6 2 1 4 5 59 0\n62 -48 0 61 58 57 0\n63 -47 0 62 55 0\n64 -46 0 62 56 0\n65 -42 0 63 54 39 40 41 42 13 15 17 19 43 0\n66 -26 0 65 44 0\n67 -28 0 65 45 0\n68 -29 0 65 46 0\n69 -6 0 66 67 68 9 0\n70 -15 0 66 14 0\n71 -17 0 67 16 0\n72 -18 0 68 18 0\n73 -40 0 64 53 33 34 35 20 22 24 36 0\n74 -32 0 73 37 0\n75 -33 0 73 38 0\n76 -21 0 74 21 0\n77 -2 0 74 67 68 66 75 7 0\n78 -10 0 74 68 66 11 0\n79 -11 0 74 67 66 75 12 0\n80 -22 0 75 23 0\n81 -4 0 75 74 8 0\n82 -8 0 75 68 67 10 0\n83 0 77 81 69 82 78 79 70 71 72 76 80 66 67 68 74 75 60 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00111.record008
