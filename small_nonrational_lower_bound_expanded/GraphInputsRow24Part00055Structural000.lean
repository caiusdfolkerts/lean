module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00055Frames
public import GraphInputsRow24Part00055Leaves
public import GraphInputsRow24Part00055Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "29c1f1d2aa87a5999655876a398e8b86e2785e0f9d1aa6991e78599565a559555475a358d1b61d2745d0f5c3a8d6364d5334c73a2d8b8acab1ac5b0ee8761e2749d1725c3783d0f23c4f8b09a518661582e07a898a49951625194558342d0758350c6324c5322c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db4d26d249349b49b49349249a492492493492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 69)]))
 (.leaf ([(facetIndex 84)])))
 (.branch 3
 (.leaf ([(facetIndex 87)]))
 (.leaf ([(facetIndex 40), (facetIndex 53)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 64), (facetIndex 72)]))
 (.leaf ([(facetIndex 79), (facetIndex 85)])))
 (.branch 7
 (.leaf ([(facetIndex 82), (facetIndex 86)]))
 (.branch 8
 (.leaf ([(facetIndex 60), (facetIndex 65), (facetIndex 68)]))
 (.leaf ([(facetIndex 78), (facetIndex 88)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "8265106005800000400070074000700000030000000000003z28;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0, 1]
def grouped3_0001 : List Nat := [0, 1, 2, 3]
def grouped3_0003 : List Nat := [2]
def grouped3_0004 : List Nat := [2, 3]
def grouped3_0005 : List Nat := [3]
def grouped3_0006 : List Nat := [4]
def grouped3_0007 : List Nat := [4, 5]
def grouped3_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0009 : List Nat := [5]
def grouped3_0010 : List Nat := [6]
def grouped3_0011 : List Nat := [6, 7, 8]
def grouped3_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [7, 8]
def grouped3_0014 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record000" 39

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record000" "{\"ridges\":[[12,385],[12,386],[22,641],[39,385],[39,386],[40,646],[46,385],[46,386],[47,641],[51,385],[51,386],[53,674],[54,385],[54,386],[61,641],[64,404],[65,660],[68,900],[70,641],[71,641],[72,464],[79,646],[82,404],[85,674],[86,464],[88,660]],\"owners\":[[12,385,[60,64,68,72],[39,46,51,54]],[39,385,[72],[12,46,51,54,60,64,68]],[46,385,[64,68,72],[12,39,51,54,60]],[51,385,[60,68],[12,39,46,54,64,72]],[54,385,[60,64,68],[12,39,46,51,72]],[12,386,[78,82,86],[39,46,51,54]],[39,386,[86],[12,46,51,54,78,82]],[46,386,[82,86],[12,39,51,54,78]],[51,386,[78],[12,39,46,54,82,86]],[54,386,[78,82],[12,39,46,51,86]],[22,641,[40,53,65,68],[47,61,70,71]],[47,641,[65,68],[22,40,53,61,70,71]],[61,641,[53],[22,40,47,65,68,70,71]],[70,641,[40,53,68],[22,47,61,65,71]],[71,641,[40,65,68],[22,47,53,61,70]],[40,646,[79],[]],[79,646,[40],[]],[53,674,[85],[]],[85,674,[53],[]],[64,404,[82],[]],[82,404,[64],[]],[65,660,[88],[]],[88,660,[65],[]],[68,900,[],[]],[72,464,[86],[]],[86,464,[72],[]]],\"edges\":[[42,[12,39,46,51,54,60,64,68,72,78,82,86]],[43,[22,40,47,53,61,65,68,70,71,79,85,88]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-10],[-18,-13],[-1,10,12,14,17],[-3,17],[-5,12,14,17],[-7,10,14],[-9,10,12,14],[-1,18,20,22],[-3,22],[-5,20,22],[-7,18],[-9,18,20],[-2,4,8,13,14],[-6,13,14],[-11,8],[-15,4,8,14],[-16,4,13,14],[-4,19],[-19,4],[-8,21],[-21,8],[-12,20],[-20,12],[-13,23],[-23,13],[-14],[-17,22],[-22,17],[-24,4,8],[-4,24],[-8,24],[-12,25],[-17,25],[-19,26],[-21,26],[-20,27],[-22,27],[-10,28],[-13,28],[-18,29],[-23,29],[-24,30],[-30,31],[-26,32],[-25,32],[-29,33],[-28,33],[-28,-29,34],[-33,35],[-34,36],[-27,35],[-32,-35,37],[-32,-36,38],[-38,39],[-31,-37,39],[-39],[1,3,5,7,9,10,12,14,17,18,20,22],[2,4,6,8,11,13,14,15,16,19,21,23]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":65,\"b\":60},{\"tag\":\"incompatible\",\"a\":78,\"b\":65},{\"tag\":\"mate\",\"ridge\":385,\"a\":12,\"owners\":[60,64,68,72]},{\"tag\":\"mate\",\"ridge\":385,\"a\":39,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":385,\"a\":46,\"owners\":[64,68,72]},{\"tag\":\"mate\",\"ridge\":385,\"a\":51,\"owners\":[60,68]},{\"tag\":\"mate\",\"ridge\":385,\"a\":54,\"owners\":[60,64,68]},{\"tag\":\"mate\",\"ridge\":386,\"a\":12,\"owners\":[78,82,86]},{\"tag\":\"mate\",\"ridge\":386,\"a\":39,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":386,\"a\":46,\"owners\":[82,86]},{\"tag\":\"mate\",\"ridge\":386,\"a\":51,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":386,\"a\":54,\"owners\":[78,82]},{\"tag\":\"mate\",\"ridge\":641,\"a\":22,\"owners\":[40,53,65,68]},{\"tag\":\"mate\",\"ridge\":641,\"a\":47,\"owners\":[65,68]},{\"tag\":\"mate\",\"ridge\":641,\"a\":61,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":641,\"a\":70,\"owners\":[40,53,68]},{\"tag\":\"mate\",\"ridge\":641,\"a\":71,\"owners\":[40,65,68]},{\"tag\":\"mate\",\"ridge\":646,\"a\":40,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":646,\"a\":79,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":674,\"a\":53,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":674,\"a\":85,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":404,\"a\":64,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":404,\"a\":82,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":660,\"a\":65,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":660,\"a\":88,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":900,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":464,\"a\":72,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":464,\"a\":86,\"owners\":[72]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[40,53],\"full_literals\":[-24,4,8]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":40,\"full_literals\":[-4,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":53,\"full_literals\":[-8,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":64,\"full_literals\":[-12,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":72,\"full_literals\":[-17,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-19,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-21,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-20,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-22,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":60,\"full_literals\":[-10,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":65,\"full_literals\":[-13,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":78,\"full_literals\":[-18,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":88,\"full_literals\":[-23,29]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-28,-29,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-34,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-32,-36,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-31,-37,39],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[12,39,46,51,54,60,64,68,72,78,82,86]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[22,40,47,53,61,65,68,70,71,79,85,88]}]}"
  "59 -38 0 56 54 0\n60 1 3 5 7 9 10 12 17 18 20 22 0 26 57 0\n61 2 4 6 8 11 13 15 16 19 21 23 0 26 58 0\n62 13 24 0 26 30 31 16 21 15 19 14 25 17 13 61 0\n63 25 -13 0 26 1 6 2 32 33 5 23 4 28 3 7 60 0\n64 -13 0 59 24 63 39 41 45 48 53 50 0\n65 24 0 64 62 0\n66 30 0 65 42 0\n67 31 0 66 43 0\n68 -37 0 67 56 55 0\n69 35 0 49 51 46 47 36 37 40 38 22 9 27 8 10 11 12 60 0\n70 -32 0 69 68 52 0\n71 -26 0 70 44 0\n72 -19 0 71 34 0\n73 -21 0 71 35 0\n74 -4 0 72 18 0\n75 -8 0 73 20 0\n76 0 75 74 65 29 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3985d16ca71d25c9aa5aa9a66a961da8e1ba1e27b9174571e25a95a719a659959695955554d475a354d8b52d1b61d4749d70da358e9364d5334d331ce8b62d4b4acab1ae1b46c9ba1e1725c3783c8f13c1f198560b961a45915468962529196151560d0b46324c5322c2b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db6d34da4924d24926934926db4924d24d24da692492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 51), (facetIndex 56), (facetIndex 59)]))
 (.leaf ([(facetIndex 86), (facetIndex 87)])))
 (.branch 3
 (.leaf ([(facetIndex 31), (facetIndex 34), (facetIndex 50)]))
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 76)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 78), (facetIndex 80), (facetIndex 85)]))
 (.leaf ([(facetIndex 33), (facetIndex 38), (facetIndex 42), (facetIndex 48), (facetIndex 49)])))
 (.branch 7
 (.leaf ([(facetIndex 79), (facetIndex 81), (facetIndex 82), (facetIndex 83), (facetIndex 84)]))
 (.branch 8
 (.leaf ([(facetIndex 66)]))
 (.leaf ([(facetIndex 88)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "8114666646403033000000700000000000000025500000500050002502z1f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
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
def grouped3_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8]
def grouped3_0016 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record005" 68

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record005" "{\"ridges\":[[10,524],[12,532],[14,296],[15,392],[18,400],[20,352],[27,524],[30,532],[33,282],[37,296],[38,330],[39,392],[45,400],[47,352],[51,284],[52,524],[54,296],[55,524],[57,524],[61,532],[62,532],[63,352],[64,392],[67,296],[67,352],[68,296],[68,392],[69,392],[70,352],[71,400],[72,400],[78,646],[81,330],[82,418],[83,306],[85,156]],\"owners\":[[10,524,[74,76,85],[27,52,55,57]],[27,524,[85],[10,52,55,57,74,76]],[52,524,[76],[10,27,55,57,74,85]],[55,524,[74,76,85],[10,27,52,57]],[57,524,[74],[10,27,52,55,76,85]],[12,532,[74,78,85],[30,52,61,62]],[30,532,[85],[12,52,61,62,74,78]],[61,532,[74,78,85],[12,30,52,62]],[62,532,[74],[12,30,52,61,78,85]],[14,296,[81,82,86],[37,54,67,68]],[37,296,[86],[14,54,67,68,81,82]],[54,296,[81,82],[14,37,67,68,86]],[67,296,[82],[14,37,54,68,81,86]],[68,296,[81,86],[14,37,54,67,82]],[15,392,[79,82,88],[39,64,68,69]],[39,392,[88],[15,64,68,69,79,82]],[64,392,[82],[15,39,68,69,79,88]],[68,392,[79,88],[15,39,64,69,82]],[69,392,[79,82],[15,39,64,68,88]],[18,400,[79,84,88],[45,64,71,72]],[45,400,[88],[18,64,71,72,79,84]],[71,400,[79,88],[18,45,64,72,84]],[72,400,[79,84],[18,45,64,71,88]],[20,352,[81,83,86,87],[47,63,67,70]],[47,352,[86,87],[20,63,67,70,81,83]],[63,352,[81,83],[20,47,67,70,86,87]],[67,352,[83,87],[20,47,63,70,81,86]],[70,352,[81,86],[20,47,63,67,83,87]],[78,646,[31,76],[]],[33,282,[79],[]],[38,330,[81],[]],[81,330,[38],[]],[83,306,[42],[]],[82,418,[48],[]],[85,156,[50,73],[]],[51,284,[],[]]],\"edges\":[[23,[10,12,27,30,31,52,55,57,61,62,74,76,78,85]],[28,[14,15,33,37,38,39,51,54,56,64,66,67,68,69,79,81,82,86,88]],[37,[14,20,37,42,47,48,54,59,63,67,68,70,81,82,83,86,87]],[42,[15,18,39,45,48,49,64,68,69,71,72,79,82,84,88]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,39,40,47],[-7,47],[-21,40],[-23,39,40,47],[-25,39],[-2,39,41,47],[-8,47],[-27,39,41,47],[-28,39],[-3,43,44,48],[-11,48],[-22,43,44],[-32,44],[-33,43,48],[-4,42,44,50],[-13,50],[-30,44],[-33,42,50],[-34,42,44],[-5,42,46,50],[-15,50],[-36,42,50],[-37,42,46],[-6,43,45,48,49],[-16,48,49],[-29,43,45],[-32,45,49],[-35,43,48],[-41,9,40],[-10,42],[-12,43],[-43,12],[-45,14],[-44,17],[-47,19,38],[-20],[-24,51],[-26,51],[-48,52],[-49,52],[-9,53],[-19,53],[-38,54],[-39,54],[-40,54],[-12,55],[-14,55],[-17,55],[-18,55],[-42,56],[-43,56],[-44,56],[-46,56],[-31,57],[-50,58],[-52,59],[-51,59],[-54,60],[-53,60],[-60,61],[-59,-60,62],[-55,63],[-58,64],[-57,64],[-64,65],[-56,65],[-65,66],[-63,66],[-63,-65,67],[-61,-67,68],[-62,-66,68],[-68],[1,2,7,8,9,21,23,25,27,28,39,40,41,47],[3,4,10,11,12,13,20,22,24,30,31,32,33,34,42,43,44,48,50],[3,6,11,14,16,17,22,26,29,32,33,35,43,44,45,48,49],[4,5,13,15,17,18,30,33,34,36,37,42,44,46,50]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":524,\"a\":10,\"owners\":[74,76,85]},{\"tag\":\"mate\",\"ridge\":524,\"a\":27,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":524,\"a\":52,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":524,\"a\":55,\"owners\":[74,76,85]},{\"tag\":\"mate\",\"ridge\":524,\"a\":57,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":532,\"a\":12,\"owners\":[74,78,85]},{\"tag\":\"mate\",\"ridge\":532,\"a\":30,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":532,\"a\":61,\"owners\":[74,78,85]},{\"tag\":\"mate\",\"ridge\":532,\"a\":62,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":296,\"a\":14,\"owners\":[81,82,86]},{\"tag\":\"mate\",\"ridge\":296,\"a\":37,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":296,\"a\":54,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":296,\"a\":67,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":296,\"a\":68,\"owners\":[81,86]},{\"tag\":\"mate\",\"ridge\":392,\"a\":15,\"owners\":[79,82,88]},{\"tag\":\"mate\",\"ridge\":392,\"a\":39,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":392,\"a\":64,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":392,\"a\":68,\"owners\":[79,88]},{\"tag\":\"mate\",\"ridge\":392,\"a\":69,\"owners\":[79,82]},{\"tag\":\"mate\",\"ridge\":400,\"a\":18,\"owners\":[79,84,88]},{\"tag\":\"mate\",\"ridge\":400,\"a\":45,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":400,\"a\":71,\"owners\":[79,88]},{\"tag\":\"mate\",\"ridge\":400,\"a\":72,\"owners\":[79,84]},{\"tag\":\"mate\",\"ridge\":352,\"a\":20,\"owners\":[81,83,86,87]},{\"tag\":\"mate\",\"ridge\":352,\"a\":47,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":352,\"a\":63,\"owners\":[81,83]},{\"tag\":\"mate\",\"ridge\":352,\"a\":67,\"owners\":[83,87]},{\"tag\":\"mate\",\"ridge\":352,\"a\":70,\"owners\":[81,86]},{\"tag\":\"mate\",\"ridge\":646,\"a\":78,\"owners\":[31,76]},{\"tag\":\"mate\",\"ridge\":282,\"a\":33,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":330,\"a\":38,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":330,\"a\":81,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":306,\"a\":83,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":418,\"a\":82,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":156,\"a\":85,\"owners\":[50,73]},{\"tag\":\"mate\",\"ridge\":284,\"a\":51,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":56,\"full_literals\":[-24,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":59,\"full_literals\":[-26,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":86,\"full_literals\":[-48,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-49,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":31,\"full_literals\":[-9,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":50,\"full_literals\":[-19,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-38,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":74,\"full_literals\":[-39,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-40,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":38,\"full_literals\":[-12,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":42,\"full_literals\":[-14,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":48,\"full_literals\":[-17,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":49,\"full_literals\":[-18,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":79,\"full_literals\":[-42,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":81,\"full_literals\":[-43,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-44,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-46,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":66,\"full_literals\":[-31,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":88,\"full_literals\":[-50,58]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-61,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-62,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[10,12,27,30,31,52,55,57,61,62,74,76,78,85]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[14,15,33,37,38,39,51,54,56,64,66,67,68,69,79,81,82,86,88]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[14,20,37,42,47,48,54,59,63,67,68,70,81,82,83,86,87]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[15,18,39,45,48,49,64,68,69,71,72,79,82,84,88]}]}"
  "77 3 4 10 11 12 13 22 24 30 31 32 33 34 42 43 44 48 50 0 36 74 0\n78 60 0 58 59 43 44 45 41 42 5 9 3 29 35 6 8 2 7 1 4 73 0\n79 61 0 78 60 0\n80 -67 0 79 72 70 0\n81 55 59 0 56 40 39 25 11 57 38 46 47 48 32 33 34 14 28 26 24 27 12 10 75 0\n82 59 0 80 56 57 39 37 11 81 62 69 65 66 63 64 50 51 52 55 54 30 31 14 13 17 19 12 10 16 15 77 0\n83 62 0 82 78 61 0\n84 -66 0 83 72 71 0\n85 -65 0 84 67 0\n86 -63 0 84 68 0\n87 -64 0 85 65 0\n88 -56 0 85 66 0\n89 -55 0 86 62 0\n90 -58 0 87 63 0\n91 -42 0 88 50 0\n92 -44 0 88 52 0\n93 -46 0 88 53 0\n94 -17 0 89 48 0\n95 -18 0 89 49 0\n96 -50 0 90 55 0\n97 -30 0 92 17 0\n98 -34 0 92 91 19 0\n99 -37 0 93 91 23 0\n100 -13 0 96 16 0\n101 -15 0 96 21 0\n102 -33 0 96 91 18 0\n103 -36 0 96 91 22 0\n104 -4 0 96 91 92 15 0\n105 -5 0 96 91 93 20 0\n106 0 97 96 104 105 100 101 94 95 98 103 99 91 92 93 102 76 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record014
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5d29c971726a96aa6966a59564d876a386e8789e17b9174571725a95a699964d959695955554d475a364d8b61d2745d68d63a4d534cc73a2d8b52d2b2ac6b86c9b16e8751d2719e1745c9715c3783c8f13c1f1b1920b961a4591546891a465854558344d0b58348d1324c8b0ac2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6da6da49b49b49269249a4924d269269b692492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 60), (facetIndex 70), (facetIndex 71)]))
 (.leaf ([(facetIndex 25), (facetIndex 29), (facetIndex 33), (facetIndex 40), (facetIndex 50), (facetIndex 76)])))
 (.branch 3
 (.leaf ([(facetIndex 58), (facetIndex 63), (facetIndex 67)]))
 (.leaf ([(facetIndex 26), (facetIndex 27), (facetIndex 45), (facetIndex 57)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 38), (facetIndex 41), (facetIndex 44), (facetIndex 51)]))
 (.leaf ([(facetIndex 24), (facetIndex 52), (facetIndex 54), (facetIndex 55), (facetIndex 56)])))
 (.branch 7
 (.leaf ([(facetIndex 49), (facetIndex 62), (facetIndex 66), (facetIndex 72)]))
 (.branch 8
 (.leaf ([(facetIndex 28), (facetIndex 34), (facetIndex 42), (facetIndex 47)]))
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 61)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "10006000026002680023555054160703407410400071888173315z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 84), (facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 39), (facetIndex 53)]))
 (.branch 4
 (.leaf ([(facetIndex 35), (facetIndex 46), (facetIndex 59)]))
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 77)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 81), (facetIndex 83), (facetIndex 88)])))
 (.branch 8
 (.leaf ([(facetIndex 82), (facetIndex 86), (facetIndex 89)]))
 (.branch 9
 (.leaf ([(facetIndex 37), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 73), (facetIndex 87)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "7697116765554044900000008800003000002000000300000020823z23;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
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
def grouped2_0008 : List Nat := [4, 5]
def grouped2_0009 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7, 8]
def grouped2_0012 : List Nat := [7, 8]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0015 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [2, 3, 4]
def grouped3_0020 : List Nat := [3]
def grouped3_0021 : List Nat := [3, 4]
def grouped3_0022 : List Nat := [4]
def grouped3_0023 : List Nat := [5]
def grouped3_0024 : List Nat := [5, 6]
def grouped3_0025 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0026 : List Nat := [6]
def grouped3_0027 : List Nat := [7]
def grouped3_0028 : List Nat := [7, 8, 9]
def grouped3_0029 : List Nat := [8]
def grouped3_0030 : List Nat := [8, 9]
def grouped3_0031 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record014" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record014" 81

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record014" "{\"ridges\":[[4,138],[16,641],[16,648],[19,656],[25,73],[26,138],[27,524],[29,84],[38,138],[41,138],[44,138],[45,138],[45,648],[48,336],[49,656],[50,352],[57,648],[58,84],[60,336],[62,656],[64,216],[66,648],[66,656],[67,352],[69,456],[70,336],[71,336],[72,656],[76,104],[80,326],[83,538],[88,156]],\"owners\":[[4,138,[74,77,83,85],[26,38,41,44,45]],[26,138,[83,85],[4,38,41,44,45,74,77]],[38,138,[77,85],[4,26,41,44,45,74,83]],[41,138,[74,77,83],[4,26,38,44,45,85]],[44,138,[74,77,83],[4,26,38,41,45,85]],[45,138,[74,85],[4,26,38,41,44,77,83]],[25,73,[15,64,65,67,69],[10,37,40,43,52,56]],[27,524,[87,88],[11,54,55,56,57,75,77]],[29,84,[87,89],[12,52,58,60,61,73,78,80]],[58,84,[73,80,87],[12,29,52,60,61,78,89]],[76,104,[15,67],[23,40,84]],[16,641,[19,36,49,62,72],[45,57]],[16,648,[77,83,88],[45,57,66]],[45,648,[88],[16,57,66,77,83]],[57,648,[83],[16,45,66,77,88]],[66,648,[77],[16,45,57,83,88]],[48,336,[89],[17,60,70,71,80,86]],[60,336,[86],[17,48,70,71,80,89]],[70,336,[80],[17,48,60,71,86,89]],[71,336,[80,86,89],[17,48,60,70]],[19,656,[81,83,88],[49,62,66,72]],[49,656,[88],[19,62,66,72,81,83]],[62,656,[83],[19,49,66,72,81,88]],[66,656,[81],[19,49,62,72,83,88]],[72,656,[81,83,88],[19,49,62,66]],[50,352,[89],[20,63,67,70,82,84,86]],[67,352,[82,86,89],[20,50,63,70,84]],[80,326,[35,82],[]],[83,538,[39,75],[]],[88,156,[53,74],[]],[64,216,[],[]],[69,456,[],[]]],\"edges\":[[27,[4,16,26,38,41,44,45,53,57,64,66,68,69,74,77,83,85,88]],[43,[16,19,36,45,49,57,62,66,72,77,81,83,88]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record014" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record014\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-6],[-23,-10],[-26,-2],[-26,-9],[-26,-14],[-40,-6],[-41,-5],[-41,-9],[-41,-14],[-41,-26],[-41,-39],[-1,37,40,44,45],[-6,44,45],[-12,40,45],[-15,37,40,44],[-16,37,40,44],[-17,37,45],[-5,2,27,28,30,32],[-7,47,48],[-8,47,49],[-23,36,41,47],[-39,2,30],[-3,4,11,19,25,35],[-3,40,44,48],[-17,48],[-22,44],[-29,40],[-18,49],[-24,46],[-33,41],[-34,41,46,49],[-4,42,44,48],[-19,48],[-25,44],[-29,42],[-35,42,44,48],[-20,49],[-30,43,46,49],[-41,10,43],[-44,13,38],[-48,21,37],[-27],[-32],[-50,18,24,33,34],[-51,5,8,9,14,20,39],[-52,23,26,30],[-53,6,7,17,22],[-54,19,25,29,35],[-55,50,51],[-56,50],[-56,51],[-57,52],[-57,53],[-58,55],[-58,56,57],[-59,56],[-59,57],[-60,54],[-61,60],[-62,58],[-62,59,61],[62],[-31,63],[-45,64],[-13,65],[-21,65],[-37,66],[-38,66],[-40,66],[-41,67],[-42,68],[-44,68],[-48,68],[-43,69],[-46,69],[-49,69],[-28,70],[-36,71],[-47,71],[-64,72],[-63,72],[-66,73],[-73,74],[-65,74],[-74,75],[-72,75],[-68,76],[-67,76],[-71,77],[-70,77],[-77,78],[-69,78],[-69,-77,79],[-79,80],[-76,-78,80],[-75,-80,81],[-81],[1,3,6,12,15,16,17,21,22,27,29,31,32,37,40,44,45,48],[3,4,11,17,19,22,25,29,35,40,42,44,48]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":36,\"b\":26},{\"tag\":\"incompatible\",\"a\":58,\"b\":35},{\"tag\":\"incompatible\",\"a\":63,\"b\":15},{\"tag\":\"incompatible\",\"a\":63,\"b\":33},{\"tag\":\"incompatible\",\"a\":63,\"b\":40},{\"tag\":\"incompatible\",\"a\":77,\"b\":26},{\"tag\":\"incompatible\",\"a\":80,\"b\":25},{\"tag\":\"incompatible\",\"a\":80,\"b\":33},{\"tag\":\"incompatible\",\"a\":80,\"b\":40},{\"tag\":\"incompatible\",\"a\":80,\"b\":63},{\"tag\":\"incompatible\",\"a\":80,\"b\":76},{\"tag\":\"mate\",\"ridge\":138,\"a\":4,\"owners\":[74,77,83,85]},{\"tag\":\"mate\",\"ridge\":138,\"a\":26,\"owners\":[83,85]},{\"tag\":\"mate\",\"ridge\":138,\"a\":38,\"owners\":[77,85]},{\"tag\":\"mate\",\"ridge\":138,\"a\":41,\"owners\":[74,77,83]},{\"tag\":\"mate\",\"ridge\":138,\"a\":44,\"owners\":[74,77,83]},{\"tag\":\"mate\",\"ridge\":138,\"a\":45,\"owners\":[74,85]},{\"tag\":\"mate\",\"ridge\":73,\"a\":25,\"owners\":[15,64,65,67,69]},{\"tag\":\"mate\",\"ridge\":524,\"a\":27,\"owners\":[87,88]},{\"tag\":\"mate\",\"ridge\":84,\"a\":29,\"owners\":[87,89]},{\"tag\":\"mate\",\"ridge\":84,\"a\":58,\"owners\":[73,80,87]},{\"tag\":\"mate\",\"ridge\":104,\"a\":76,\"owners\":[15,67]},{\"tag\":\"mate\",\"ridge\":641,\"a\":16,\"owners\":[19,36,49,62,72]},{\"tag\":\"mate\",\"ridge\":648,\"a\":16,\"owners\":[77,83,88]},{\"tag\":\"mate\",\"ridge\":648,\"a\":45,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":648,\"a\":57,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":648,\"a\":66,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":336,\"a\":48,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":336,\"a\":60,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":336,\"a\":70,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":336,\"a\":71,\"owners\":[80,86,89]},{\"tag\":\"mate\",\"ridge\":656,\"a\":19,\"owners\":[81,83,88]},{\"tag\":\"mate\",\"ridge\":656,\"a\":49,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":656,\"a\":62,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":656,\"a\":66,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":656,\"a\":72,\"owners\":[81,83,88]},{\"tag\":\"mate\",\"ridge\":352,\"a\":50,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":352,\"a\":67,\"owners\":[82,86,89]},{\"tag\":\"mate\",\"ridge\":326,\"a\":80,\"owners\":[35,82]},{\"tag\":\"mate\",\"ridge\":538,\"a\":83,\"owners\":[39,75]},{\"tag\":\"mate\",\"ridge\":156,\"a\":88,\"owners\":[53,74]},{\"tag\":\"mate\",\"ridge\":216,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":456,\"a\":69,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[48,60,70,71],\"full_literals\":[-50,18,24,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[25,29,33,40,50,76],\"full_literals\":[-51,5,8,9,14,20,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[58,63,67],\"full_literals\":[-52,23,26,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[26,27,45,57],\"full_literals\":[-53,6,7,17,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[49,62,66,72],\"full_literals\":[-54,19,25,29,35]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,50,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,50,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-58,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,56,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-60,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-61,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-62,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-62,59,61],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":68,\"full_literals\":[-31,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-45,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":39,\"full_literals\":[-13,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":53,\"full_literals\":[-21,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-37,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":75,\"full_literals\":[-38,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":77,\"full_literals\":[-40,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":80,\"full_literals\":[-41,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":81,\"full_literals\":[-42,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":83,\"full_literals\":[-44,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-48,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":82,\"full_literals\":[-43,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-46,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":89,\"full_literals\":[-49,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":65,\"full_literals\":[-28,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":73,\"full_literals\":[-36,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":87,\"full_literals\":[-47,71]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-73,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-69,-77,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-79,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-78,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-75,-80,81],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":27,\"owners\":[4,16,26,38,41,44,45,53,57,64,66,68,69,74,77,83,85,88]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[16,19,36,45,49,57,62,66,72,77,81,83,88]}]}"
  "100 58 0 62 60 0\n101 55 0 100 54 0\n102 1 3 6 12 15 16 17 21 22 29 31 37 40 44 45 48 0 42 43 98 0\n103 75 0 85 86 83 84 80 81 82 65 66 64 63 67 68 69 17 41 40 14 24 27 13 26 12 15 16 102 0\n104 -80 0 103 97 96 0\n105 -79 0 104 94 0\n106 69 76 0 62 87 73 72 71 36 34 35 33 48 58 59 61 56 50 88 70 30 75 76 29 28 31 44 0\n107 76 0 62 105 87 71 72 73 32 35 36 26 34 25 33 48 58 59 61 57 53 106 93 89 79 19 47 1 6 23 99 0\n108 -78 0 107 104 95 0\n109 -77 0 108 91 0\n110 -69 0 108 92 0\n111 -71 0 109 89 0\n112 -70 0 109 90 0\n113 -43 0 110 74 0\n114 -46 0 110 75 0\n115 -49 0 110 76 0\n116 -36 0 111 78 0\n117 -47 0 111 79 0\n118 -28 0 112 77 0\n119 -30 0 113 114 115 38 0\n120 -24 0 114 29 0\n121 -18 0 115 28 0\n122 -20 0 115 37 0\n123 -8 0 115 117 20 0\n124 41 -50 0 115 114 120 121 30 31 44 0\n125 -41 0 113 123 122 119 100 7 8 9 10 11 39 45 2 51 46 55 52 0\n126 -23 0 125 116 117 21 0\n127 -50 0 125 124 0\n128 51 0 127 101 49 0\n129 -56 0 127 50 0\n130 57 0 129 100 55 0\n131 52 0 130 52 0\n132 26 0 131 126 119 46 0\n133 -2 0 132 3 0\n134 -9 0 132 4 0\n135 -14 0 132 5 0\n136 -39 0 133 119 22 0\n137 -5 0 133 42 118 119 43 18 0\n138 0 136 135 122 137 123 134 128 45 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record021
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1d86b19c5c96a56a961da8e1b89e17b9174571725a966559365a5655351d68d6352d2b46d4749d17563a4e5354d331ce8b52d2b46c9b16e8789c6725c570de0f23c4f07d68a506a8582e5869164551625494a469a16152548d0b46384c5312c2b81c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36da69b4da49249b4da49269a4934d26d2492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 29), (facetIndex 33), (facetIndex 36), (facetIndex 47), (facetIndex 74)]))
 (.leaf ([(facetIndex 59), (facetIndex 63), (facetIndex 67), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 40), (facetIndex 52), (facetIndex 71), (facetIndex 76)]))
 (.leaf ([(facetIndex 32), (facetIndex 37), (facetIndex 43), (facetIndex 45), (facetIndex 46)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 54), (facetIndex 55), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 50), (facetIndex 53), (facetIndex 56)])))
 (.branch 7
 (.leaf ([(facetIndex 41), (facetIndex 48), (facetIndex 62), (facetIndex 66)]))
 (.leaf ([(facetIndex 27), (facetIndex 28), (facetIndex 30), (facetIndex 31), (facetIndex 34), (facetIndex 35)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "20004013a438020592a1460d8632018fc3fc7ez14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 38), (facetIndex 42)]))
 (.leaf ([(facetIndex 70), (facetIndex 72)])))
 (.branch 3
 (.leaf ([(facetIndex 51), (facetIndex 58), (facetIndex 60)]))
 (.leaf ([(facetIndex 78), (facetIndex 79)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 44), (facetIndex 57)]))
 (.leaf ([(facetIndex 73), (facetIndex 77)])))
 (.branch 7
 (.leaf ([(facetIndex 39), (facetIndex 49), (facetIndex 61)]))
 (.leaf ([(facetIndex 69), (facetIndex 75), (facetIndex 80)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "76e8e290780000320a0000430004000cz1d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
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
def grouped2_0010 : List Nat := [6, 7]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [4, 5, 6, 7]
def grouped3_0022 : List Nat := [5]
def grouped3_0023 : List Nat := [6]
def grouped3_0024 : List Nat := [6, 7]
def grouped3_0025 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record021" "{\"atoms\":[{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record021" 42

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record021" "{\"ridges\":[[32,82],[37,82],[43,82],[45,336],[46,82],[50,140],[53,140],[56,140],[69,92],[73,116],[75,282],[77,306],[80,216]],\"owners\":[[32,82,[75,77],[6,37,43,45,46,69,73]],[37,82,[73,77],[6,32,43,45,46,69,75]],[43,82,[69,75],[6,32,37,45,46,73,77]],[46,82,[69,73,75,77],[6,32,37,43,45]],[50,140,[72,79],[10,29,53,55,56,70,78]],[53,140,[70,72,78],[10,29,50,55,56,79]],[56,140,[70,78,79],[10,29,50,53,55,72]],[45,336,[80],[18,62,66,67,75,77]],[75,282,[39],[]],[77,306,[44],[]],[69,92,[49],[]],[73,116,[57],[]],[80,216,[61],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record021" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record021\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-1,18,19],[-2,17,19],[-4,14,18],[-7,14,17,18,19],[-9,16,21],[-10,15,16,20],[-11,15,20,21],[-6,22],[-18,3],[-19,5],[-14,8],[-17,12],[-22,13],[-23,1,2,4,6,7],[-24,9,10,11],[-25,23],[-26,25],[-27,24],[-28,27],[-29,26],[-29,28],[29],[-15,30],[-16,30],[-20,31],[-21,31],[-5,32],[-12,32],[-33,17,19],[-17,33],[-19,33],[-3,34],[-8,34],[-13,34],[-35,14,18,22],[-14,35],[-18,35],[-22,35],[-30,36],[-31,37],[-37,38],[-36,38],[-32,-33,39],[-34,-35,40],[-40,41],[-39,41],[-38,-41,42],[-42]],\"atoms\":[{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":82,\"a\":32,\"owners\":[75,77]},{\"tag\":\"mate\",\"ridge\":82,\"a\":37,\"owners\":[73,77]},{\"tag\":\"mate\",\"ridge\":82,\"a\":43,\"owners\":[69,75]},{\"tag\":\"mate\",\"ridge\":82,\"a\":46,\"owners\":[69,73,75,77]},{\"tag\":\"mate\",\"ridge\":140,\"a\":50,\"owners\":[72,79]},{\"tag\":\"mate\",\"ridge\":140,\"a\":53,\"owners\":[70,72,78]},{\"tag\":\"mate\",\"ridge\":140,\"a\":56,\"owners\":[70,78,79]},{\"tag\":\"mate\",\"ridge\":336,\"a\":45,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":282,\"a\":75,\"owners\":[39]},{\"tag\":\"mate\",\"ridge\":306,\"a\":77,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":92,\"a\":69,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":116,\"a\":73,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":216,\"a\":80,\"owners\":[61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[32,37,43,45,46],\"full_literals\":[-23,1,2,4,6,7]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[50,53,56],\"full_literals\":[-24,9,10,11]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-25,false,23],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-26,false,25],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-27,false,24],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-28,27,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-29,26,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-29,false,28],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":70,\"full_literals\":[-15,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":72,\"full_literals\":[-16,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":78,\"full_literals\":[-20,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":79,\"full_literals\":[-21,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":44,\"full_literals\":[-5,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":57,\"full_literals\":[-12,32]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[73,77],\"full_literals\":[-33,17,19]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":73,\"full_literals\":[-17,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":77,\"full_literals\":[-19,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":39,\"full_literals\":[-3,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":49,\"full_literals\":[-8,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":61,\"full_literals\":[-13,34]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[69,75,80],\"full_literals\":[-35,14,18,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":69,\"full_literals\":[-14,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":75,\"full_literals\":[-18,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":80,\"full_literals\":[-22,35]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-33,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-34,-35,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-40,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-38,-41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "49 26 0 22 20 0\n50 28 0 22 21 0\n51 25 0 49 17 0\n52 27 0 50 19 0\n53 23 0 51 16 0\n54 24 0 52 18 0\n55 38 0 54 41 42 40 39 25 26 23 24 7 6 5 15 0\n56 -41 0 55 48 47 0\n57 -40 0 56 45 0\n58 -39 0 56 46 0\n59 -35 0 57 44 32 33 34 9 11 13 35 0\n60 -14 0 59 36 0\n61 -18 0 59 37 0\n62 -22 0 59 38 0\n63 -4 0 60 61 3 0\n64 -6 0 62 8 0\n65 -33 0 58 43 27 28 10 12 29 0\n66 -17 0 65 30 0\n67 -19 0 65 31 0\n68 -7 0 66 60 61 67 4 0\n69 -2 0 67 66 2 0\n70 -1 0 67 61 1 0\n71 0 68 69 53 63 70 64 14 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record028
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5e1cc5707c6a93a1ea961da8e1b85e0fb91725a9565391e5c5a5595955551d68d6354d3346d4745d0f5a3a4d938cd331ce8b62d2b2ac6b46c5b0ec6725c570de0f13c2f07d705a2868588e585514c471625494a469a16151548d1368384c3322c2b81c8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "136db69a6db4924d349249269b4d249249b4d2492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 33), (facetIndex 42), (facetIndex 56), (facetIndex 72)]))
 (.leaf ([(facetIndex 27), (facetIndex 35), (facetIndex 50), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 81)])))
 (.branch 3
 (.leaf ([(facetIndex 47), (facetIndex 61), (facetIndex 74)]))
 (.leaf ([(facetIndex 32), (facetIndex 57), (facetIndex 58), (facetIndex 59)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 31), (facetIndex 43), (facetIndex 44), (facetIndex 45)]))
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 66)])))
 (.branch 7
 (.leaf ([(facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 67)]))
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 38), (facetIndex 52)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "8000080000d492106d8db704042482dbc020383f2z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 60), (facetIndex 68)]))
 (.leaf ([(facetIndex 37), (facetIndex 48)])))
 (.branch 3
 (.leaf ([(facetIndex 51), (facetIndex 62)]))
 (.leaf ([(facetIndex 76), (facetIndex 77)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 34), (facetIndex 36), (facetIndex 49)])))
 (.branch 7
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 71)]))
 (.leaf ([(facetIndex 73), (facetIndex 75), (facetIndex 78)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "49dbe38db000008000000042900000000d14z19;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4, 5, 6, 7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1]
def grouped3_0009 : List Nat := [0, 1, 2, 3]
def grouped3_0011 : List Nat := [1]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [2, 3]
def grouped3_0014 : List Nat := [3]
def grouped3_0015 : List Nat := [4]
def grouped3_0016 : List Nat := [4, 5]
def grouped3_0017 : List Nat := [4, 5, 6, 7]
def grouped3_0018 : List Nat := [5]
def grouped3_0019 : List Nat := [6]
def grouped3_0020 : List Nat := [6, 7]
def grouped3_0021 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record028" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record028" 60

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record028" "{\"ridges\":[[4,42],[6,50],[17,385],[28,42],[31,50],[32,84],[35,50],[37,282],[38,42],[39,42],[40,42],[41,385],[43,50],[44,50],[45,50],[46,402],[48,418],[51,284],[55,392],[57,84],[58,84],[59,84],[60,404],[62,452],[66,385],[67,392],[68,912],[76,282],[77,418],[80,452]],\"owners\":[[4,42,[69,71,75,76,77],[28,35,38,39,40]],[28,42,[75,76,77],[4,35,38,39,40,69,71]],[38,42,[69,76,77],[4,28,35,39,40,71,75]],[39,42,[69,71,75,76],[4,28,35,38,40,77]],[40,42,[69,71,75],[4,28,35,38,39,76,77]],[6,50,[69,73,75,76],[31,35,43,44,45]],[31,50,[75,76],[6,35,43,44,45,69,73]],[35,50,[73],[6,31,43,44,45,69,75,76]],[43,50,[69,76],[6,31,35,44,45,73,75]],[44,50,[69,73,75],[6,31,35,43,45,76]],[45,50,[69,73,75,76],[6,31,35,43,44]],[32,84,[78,79],[11,50,57,58,59,70,73]],[57,84,[70,79],[11,32,50,58,59,73,78]],[58,84,[70,73,78],[11,32,50,57,59,79]],[59,84,[70,73,78,79],[11,32,50,57,58]],[17,385,[46,48,60,62,68],[41,55,66,67]],[41,385,[60,62,68],[17,46,48,55,66,67]],[66,385,[46,60,62,68],[17,41,48,55,67]],[55,392,[77],[17,41,66,67,80]],[67,392,[77],[17,41,55,66,80]],[37,282,[76],[]],[76,282,[37],[]],[46,402,[],[]],[48,418,[77],[]],[77,418,[48],[]],[51,284,[79],[]],[60,404,[],[]],[62,452,[80],[]],[80,452,[62],[]],[68,912,[],[]]],\"edges\":[[12,[4,6,28,31,34,35,38,39,40,43,44,45,48,69,71,73,75,76,77]],[42,[17,41,46,48,55,60,62,66,67,68,77,80]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record028" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record028\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,29,31,33,34,35],[-4,33,34,35],[-10,29,34,35],[-11,29,31,33,34],[-12,29,31,33],[-2,29,32,33,34],[-5,33,34],[-8,32],[-14,29,34],[-15,29,32,33],[-16,29,32,33,34],[-6,36,37],[-21,30,37],[-22,30,32,36],[-23,30,32,36,37],[-3,17,18,24,25,28],[-13,24,25,28],[-26,17,24,25,28],[-20,35],[-27,35],[-9,34],[-34,9],[-17],[-18,35],[-35,18],[-19,37],[-24],[-25,38],[-38,25],[-28],[-39,6,21,22,23],[-40,39],[-41,40],[-42,41],[42],[-43,17,24,28],[-44,9,18],[-9,44],[-18,44],[-45,19,25],[-25,45],[-46,34,35],[-34,46],[-35,46],[-37,47],[-38,47],[-7,48],[-29,49],[-30,49],[-31,49],[-32,50],[-33,50],[-36,50],[-51,43,44],[-44,51],[-52,45,46],[-46,52],[-45,52],[-53,51,52],[-52,53],[-51,53],[-51,-52,54],[-47,55],[-47,-48,56],[-50,57],[-49,57],[-57,58],[-55,58],[-55,-57,59],[-56,59],[-53,-59,60],[-54,-58,60],[-60],[1,2,4,5,7,8,10,11,12,14,15,16,18,29,31,32,33,34,35],[3,13,17,18,20,24,25,26,27,28,35,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":42,\"a\":4,\"owners\":[69,71,75,76,77]},{\"tag\":\"mate\",\"ridge\":42,\"a\":28,\"owners\":[75,76,77]},{\"tag\":\"mate\",\"ridge\":42,\"a\":38,\"owners\":[69,76,77]},{\"tag\":\"mate\",\"ridge\":42,\"a\":39,\"owners\":[69,71,75,76]},{\"tag\":\"mate\",\"ridge\":42,\"a\":40,\"owners\":[69,71,75]},{\"tag\":\"mate\",\"ridge\":50,\"a\":6,\"owners\":[69,73,75,76]},{\"tag\":\"mate\",\"ridge\":50,\"a\":31,\"owners\":[75,76]},{\"tag\":\"mate\",\"ridge\":50,\"a\":35,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":50,\"a\":43,\"owners\":[69,76]},{\"tag\":\"mate\",\"ridge\":50,\"a\":44,\"owners\":[69,73,75]},{\"tag\":\"mate\",\"ridge\":50,\"a\":45,\"owners\":[69,73,75,76]},{\"tag\":\"mate\",\"ridge\":84,\"a\":32,\"owners\":[78,79]},{\"tag\":\"mate\",\"ridge\":84,\"a\":57,\"owners\":[70,79]},{\"tag\":\"mate\",\"ridge\":84,\"a\":58,\"owners\":[70,73,78]},{\"tag\":\"mate\",\"ridge\":84,\"a\":59,\"owners\":[70,73,78,79]},{\"tag\":\"mate\",\"ridge\":385,\"a\":17,\"owners\":[46,48,60,62,68]},{\"tag\":\"mate\",\"ridge\":385,\"a\":41,\"owners\":[60,62,68]},{\"tag\":\"mate\",\"ridge\":385,\"a\":66,\"owners\":[46,60,62,68]},{\"tag\":\"mate\",\"ridge\":392,\"a\":55,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":392,\"a\":67,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":282,\"a\":37,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":282,\"a\":76,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":402,\"a\":46,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":418,\"a\":48,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":418,\"a\":77,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":284,\"a\":51,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":404,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":452,\"a\":62,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":452,\"a\":80,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":912,\"a\":68,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[32,57,58,59],\"full_literals\":[-39,6,21,22,23]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-40,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-42,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[46,60,68],\"full_literals\":[-43,17,24,28]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[37,48],\"full_literals\":[-44,9,18]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":37,\"full_literals\":[-9,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":48,\"full_literals\":[-18,44]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[51,62],\"full_literals\":[-45,19,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":62,\"full_literals\":[-25,45]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[76,77],\"full_literals\":[-46,34,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-34,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":77,\"full_literals\":[-35,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":79,\"full_literals\":[-37,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-38,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":34,\"full_literals\":[-7,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":69,\"full_literals\":[-29,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":70,\"full_literals\":[-30,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":71,\"full_literals\":[-31,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":73,\"full_literals\":[-32,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":75,\"full_literals\":[-33,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":78,\"full_literals\":[-36,50]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,43,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-48,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-53,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":12,\"owners\":[4,6,28,31,34,35,38,39,40,43,44,45,48,69,71,73,75,76,77]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[17,41,46,48,55,60,62,66,67,68,77,80]}]}"
  "76 41 0 35 34 0\n77 40 0 76 33 0\n78 39 0 77 32 0\n79 -43 0 23 27 30 36 0\n80 -51 44 0 79 54 0\n81 3 13 18 20 25 26 27 35 38 0 23 27 30 75 0\n82 53 0 30 27 23 60 61 57 58 55 44 41 39 19 20 17 18 29 16 81 0\n83 -59 0 82 73 71 0\n84 -56 0 83 70 0\n85 52 0 82 57 59 43 44 80 21 24 37 0\n86 47 -45 0 45 46 26 28 40 0\n87 44 0 85 84 83 38 39 22 25 42 56 86 63 64 69 47 65 66 51 52 48 50 8 2 7 4 6 10 11 1 3 5 9 74 0\n88 51 0 87 55 0\n89 54 0 88 85 62 0\n90 -58 0 89 73 72 0\n91 -57 0 90 67 0\n92 -55 0 90 68 0\n93 -50 0 91 65 0\n94 -49 0 91 66 0\n95 -47 0 92 63 0\n96 -32 0 93 51 0\n97 -36 0 93 53 0\n98 -30 0 94 49 0\n99 -37 0 95 45 0\n100 -22 0 98 96 97 14 0\n101 -6 0 99 97 12 0\n102 -21 0 99 98 13 0\n103 -23 0 99 96 97 98 15 0\n104 0 100 103 78 101 102 31 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00055.record028
