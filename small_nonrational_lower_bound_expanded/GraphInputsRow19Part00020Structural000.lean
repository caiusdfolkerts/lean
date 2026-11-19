module
prelude
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00020Frames
public import GraphInputsRow19Part00020Leaves
public import GraphInputsRow19Part00020Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00020.record074
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2cc4f0f2b2aaa4eac695936a3a4e3392e4783e3c6c96a539b15554d68d934cd4b51d0f6c338cd34ccb31ce8b92ccb4ad1b0ee8791cc749d170de0f43c8f13c2f07ec2a28aa91856839314a4a945455434c328c530cc8b0ac4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36d269349b6db49a4db49a49249a4d349a492491249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 46), (facetIndex 51), (facetIndex 52)]))
 (.branch 2
 (.leaf ([(facetIndex 35), (facetIndex 47), (facetIndex 54), (facetIndex 55)]))
 (.leaf ([(facetIndex 31), (facetIndex 62), (facetIndex 65), (facetIndex 66)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 38), (facetIndex 63), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 27), (facetIndex 33), (facetIndex 39), (facetIndex 40), (facetIndex 41)])))
 (.branch 6
 (.leaf ([(facetIndex 30), (facetIndex 36), (facetIndex 42), (facetIndex 43), (facetIndex 44)]))
 (.leaf ([(facetIndex 21), (facetIndex 22), (facetIndex 23), (facetIndex 24), (facetIndex 25), (facetIndex 26)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b090680000240000205b648c52205409b6dbz10;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [1, 2]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [3]
def grouped2_0007 : List Nat := [3, 4]
def grouped2_0008 : List Nat := [3, 4, 5, 6]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00020.record074" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00020.record074" 49

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00020.record074" "{\"ridges\":[[9,13],[15,14],[25,14],[25,268],[26,13],[26,524],[28,261],[31,518],[35,265],[38,522],[46,268],[47,268],[48,13],[51,276],[52,276],[54,296],[55,265],[58,14],[61,14],[62,524],[63,524],[65,580],[66,580],[68,648],[69,648],[71,60],[71,268],[72,204]],\"owners\":[[28,261,[9,47],[11,25,29,51,52]],[35,265,[9,46],[13,25,34,54,55]],[55,265,[9,25,34,46],[13,35,54]],[25,268,[71],[9,46,47,59,60]],[46,268,[60],[9,25,47,59,71]],[47,268,[59],[9,25,46,60,71]],[71,268,[9,25],[46,47,59,60]],[51,276,[59],[11,28,46,52,64,71]],[52,276,[59,64,71],[11,28,46,51]],[54,296,[60],[13,35,47,55,67,71]],[31,518,[15,63],[17,26,32,65,66]],[38,522,[15,62],[19,26,37,68,69]],[26,524,[72],[15,49,50,62,63]],[62,524,[50],[15,26,49,63,72]],[63,524,[49],[15,26,50,62,72]],[65,580,[49,53,72],[17,31,62,66]],[66,580,[49],[17,31,53,62,65,72]],[68,648,[50,56,72],[19,38,63,69]],[69,648,[50],[19,38,56,63,68,72]],[71,60,[45,58],[]],[72,204,[48,61],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00020.record074" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00020.record074\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-9,-3],[-10,-5],[-12,-4],[-13,-6],[-14,-7],[-15,-3],[-16,-4],[-17,-7],[-18,-5],[-18,-7],[-19,-6],[-19,-7],[-21,-3],[-24,-4],[-25,-22],[-27,-3],[-27,-8],[-28,-4],[-28,-8],[-29,-8],[-30,-5],[-31,-6],[-32,-11],[-33,-5],[-35,-6],[-1,-8,-17],[-2,-7,-26],[-7,-26,-29],[-9,1,16],[-12,1,15],[-24,1,7,11,15],[-7,37],[-15,28],[-16,27],[-37,1,7],[-20,27],[-21,27,32,37],[-23,28],[-10,2,31],[-13,2,30],[-8,38],[-30,19],[-31,18],[-33,18,22,38],[-34,18],[-35,19,25,38],[-36,19],[-37,14,26],[-38,17,29],[-39,9,15,20,21],[-40,12,16,23,24],[-41,10,30,33,34],[-42,13,31,35,36],[-43,3,4,5,6,7,8],[-44,40],[-44,41],[-45,39],[-45,44],[-46,42],[-47,43],[-48,46],[-48,47],[-49,45],[-49,48],[49]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":28,\"b\":21},{\"tag\":\"incompatible\",\"a\":31,\"b\":23},{\"tag\":\"incompatible\",\"a\":35,\"b\":22},{\"tag\":\"incompatible\",\"a\":38,\"b\":24},{\"tag\":\"incompatible\",\"a\":45,\"b\":25},{\"tag\":\"incompatible\",\"a\":46,\"b\":21},{\"tag\":\"incompatible\",\"a\":47,\"b\":22},{\"tag\":\"incompatible\",\"a\":48,\"b\":25},{\"tag\":\"incompatible\",\"a\":49,\"b\":23},{\"tag\":\"incompatible\",\"a\":49,\"b\":25},{\"tag\":\"incompatible\",\"a\":50,\"b\":24},{\"tag\":\"incompatible\",\"a\":50,\"b\":25},{\"tag\":\"incompatible\",\"a\":52,\"b\":21},{\"tag\":\"incompatible\",\"a\":55,\"b\":22},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":59,\"b\":21},{\"tag\":\"incompatible\",\"a\":59,\"b\":26},{\"tag\":\"incompatible\",\"a\":60,\"b\":22},{\"tag\":\"incompatible\",\"a\":60,\"b\":26},{\"tag\":\"incompatible\",\"a\":61,\"b\":26},{\"tag\":\"incompatible\",\"a\":62,\"b\":23},{\"tag\":\"incompatible\",\"a\":63,\"b\":24},{\"tag\":\"incompatible\",\"a\":64,\"b\":34},{\"tag\":\"incompatible\",\"a\":65,\"b\":23},{\"tag\":\"incompatible\",\"a\":68,\"b\":24},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[9,26,48]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[15,25,58]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[25,58,61]},{\"tag\":\"mate\",\"ridge\":261,\"a\":28,\"owners\":[9,47]},{\"tag\":\"mate\",\"ridge\":265,\"a\":35,\"owners\":[9,46]},{\"tag\":\"mate\",\"ridge\":265,\"a\":55,\"owners\":[9,25,34,46]},{\"tag\":\"mate\",\"ridge\":268,\"a\":25,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":268,\"a\":46,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":268,\"a\":47,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":268,\"a\":71,\"owners\":[9,25]},{\"tag\":\"mate\",\"ridge\":276,\"a\":51,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":276,\"a\":52,\"owners\":[59,64,71]},{\"tag\":\"mate\",\"ridge\":296,\"a\":54,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":518,\"a\":31,\"owners\":[15,63]},{\"tag\":\"mate\",\"ridge\":522,\"a\":38,\"owners\":[15,62]},{\"tag\":\"mate\",\"ridge\":524,\"a\":26,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":524,\"a\":62,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":524,\"a\":63,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":580,\"a\":65,\"owners\":[49,53,72]},{\"tag\":\"mate\",\"ridge\":580,\"a\":66,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":648,\"a\":68,\"owners\":[50,56,72]},{\"tag\":\"mate\",\"ridge\":648,\"a\":69,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":60,\"a\":71,\"owners\":[45,58]},{\"tag\":\"mate\",\"ridge\":204,\"a\":72,\"owners\":[48,61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[28,46,51,52],\"full_literals\":[-39,9,15,20,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[35,47,54,55],\"full_literals\":[-40,12,16,23,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[31,62,65,66],\"full_literals\":[-41,10,30,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[38,63,68,69],\"full_literals\":[-42,13,31,35,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[21,22,23,24,25,26],\"full_literals\":[-43,3,4,5,6,7,8]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-45,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-48,46,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-49,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-49,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true}]}"
  "66 45 0 65 63 0\n67 48 0 65 64 0\n68 39 0 66 57 0\n69 44 0 66 58 0\n70 46 0 67 61 0\n71 47 0 67 62 0\n72 40 0 69 55 0\n73 41 0 69 56 0\n74 42 0 70 59 0\n75 43 0 71 60 0\n76 -5 0 73 2 9 21 24 45 52 0\n77 -3 0 68 1 6 13 16 50 36 0\n78 -4 0 72 3 7 14 18 51 38 0\n79 -7 0 74 73 5 8 10 12 32 43 45 42 47 48 28 27 49 40 39 53 52 46 44 15 0\n80 -8 0 72 68 79 17 19 20 41 34 36 33 38 49 26 35 30 29 51 50 31 37 23 0\n81 6 0 80 75 79 77 76 78 54 0\n82 -13 0 81 4 0\n83 -19 0 81 11 0\n84 -31 0 81 22 0\n85 -35 0 81 25 0\n86 -36 0 83 47 0\n87 0 85 86 74 84 82 53 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00020.record074
