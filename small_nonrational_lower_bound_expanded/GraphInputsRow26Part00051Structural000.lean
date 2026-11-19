module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00051Frames
public import GraphInputsRow26Part00051Leaves
public import GraphInputsRow26Part00051Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00051.record034
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "b62b8ab23a399564d876338ae4785e0fad1cc6b13c6c9aa699964d98e4b9a95a5395554d475a362d2b51d1743d38d538cc7332e2b2ae1b46c3b51cc729c6745c570dd0f23c2f07ccc4c85a4984ea86314c68932619164c5494a52344d48d1314c3312c1b41c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6d34da6d26924934934d34d36924da492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 49), (facetIndex 72), (facetIndex 75)]))
 (.leaf ([(facetIndex 35), (facetIndex 51), (facetIndex 57), (facetIndex 58), (facetIndex 59)])))
 (.branch 3
 (.leaf ([(facetIndex 45), (facetIndex 61), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 27), (facetIndex 31), (facetIndex 32), (facetIndex 33), (facetIndex 55), (facetIndex 77)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 66)]))
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 44), (facetIndex 46)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 30), (facetIndex 34), (facetIndex 36), (facetIndex 37)]))
 (.leaf ([(facetIndex 53), (facetIndex 65)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1800001213c910248638200155005b7639b7b66z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 60), (facetIndex 67), (facetIndex 70)]))
 (.leaf ([(facetIndex 82), (facetIndex 83)])))
 (.branch 3
 (.leaf ([(facetIndex 47), (facetIndex 54)]))
 (.leaf ([(facetIndex 76), (facetIndex 79)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 48), (facetIndex 50), (facetIndex 56)]))
 (.leaf ([(facetIndex 71), (facetIndex 73), (facetIndex 78)])))
 (.branch 7
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 52)]))
 (.leaf ([(facetIndex 74), (facetIndex 80), (facetIndex 81)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "27f7431e8a000000000040861044001bz1f;"⟩
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
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0015 : List Nat := [0, 1, 2, 3]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [2, 3]
def grouped3_0020 : List Nat := [3]
def grouped3_0021 : List Nat := [4, 5]
def grouped3_0022 : List Nat := [4, 5, 6, 7]
def grouped3_0023 : List Nat := [6]
def grouped3_0024 : List Nat := [6, 7]
def grouped3_0025 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00051.record034" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00051.record034" 64

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00051.record034" "{\"ridges\":[[12,164],[15,25],[16,25],[16,529],[18,648],[20,49],[20,560],[21,545],[21,672],[35,164],[39,25],[42,554],[44,49],[45,560],[46,81],[49,25],[53,648],[54,49],[57,164],[58,164],[59,672],[60,25],[60,49],[60,184],[61,560],[64,648],[65,672],[66,648],[67,240],[68,560],[68,672],[69,560],[70,720],[80,554],[82,184],[82,536],[83,720]],\"owners\":[[46,81,[15,49,54,62,63,67,70],[7,32,44,56]],[12,164,[74,79,81],[35,51,57,58,59]],[35,164,[81],[12,51,57,58,59,74,79]],[57,164,[74,81],[12,35,51,58,59,79]],[58,164,[74,79,81],[12,35,51,57,59]],[16,529,[20,45,68,69,70],[40,63,64]],[82,536,[16,40,63],[61,64,80,83]],[18,648,[81,82,83],[53,64,65,66]],[53,648,[82,83],[18,64,65,66,81]],[64,648,[81],[18,53,65,66,82,83]],[66,648,[81,82],[18,53,64,65,83]],[21,545,[20,42,45,52,61,69],[59,65]],[20,560,[80,82],[45,61,68,69]],[45,560,[82],[20,61,68,69,80]],[61,560,[],[20,45,68,69,80,82]],[68,560,[80],[20,45,61,69,82]],[69,560,[80,82],[20,45,61,68]],[21,672,[81,82],[59,65,68]],[59,672,[82],[21,65,68,81]],[65,672,[],[21,59,68,81,82]],[68,672,[81],[21,59,65,82]],[42,554,[80],[]],[80,554,[42],[]],[60,184,[82],[]],[82,184,[60],[]],[67,240,[],[]],[70,720,[83],[]],[83,720,[70],[]]],\"edges\":[[36,[12,21,35,41,47,51,57,58,59,60,65,67,68,74,79,81,82]],[38,[20,21,42,45,52,59,61,65,68,69,80,81,82]],[43,[18,21,53,59,64,65,66,68,70,81,82,83]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00051.record034" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00051.record034\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-20,-19],[-25,-10],[-25,-14],[-28,-25],[-31,-25],[-34,-25],[-38,-11],[-38,-18],[-38,-36],[-39,-20],[-39,-38],[-40,-8],[-40,-27],[-40,-29],[-40,-33],[-40,-35],[-2,-3,-25],[-3,-9,-25],[-3,-17,-25],[-5,-13,-25],[-5,-21,-25],[-15,2,17,21,27,28,32,35],[-1,36,37,39],[-7,39],[-22,36,39],[-23,36,37,39],[-3,5,14,33,34,35],[-40,3,10,28],[-4,39,40,41],[-20,40,41],[-29,39],[-31,39,40],[-6,5,12,14,19,26,34],[-5,38,40],[-14,40],[-26],[-33,38],[-34,38,40],[-6,39,40],[-24,40],[-30],[-33,39],[-12,38],[-38,12],[-25,40],[-40,25],[-32],[-35,41],[-41,35],[-42,14,26,33,34],[-43,27,28,29,31],[-44,8,9,10,13,15],[-45,20,30],[-46,42],[-47,46],[-48,43,44],[-49,45],[-50,48],[-51,49],[-52,47,51],[-52,50],[52],[-35,53],[-41,54],[-16,55],[-37,56],[-12,57],[-38,58],[-53,-54,59],[-56,60],[-55,60],[-59,-60,61],[-57,-58,62],[-62,63],[-61,-63,64],[-64],[1,6,7,11,16,18,22,23,24,25,30,32,33,36,37,39,40],[5,6,12,14,19,24,26,30,33,34,38,39,40],[4,6,20,24,29,30,31,33,35,39,40,41]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":60,\"b\":40},{\"tag\":\"incompatible\",\"a\":60,\"b\":45},{\"tag\":\"incompatible\",\"a\":63,\"b\":60},{\"tag\":\"incompatible\",\"a\":66,\"b\":60},{\"tag\":\"incompatible\",\"a\":69,\"b\":60},{\"tag\":\"incompatible\",\"a\":80,\"b\":41},{\"tag\":\"incompatible\",\"a\":80,\"b\":51},{\"tag\":\"incompatible\",\"a\":80,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":53},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":38},{\"tag\":\"incompatible\",\"a\":82,\"b\":62},{\"tag\":\"incompatible\",\"a\":82,\"b\":64},{\"tag\":\"incompatible\",\"a\":82,\"b\":68},{\"tag\":\"incompatible\",\"a\":82,\"b\":70},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[15,16,60]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[16,39,60]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[16,49,60]},{\"tag\":\"three\",\"ridge\":49,\"vertices\":[20,44,60]},{\"tag\":\"three\",\"ridge\":49,\"vertices\":[20,54,60]},{\"tag\":\"mate\",\"ridge\":81,\"a\":46,\"owners\":[15,49,54,62,63,67,70]},{\"tag\":\"mate\",\"ridge\":164,\"a\":12,\"owners\":[74,79,81]},{\"tag\":\"mate\",\"ridge\":164,\"a\":35,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":164,\"a\":57,\"owners\":[74,81]},{\"tag\":\"mate\",\"ridge\":164,\"a\":58,\"owners\":[74,79,81]},{\"tag\":\"mate\",\"ridge\":529,\"a\":16,\"owners\":[20,45,68,69,70]},{\"tag\":\"mate\",\"ridge\":536,\"a\":82,\"owners\":[16,40,63]},{\"tag\":\"mate\",\"ridge\":648,\"a\":18,\"owners\":[81,82,83]},{\"tag\":\"mate\",\"ridge\":648,\"a\":53,\"owners\":[82,83]},{\"tag\":\"mate\",\"ridge\":648,\"a\":64,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":648,\"a\":66,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":545,\"a\":21,\"owners\":[20,42,45,52,61,69]},{\"tag\":\"mate\",\"ridge\":560,\"a\":20,\"owners\":[80,82]},{\"tag\":\"mate\",\"ridge\":560,\"a\":45,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":560,\"a\":61,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":560,\"a\":68,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":560,\"a\":69,\"owners\":[80,82]},{\"tag\":\"mate\",\"ridge\":672,\"a\":21,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":672,\"a\":59,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":672,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":672,\"a\":68,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":554,\"a\":42,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":554,\"a\":80,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":184,\"a\":60,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":184,\"a\":82,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":240,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":720,\"a\":70,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":720,\"a\":83,\"owners\":[70]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[45,61,68,69],\"full_literals\":[-42,14,26,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[62,63,64,66],\"full_literals\":[-43,27,28,29,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[38,39,40,44,46],\"full_literals\":[-44,8,9,10,13,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[53,65],\"full_literals\":[-45,20,30]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,43,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-50,48,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-52,47,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-52,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-35,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-41,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":47,\"full_literals\":[-16,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":79,\"full_literals\":[-37,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":42,\"full_literals\":[-12,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":80,\"full_literals\":[-38,58]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-54,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-58,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-62,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-61,-63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":36,\"owners\":[12,21,35,41,47,51,57,58,59,60,65,67,68,74,79,81,82]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[20,21,42,45,52,59,61,65,68,69,80,81,82]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,21,53,59,64,65,66,68,70,81,82,83]}]}"
  "80 -42 14 33 34 0 36 50 0\n81 -45 20 0 41 53 0\n82 50 0 62 61 0\n83 48 0 82 58 0\n84 1 6 7 11 16 18 22 23 24 25 33 36 37 39 40 0 41 47 77 0\n85 5 6 12 14 19 24 33 34 38 39 40 0 36 41 78 0\n86 4 6 20 24 29 31 33 35 39 40 41 0 41 79 0\n87 41 39 40 0 42 39 32 31 40 48 30 29 86 0\n88 -38 40 0 76 45 40 7 8 9 11 44 68 25 24 39 42 67 73 74 75 87 49 64 63 69 72 70 71 66 65 23 26 84 0\n89 40 0 62 36 35 40 88 34 37 38 43 80 54 55 60 59 57 81 1 10 33 85 0\n90 -8 0 89 12 0\n91 -27 0 89 13 0\n92 -29 0 89 14 0\n93 -33 0 89 15 0\n94 -35 0 89 16 0\n95 25 0 89 46 0\n96 -10 0 95 2 0\n97 -14 0 95 3 0\n98 -28 0 95 4 0\n99 -31 0 95 5 0\n100 -34 0 95 6 0\n101 3 0 98 96 89 28 0\n102 5 0 93 97 101 100 94 27 0\n103 -43 0 99 91 98 92 51 0\n104 -2 0 101 95 17 0\n105 -9 0 101 95 18 0\n106 -17 0 101 95 19 0\n107 -13 0 102 95 20 0\n108 -21 0 102 95 21 0\n109 44 0 103 83 56 0\n110 15 0 105 109 96 107 90 52 0\n111 0 110 106 104 108 91 98 47 94 22 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00051.record034

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00051.record053
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5e1745b15c4f07caa8ea4e87aa58d64d8763392e1b91e1783eb86d1cc6715c6a95a4e9565391e565a5555355351d58d5352d1b51d1743da8ce3a4cd34cc73a2ccb8ad2b2ac6b46c5b0ee8731d2719e1745c9715c3743c4f0bc1f3323223a314c471325291a4c5454554348d1368388e130cc8b0ac8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6db6d36db6d24d26936924924934d34924926d24da492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 26), (facetIndex 35), (facetIndex 44), (facetIndex 58), (facetIndex 81)]))
 (.leaf ([(facetIndex 32), (facetIndex 36), (facetIndex 49), (facetIndex 51)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 46), (facetIndex 47), (facetIndex 59), (facetIndex 60), (facetIndex 71), (facetIndex 72), (facetIndex 73)]))
 (.leaf ([(facetIndex 40), (facetIndex 42), (facetIndex 55), (facetIndex 65), (facetIndex 68), (facetIndex 69)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 27), (facetIndex 54), (facetIndex 56), (facetIndex 57)]))
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 31), (facetIndex 61), (facetIndex 62)])))
 (.branch 7
 (.leaf ([(facetIndex 25), (facetIndex 41), (facetIndex 43), (facetIndex 45)]))
 (.leaf ([(facetIndex 24), (facetIndex 37), (facetIndex 53), (facetIndex 66)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1241b1d816a4247382084b0cf3039001b6a837z12;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00051.record053" "{\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00051.record053" 69

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00051.record053" "{\"ridges\":[[8,642],[15,41],[18,97],[25,41],[25,42],[36,642],[37,41],[45,642],[46,97],[49,642],[51,642],[55,41],[63,660],[65,41],[66,41],[70,41],[70,680],[71,112],[72,97],[74,720],[75,736],[81,134],[81,138],[85,660],[86,42],[89,42],[89,680],[95,104]],\"owners\":[[81,134,[2,30,36,85],[21,35,84]],[81,138,[4,41,45,89],[21,44,88]],[8,642,[85,89],[36,45,49,51]],[36,642,[89],[8,45,49,51,85]],[45,642,[85],[8,36,49,51,89]],[49,642,[89],[8,36,45,51,85]],[51,642,[85],[8,36,45,49,89]],[18,97,[15,33,40,50,55,64,68,69,75],[46,59,71,72]],[46,97,[15,55,64,68,69,75],[18,33,40,50,59,71,72]],[72,97,[15,33,40,50,55,64,68,69],[18,46,59,71,75]],[95,104,[15,40,55,68,79,88],[65,69,86,90,93]],[71,112,[82,86,90],[18,46,59,65,72,94,95]],[63,660,[85],[]],[85,660,[63],[]],[70,680,[89],[]],[89,680,[70],[]],[74,720,[],[]],[75,736,[],[]]],\"edges\":[[35,[15,18,33,40,46,50,55,59,64,65,68,69,71,72,75,79,82,86,88,90,93,94,95]],[43,[8,36,45,49,51,63,70,74,75,85,89]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00051.record053" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00051.record053\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-6,-1],[-7,-2],[-8,-6],[-8,-7],[-10,-6],[-13,-7],[-14,-6],[-15,-6],[-21,-7],[-26,-18],[-26,-20],[-26,-22],[-28,-7],[-28,-27],[-29,-6],[-29,-7],[-30,-7],[-33,-9],[-33,-11],[-33,-14],[-33,-32],[-34,-7],[-35,-16],[-35,-27],[-36,-35],[-39,-17],[-39,-19],[-39,-21],[-39,-38],[-44,-7],[-46,-7],[-47,-10],[-47,-12],[-47,-15],[-47,-24],[-47,-31],[-50,-18],[-50,-20],[-50,-22],[-50,-25],[-50,-26],[-50,-37],[-50,-49],[-51,-7],[-52,-7],[-53,-7],[-45,1,10,15,47],[-4,-7,-39],[-7,-35,-39],[-16,-28,-39],[-28,-36,-39],[-7,-48,-50],[-45,2,18,22,50],[-3,47,50],[-15,50],[-22,47],[-24,50],[-26,47],[-5,4,13,17,25,28,34,37,38,43],[-23,4,28,34,37,38,43],[-41,4,13,17,25,28,34,37,38],[-54,4,17,28,37,44,49],[-40,46,48,51],[-33,47],[-47,33],[-39,50],[-50,39],[-42],[-43],[-55,8,14,21,29,45],[-56,12,15,24,26],[-57,17,19,28,35,37,38],[-58,9,10,11,31,32],[-59,7,18,20,22],[-60,6,16,27,36],[-61,55],[-61,56],[-62,57],[-63,61],[-63,62],[-64,58],[-65,59,60],[-66,59],[-67,64,66],[-68,64],[-67,65],[-68,66],[-69,63,68],[-69,67],[69],[4,5,13,17,23,25,28,30,34,35,37,38,40,41,43,44,46,48,49,51,52,53,54],[3,15,22,24,26,33,39,42,43,47,50]],\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":24,\"b\":2},{\"tag\":\"incompatible\",\"a\":25,\"b\":4},{\"tag\":\"incompatible\",\"a\":26,\"b\":24},{\"tag\":\"incompatible\",\"a\":26,\"b\":25},{\"tag\":\"incompatible\",\"a\":30,\"b\":24},{\"tag\":\"incompatible\",\"a\":33,\"b\":25},{\"tag\":\"incompatible\",\"a\":35,\"b\":24},{\"tag\":\"incompatible\",\"a\":36,\"b\":24},{\"tag\":\"incompatible\",\"a\":44,\"b\":25},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":51,\"b\":43},{\"tag\":\"incompatible\",\"a\":51,\"b\":45},{\"tag\":\"incompatible\",\"a\":55,\"b\":25},{\"tag\":\"incompatible\",\"a\":55,\"b\":53},{\"tag\":\"incompatible\",\"a\":58,\"b\":24},{\"tag\":\"incompatible\",\"a\":58,\"b\":25},{\"tag\":\"incompatible\",\"a\":59,\"b\":25},{\"tag\":\"incompatible\",\"a\":63,\"b\":29},{\"tag\":\"incompatible\",\"a\":63,\"b\":31},{\"tag\":\"incompatible\",\"a\":63,\"b\":35},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":25},{\"tag\":\"incompatible\",\"a\":65,\"b\":37},{\"tag\":\"incompatible\",\"a\":65,\"b\":53},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":70,\"b\":40},{\"tag\":\"incompatible\",\"a\":70,\"b\":42},{\"tag\":\"incompatible\",\"a\":70,\"b\":44},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":79,\"b\":25},{\"tag\":\"incompatible\",\"a\":82,\"b\":25},{\"tag\":\"incompatible\",\"a\":85,\"b\":30},{\"tag\":\"incompatible\",\"a\":85,\"b\":32},{\"tag\":\"incompatible\",\"a\":85,\"b\":36},{\"tag\":\"incompatible\",\"a\":85,\"b\":49},{\"tag\":\"incompatible\",\"a\":85,\"b\":61},{\"tag\":\"incompatible\",\"a\":89,\"b\":41},{\"tag\":\"incompatible\",\"a\":89,\"b\":43},{\"tag\":\"incompatible\",\"a\":89,\"b\":45},{\"tag\":\"incompatible\",\"a\":89,\"b\":50},{\"tag\":\"incompatible\",\"a\":89,\"b\":51},{\"tag\":\"incompatible\",\"a\":89,\"b\":68},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":90,\"b\":25},{\"tag\":\"incompatible\",\"a\":93,\"b\":25},{\"tag\":\"incompatible\",\"a\":94,\"b\":25},{\"tag\":\"mate\",\"ridge\":134,\"a\":81,\"owners\":[2,30,36,85]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[15,25,70]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[25,65,70]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[37,55,70]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[55,66,70]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[25,86,89]},{\"tag\":\"mate\",\"ridge\":138,\"a\":81,\"owners\":[4,41,45,89]},{\"tag\":\"mate\",\"ridge\":642,\"a\":8,\"owners\":[85,89]},{\"tag\":\"mate\",\"ridge\":642,\"a\":36,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":642,\"a\":45,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":642,\"a\":49,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":642,\"a\":51,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":97,\"a\":18,\"owners\":[15,33,40,50,55,64,68,69,75]},{\"tag\":\"mate\",\"ridge\":97,\"a\":46,\"owners\":[15,55,64,68,69,75]},{\"tag\":\"mate\",\"ridge\":97,\"a\":72,\"owners\":[15,33,40,50,55,64,68,69]},{\"tag\":\"mate\",\"ridge\":104,\"a\":95,\"owners\":[15,40,55,68,79,88]},{\"tag\":\"mate\",\"ridge\":112,\"a\":71,\"owners\":[82,86,90]},{\"tag\":\"mate\",\"ridge\":660,\"a\":63,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":660,\"a\":85,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":680,\"a\":70,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":680,\"a\":89,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":720,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":75,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[26,35,44,58,81],\"full_literals\":[-55,8,14,21,29,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[32,36,49,51],\"full_literals\":[-56,12,15,24,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[40,42,55,65,68,69],\"full_literals\":[-57,17,19,28,35,37,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[29,30,31,61,62],\"full_literals\":[-58,9,10,11,31,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[25,41,43,45],\"full_literals\":[-59,7,18,20,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[24,37,53,66],\"full_literals\":[-60,6,16,27,36]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-63,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,59,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,64,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-68,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-69,63,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-69,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":35,\"owners\":[15,18,33,40,46,50,55,59,64,65,68,69,71,72,75,79,82,86,88,90,93,94,95]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[8,36,45,49,51,63,70,74,75,85,89]}]}"
  "93 67 0 90 89 0\n94 65 0 93 86 0\n95 4 5 13 17 23 25 28 30 34 35 37 38 40 41 44 46 48 49 51 52 53 54 0 69 91 0\n96 3 15 22 24 26 33 39 47 50 0 68 69 92 0\n97 47 50 0 54 56 58 64 55 57 66 96 0\n98 50 0 93 90 55 57 97 32 33 36 65 18 19 20 21 73 81 84 85 83 88 79 76 77 71 10 11 12 74 2 4 9 16 53 70 0\n99 -18 0 98 37 0\n100 -20 0 98 38 0\n101 -22 0 98 39 0\n102 -25 0 98 40 0\n103 -26 0 98 41 0\n104 -37 0 98 42 0\n105 -49 0 98 43 0\n106 39 0 98 67 0\n107 -17 0 106 26 0\n108 -19 0 106 27 0\n109 -21 0 106 28 0\n110 -38 0 106 29 0\n111 -47 0 103 90 32 33 34 35 36 65 71 18 19 21 77 73 79 81 88 85 0\n112 -7 0 106 98 69 105 110 104 102 107 6 13 17 22 30 31 44 45 46 48 49 52 60 63 62 59 61 95 0\n113 -59 0 112 99 100 101 74 0\n114 60 0 113 94 82 0\n115 -66 0 113 83 0\n116 -68 0 115 87 0\n117 63 0 116 90 88 0\n118 61 0 117 79 0\n119 62 0 117 80 0\n120 55 0 118 76 0\n121 57 0 119 78 0\n122 -28 6 0 106 114 14 50 51 75 0\n123 6 0 110 104 121 107 108 114 122 72 23 24 25 75 0\n124 -1 0 123 1 0\n125 -8 0 123 3 0\n126 -10 0 123 5 0\n127 -14 0 123 7 0\n128 -15 0 123 8 0\n129 -29 0 123 15 0\n130 -45 0 124 126 128 111 47 0\n131 0 130 129 125 127 120 109 70 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00051.record053
