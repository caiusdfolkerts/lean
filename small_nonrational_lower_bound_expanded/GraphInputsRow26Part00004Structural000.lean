module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00004Frames
public import GraphInputsRow26Part00004Leaves
public import GraphInputsRow26Part00004Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00004.record046
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "7331c8f1caa6a3a718766394e3383ef0761b85c9c66998e5c5c9565c56351d70d6354d3362d8751d0f5c3a8ce3a4e331ce8b62d4b32e2b86c9b0ed8751cc715d0f23c4f0bf881983607b8170631c268962619514650d50d074c318c3322c1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6da6da4da49269a4926d249a6924d3493492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 60), (facetIndex 64), (facetIndex 67)]))
 (.leaf ([(facetIndex 25), (facetIndex 29), (facetIndex 68), (facetIndex 72)])))
 (.branch 3
 (.leaf ([(facetIndex 26), (facetIndex 30), (facetIndex 37), (facetIndex 44)]))
 (.leaf ([(facetIndex 31), (facetIndex 55), (facetIndex 58)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 33), (facetIndex 41), (facetIndex 42), (facetIndex 56)]))
 (.leaf ([(facetIndex 35), (facetIndex 40), (facetIndex 62), (facetIndex 63)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 48), (facetIndex 52), (facetIndex 53), (facetIndex 54)]))
 (.branch 8
 (.leaf ([(facetIndex 47), (facetIndex 49), (facetIndex 61)]))
 (.leaf ([(facetIndex 27), (facetIndex 34), (facetIndex 39)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "100010000557003043666007670020445802058403216821z19;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 65), (facetIndex 66)]))
 (.leaf ([(facetIndex 36), (facetIndex 43), (facetIndex 45)])))
 (.branch 3
 (.leaf ([(facetIndex 50), (facetIndex 57), (facetIndex 59)]))
 (.leaf ([(facetIndex 74), (facetIndex 75)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 32), (facetIndex 38), (facetIndex 51)])))
 (.branch 7
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 71)]))
 (.leaf ([(facetIndex 73), (facetIndex 76), (facetIndex 79)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "f276f8db0000000410000a80008200141005z18;"⟩
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
def grouped3_0015 : List Nat := [2]
def grouped3_0016 : List Nat := [2, 3]
def grouped3_0017 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00004.record046" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00004.record046" 59

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00004.record046" "{\"ridges\":[[14,521],[16,521],[16,648],[17,521],[18,545],[20,896],[24,648],[24,776],[35,521],[36,521],[36,554],[40,648],[42,545],[43,658],[45,674],[49,521],[50,521],[50,556],[56,545],[56,560],[57,788],[59,804],[61,560],[65,736],[66,864],[67,896],[74,554],[75,658],[77,536],[77,556]],\"owners\":[[77,536,[14,35,62,63,75],[49,61,74,78]],[16,648,[24,75],[40,62]],[24,648,[16,40,62,75],[]],[40,648,[24],[16,62,75]],[24,776,[17,54,63,78],[]],[18,545,[36,45,50,59,65,66],[42,56,61]],[42,545,[50,59,65,66],[18,36,45,56,61]],[56,545,[36,45,65,66],[18,42,50,59,61]],[56,560,[74],[18,42,61,77]],[61,560,[],[18,42,56,74,77]],[20,896,[24],[67]],[67,896,[24],[20]],[36,554,[74],[]],[74,554,[36],[]],[43,658,[75],[]],[75,658,[43],[]],[45,674,[],[]],[50,556,[77],[]],[77,556,[50],[]],[57,788,[78],[]],[59,804,[],[]],[65,736,[],[]],[66,864,[],[]]],\"edges\":[[38,[18,36,42,45,50,56,59,61,65,66,74,77]],[43,[16,20,24,40,43,45,62,65,67,75]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00004.record046" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00004.record046\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-8],[-13,-11],[-13,-12],[-14,-2],[-15,-13],[-16,-9],[-18,-10],[-20,-13],[-22,-7],[-22,-20],[-22,-21],[-28,-13],[-28,-18],[-28,-22],[-29,-13],[-29,-22],[-33,-22],[-34,-16],[-36,-12],[-36,-13],[-36,-15],[-36,-17],[-36,-35],[-37,-23],[-38,-22],[-38,-37],[-1,-3,-22],[-2,-13,-21],[-3,-12,-22],[-37,1,12,28,29,36],[-2,6,36],[-6,2,15,28,36],[-15,6],[-6,3,23,29,38],[-4,13,19,22,26,30,31],[-17,22,26,30,31],[-24,13,19,30,31],[-24,35],[-27],[-5,6],[-32,6],[-13,35],[-35,13],[-18,36],[-36,18],[-19],[-22,37],[-37,22],[-25,38],[-26],[-30],[-31],[-39,7,9,33,34],[-40,10,16,17,24],[-41,12,15,28,29],[-42,20,21,27],[-43,8,11,14],[-44,39],[-45,44],[-46,40,41],[-47,41],[-48,42,43],[-49,42],[-50,48],[-51,49],[-52,46,51],[-52,47,50],[-53,47,51],[-54,45,53],[-54,52],[54],[-55,13,18,19],[-13,55],[-18,55],[-56,22,25,26],[-22,56],[-57,35,36],[-35,57],[-58,37,38],[-37,58],[-38,58],[-59,56,57],[-57,59],[-56,59],[4,13,17,19,22,24,26,27,30,31,35,37],[2,5,6,15,18,19,28,30,32,36]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":36,\"b\":27},{\"tag\":\"incompatible\",\"a\":36,\"b\":34},{\"tag\":\"incompatible\",\"a\":36,\"b\":35},{\"tag\":\"incompatible\",\"a\":39,\"b\":16},{\"tag\":\"incompatible\",\"a\":40,\"b\":36},{\"tag\":\"incompatible\",\"a\":41,\"b\":29},{\"tag\":\"incompatible\",\"a\":43,\"b\":33},{\"tag\":\"incompatible\",\"a\":47,\"b\":36},{\"tag\":\"incompatible\",\"a\":50,\"b\":25},{\"tag\":\"incompatible\",\"a\":50,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":62,\"b\":36},{\"tag\":\"incompatible\",\"a\":62,\"b\":43},{\"tag\":\"incompatible\",\"a\":62,\"b\":50},{\"tag\":\"incompatible\",\"a\":63,\"b\":36},{\"tag\":\"incompatible\",\"a\":63,\"b\":50},{\"tag\":\"incompatible\",\"a\":68,\"b\":50},{\"tag\":\"incompatible\",\"a\":72,\"b\":41},{\"tag\":\"incompatible\",\"a\":75,\"b\":35},{\"tag\":\"incompatible\",\"a\":75,\"b\":36},{\"tag\":\"incompatible\",\"a\":75,\"b\":40},{\"tag\":\"incompatible\",\"a\":75,\"b\":42},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":77,\"b\":54},{\"tag\":\"incompatible\",\"a\":78,\"b\":50},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[14,17,50]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[16,36,49]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[17,35,50]},{\"tag\":\"mate\",\"ridge\":536,\"a\":77,\"owners\":[14,35,62,63,75]},{\"tag\":\"mate\",\"ridge\":648,\"a\":16,\"owners\":[24,75]},{\"tag\":\"mate\",\"ridge\":648,\"a\":24,\"owners\":[16,40,62,75]},{\"tag\":\"mate\",\"ridge\":648,\"a\":40,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":776,\"a\":24,\"owners\":[17,54,63,78]},{\"tag\":\"mate\",\"ridge\":545,\"a\":18,\"owners\":[36,45,50,59,65,66]},{\"tag\":\"mate\",\"ridge\":545,\"a\":42,\"owners\":[50,59,65,66]},{\"tag\":\"mate\",\"ridge\":545,\"a\":56,\"owners\":[36,45,65,66]},{\"tag\":\"mate\",\"ridge\":560,\"a\":56,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":560,\"a\":61,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":896,\"a\":20,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":896,\"a\":67,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":554,\"a\":36,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":554,\"a\":74,\"owners\":[36]},{\"tag\":\"mate\",\"ridge\":658,\"a\":43,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":658,\"a\":75,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":674,\"a\":45,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":556,\"a\":50,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":556,\"a\":77,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":788,\"a\":57,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":804,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":864,\"a\":66,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[25,29,68,72],\"full_literals\":[-39,7,9,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[33,41,42,56],\"full_literals\":[-40,10,16,17,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[35,40,62,63],\"full_literals\":[-41,12,15,28,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[47,49,61],\"full_literals\":[-42,20,21,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[27,34,39],\"full_literals\":[-43,8,11,14]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-45,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,40,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,42,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-52,46,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,47,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-53,47,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-54,45,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-54,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[36,43,45],\"full_literals\":[-55,13,18,19]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":36,\"full_literals\":[-13,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":43,\"full_literals\":[-18,55]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[50,57,59],\"full_literals\":[-56,22,25,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":50,\"full_literals\":[-22,56]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[74,75],\"full_literals\":[-57,35,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":74,\"full_literals\":[-35,57]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[77,78],\"full_literals\":[-58,37,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":77,\"full_literals\":[-37,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":78,\"full_literals\":[-38,58]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"edge\",\"edge\":38,\"owners\":[18,36,42,45,50,56,59,61,65,66,74,77]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[16,20,24,40,43,45,62,65,67,75]}]}"
  "87 -42 20 21 0 39 56 0\n88 52 0 71 70 0\n89 -55 13 18 0 46 72 0\n90 -56 22 25 0 50 75 0\n91 4 13 17 22 24 35 37 0 46 50 39 51 52 85 0\n92 2 5 6 15 18 28 32 36 0 46 51 86 0\n93 59 0 52 51 50 46 83 84 78 76 38 42 36 48 35 91 0\n94 58 -56 0 80 81 47 49 90 0\n95 6 28 18 0 45 31 33 40 41 92 0\n96 38 55 0 93 73 43 74 45 77 82 94 49 79 90 24 14 16 95 34 27 29 30 0\n97 55 0 52 51 50 46 73 37 43 96 25 26 36 35 91 0\n98 36 28 0 97 88 44 89 95 1 2 3 5 8 15 55 32 61 4 28 67 57 87 64 62 0\n99 22 -36 0 52 51 50 46 20 37 23 36 48 35 91 0\n100 28 0 52 51 46 88 71 98 19 20 21 45 37 99 22 7 9 10 11 16 17 87 55 63 61 65 66 68 60 69 54 59 6 18 58 53 0\n101 -13 0 100 12 0\n102 -18 0 100 13 0\n103 0 102 101 97 89 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00004.record046

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00004.record059
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "733c272b2ac6a3a71aa6a5a366394e3386e17bc172729c6639716a5a56356354d3346d17783d0ec370f23a8f13a4e33c2d8b52ccb8ad2b1ae1b46c5b0ee8761d4731e2729c6785c9715c3743c8f13c2f07c3ce09c28c94a0e8c60d84e0b81ee05c18c5490e4c50d44d0b41d"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a4da4da69249369369a4926d36da6d36db6d36d36db69b491249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 26), (facetIndex 37), (facetIndex 48), (facetIndex 62), (facetIndex 66)]))
 (.leaf ([(facetIndex 53), (facetIndex 56), (facetIndex 70), (facetIndex 84)])))
 (.branch 3
 (.leaf ([(facetIndex 76), (facetIndex 80)]))
 (.leaf ([(facetIndex 23), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 71), (facetIndex 72), (facetIndex 73), (facetIndex 74)]))
 (.leaf ([(facetIndex 33), (facetIndex 65), (facetIndex 79)])))
 (.branch 7
 (.leaf ([(facetIndex 45), (facetIndex 69), (facetIndex 83)]))
 (.leaf ([(facetIndex 21), (facetIndex 22)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1c02a021248700280036d90080000300000000280000007f8000000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 24), (facetIndex 25), (facetIndex 61)]))
 (.leaf ([(facetIndex 34), (facetIndex 44), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 35), (facetIndex 46), (facetIndex 85)]))
 (.leaf ([(facetIndex 29), (facetIndex 63), (facetIndex 64)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 40), (facetIndex 67), (facetIndex 68)]))
 (.leaf ([(facetIndex 32), (facetIndex 77), (facetIndex 78)])))
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 81), (facetIndex 82)]))
 (.branch 8
 (.leaf ([(facetIndex 27), (facetIndex 28), (facetIndex 30), (facetIndex 31), (facetIndex 36), (facetIndex 39), (facetIndex 42), (facetIndex 47), (facetIndex 54)]))
 (.leaf ([(facetIndex 38), (facetIndex 41), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 55)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "20066005501000000440033000000087088880720167847807210577377z1b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
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
def grouped2_0009 : List Nat := [4, 5, 6, 7]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00004.record059" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":8}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00004.record059" 47

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00004.record059" "{\"ridges\":[[9,641],[19,642],[36,519],[54,579],[55,579],[56,641],[66,529],[66,545],[70,641],[77,660],[78,676],[80,530],[80,546],[84,642]],\"owners\":[[66,529,[29,49,50,63],[7,40,48,62,67]],[66,545,[32,51,52,64],[7,43,48,62,68]],[9,641,[36,49,51,54,63,64],[56,70]],[56,641,[63,64],[9,36,49,51,54,70]],[70,641,[36,49,51,63,64],[9,54,56]],[80,530,[29,49,50,77],[17,40,48,76,81]],[80,546,[32,51,52,78],[17,43,48,76,82]],[19,642,[36,49,51,54,77,78],[56,84]],[84,642,[36,49,51,77,78],[19,54,56]],[36,519,[29,32],[]],[54,579,[55],[]],[55,579,[54],[]],[77,660,[63],[]],[78,676,[64],[]]],\"edges\":[[43,[9,19,36,49,51,54,56,63,64,70,77,78,84]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00004.record059" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00004.record059\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-5,-3],[-5,-4],[-6,-5],[-7,-3],[-7,-4],[-7,-5],[-9,-3],[-9,-4],[-9,-6],[-9,-7],[-10,-3],[-10,-4],[-11,-3],[-11,-4],[-13,-3],[-13,-4],[-13,-6],[-13,-7],[-14,-3],[-14,-4],[-14,-5],[-14,-9],[-14,-13],[-15,-3],[-15,-4],[-16,-3],[-16,-4],[-16,-5],[-16,-6],[-16,-9],[-16,-13],[-16,-14],[-16,-15],[-17,-3],[-17,-4],[-17,-6],[-17,-14],[-18,-3],[-18,-4],[-18,-12],[-21,-6],[-21,-7],[-22,-14],[-22,-21],[-23,-6],[-23,-16],[-23,-21],[-23,-22],[-25,-19],[-27,-6],[-27,-7],[-27,-21],[-27,-22],[-27,-23],[-29,-6],[-29,-22],[-30,-5],[-30,-9],[-30,-13],[-30,-24],[-31,-19],[-24,6,14,15,22],[-24,7,16,17,23],[-1,8,14,16,18,22,23],[-20,22,23],[-26,8,14,16,22,23],[-30,6,14,15,28],[-30,7,16,17,29],[-2,8,14,16,18,28,29],[-32,8,14,16,28,29],[-8,6,7],[-18,19],[-19,18],[-28,22],[-29,23],[-33,5,9,13,21,24],[-34,27,30],[-35,12,25,31],[-36,3,4],[-37,33],[-38,34],[-39,37,38],[-40,37],[-40,38],[-41,35,36],[-42,36],[-43,41],[-44,42],[-45,39],[-45,40,44],[-45,43],[45],[-46,6,22,23],[-6,46],[-22,46],[-23,46],[-47,10,11,14,15,16,17,19],[-14,47],[-15,47],[-16,47],[-17,47],[1,2,8,14,16,18,20,22,23,26,28,29,32]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":26,\"b\":21},{\"tag\":\"incompatible\",\"a\":26,\"b\":22},{\"tag\":\"incompatible\",\"a\":29,\"b\":26},{\"tag\":\"incompatible\",\"a\":32,\"b\":21},{\"tag\":\"incompatible\",\"a\":32,\"b\":22},{\"tag\":\"incompatible\",\"a\":32,\"b\":26},{\"tag\":\"incompatible\",\"a\":37,\"b\":21},{\"tag\":\"incompatible\",\"a\":37,\"b\":22},{\"tag\":\"incompatible\",\"a\":37,\"b\":29},{\"tag\":\"incompatible\",\"a\":37,\"b\":32},{\"tag\":\"incompatible\",\"a\":38,\"b\":21},{\"tag\":\"incompatible\",\"a\":38,\"b\":22},{\"tag\":\"incompatible\",\"a\":41,\"b\":21},{\"tag\":\"incompatible\",\"a\":41,\"b\":22},{\"tag\":\"incompatible\",\"a\":48,\"b\":21},{\"tag\":\"incompatible\",\"a\":48,\"b\":22},{\"tag\":\"incompatible\",\"a\":48,\"b\":29},{\"tag\":\"incompatible\",\"a\":48,\"b\":32},{\"tag\":\"incompatible\",\"a\":49,\"b\":21},{\"tag\":\"incompatible\",\"a\":49,\"b\":22},{\"tag\":\"incompatible\",\"a\":49,\"b\":26},{\"tag\":\"incompatible\",\"a\":49,\"b\":37},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":21},{\"tag\":\"incompatible\",\"a\":50,\"b\":22},{\"tag\":\"incompatible\",\"a\":51,\"b\":21},{\"tag\":\"incompatible\",\"a\":51,\"b\":22},{\"tag\":\"incompatible\",\"a\":51,\"b\":26},{\"tag\":\"incompatible\",\"a\":51,\"b\":29},{\"tag\":\"incompatible\",\"a\":51,\"b\":37},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":21},{\"tag\":\"incompatible\",\"a\":52,\"b\":22},{\"tag\":\"incompatible\",\"a\":52,\"b\":29},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":54,\"b\":21},{\"tag\":\"incompatible\",\"a\":54,\"b\":22},{\"tag\":\"incompatible\",\"a\":54,\"b\":45},{\"tag\":\"incompatible\",\"a\":62,\"b\":29},{\"tag\":\"incompatible\",\"a\":62,\"b\":32},{\"tag\":\"incompatible\",\"a\":63,\"b\":49},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":29},{\"tag\":\"incompatible\",\"a\":64,\"b\":51},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":69,\"b\":55},{\"tag\":\"incompatible\",\"a\":76,\"b\":29},{\"tag\":\"incompatible\",\"a\":76,\"b\":32},{\"tag\":\"incompatible\",\"a\":76,\"b\":62},{\"tag\":\"incompatible\",\"a\":76,\"b\":63},{\"tag\":\"incompatible\",\"a\":76,\"b\":64},{\"tag\":\"incompatible\",\"a\":78,\"b\":29},{\"tag\":\"incompatible\",\"a\":78,\"b\":63},{\"tag\":\"incompatible\",\"a\":80,\"b\":26},{\"tag\":\"incompatible\",\"a\":80,\"b\":37},{\"tag\":\"incompatible\",\"a\":80,\"b\":48},{\"tag\":\"incompatible\",\"a\":80,\"b\":66},{\"tag\":\"incompatible\",\"a\":83,\"b\":55},{\"tag\":\"mate\",\"ridge\":529,\"a\":66,\"owners\":[29,49,50,63]},{\"tag\":\"mate\",\"ridge\":545,\"a\":66,\"owners\":[32,51,52,64]},{\"tag\":\"mate\",\"ridge\":641,\"a\":9,\"owners\":[36,49,51,54,63,64]},{\"tag\":\"mate\",\"ridge\":641,\"a\":56,\"owners\":[63,64]},{\"tag\":\"mate\",\"ridge\":641,\"a\":70,\"owners\":[36,49,51,63,64]},{\"tag\":\"mate\",\"ridge\":530,\"a\":80,\"owners\":[29,49,50,77]},{\"tag\":\"mate\",\"ridge\":546,\"a\":80,\"owners\":[32,51,52,78]},{\"tag\":\"mate\",\"ridge\":642,\"a\":19,\"owners\":[36,49,51,54,77,78]},{\"tag\":\"mate\",\"ridge\":642,\"a\":84,\"owners\":[36,49,51,77,78]},{\"tag\":\"mate\",\"ridge\":519,\"a\":36,\"owners\":[29,32]},{\"tag\":\"mate\",\"ridge\":579,\"a\":54,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":579,\"a\":55,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":660,\"a\":77,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":676,\"a\":78,\"owners\":[64]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[26,37,48,62,66],\"full_literals\":[-33,5,9,13,21,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[76,80],\"full_literals\":[-34,27,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[45,69,83],\"full_literals\":[-35,12,25,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[21,22],\"full_literals\":[-36,3,4]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,37,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-40,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-41,35,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-42,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-45,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-45,40,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-45,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[29,63,64],\"full_literals\":[-46,6,22,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":29,\"full_literals\":[-6,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":63,\"full_literals\":[-22,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":64,\"full_literals\":[-23,46]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[38,41,49,50,51,52,55],\"full_literals\":[-47,10,11,14,15,16,17,19]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":49,\"full_literals\":[-14,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":50,\"full_literals\":[-15,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":51,\"full_literals\":[-16,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":52,\"full_literals\":[-17,47]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[9,19,36,49,51,54,56,63,64,70,77,78,84]}]}"
  "103 39 0 92 89 0\n104 43 0 92 91 0\n105 41 0 104 87 0\n106 14 16 18 8 46 0 96 75 95 74 65 66 70 64 69 102 0\n107 16 17 18 7 46 0 92 94 71 96 75 63 68 106 19 20 21 22 23 79 86 88 90 83 84 80 81 76 77 52 0\n108 -16 46 0 92 95 74 94 26 27 28 30 31 32 33 79 62 67 86 88 90 83 84 80 81 76 77 52 0\n109 18 7 46 0 94 71 108 106 107 37 0\n110 -7 0 92 4 5 6 10 18 42 51 79 86 88 90 83 84 80 81 76 77 60 0\n111 -18 0 105 38 39 40 72 79 49 61 85 78 0\n112 -19 0 111 73 0\n113 46 0 111 110 109 0\n114 -40 -23 0 54 47 83 84 80 81 77 57 58 59 60 76 0\n115 -3 14 16 -47 0 112 11 13 24 34 97 0\n116 14 -23 -47 0 92 112 114 90 88 86 46 115 79 12 14 25 35 97 0\n117 -23 -47 0 92 114 90 88 86 116 19 20 79 0\n118 -3 14 -47 0 26 115 0\n119 -4 14 -47 0 112 12 14 25 27 35 97 0\n120 -47 6 0 113 92 117 93 43 44 53 118 119 79 86 88 90 83 84 80 81 77 57 58 59 60 76 0\n121 -40 6 0 113 110 120 101 100 84 114 81 75 93 68 53 77 0\n122 -3 -33 24 21 0 1 7 15 76 0\n123 -22 6 0 92 110 103 121 90 88 86 120 101 100 44 48 53 56 63 68 77 81 82 80 122 79 2 8 16 76 0\n124 6 0 92 113 103 120 98 99 121 90 88 86 123 74 93 62 67 47 54 77 81 82 80 122 79 2 8 16 76 0\n125 -5 0 124 3 0\n126 -9 0 124 9 0\n127 -13 0 124 17 0\n128 -16 0 124 29 0\n129 -17 0 124 36 0\n130 -21 0 124 41 0\n131 -23 0 124 45 0\n132 -27 0 124 50 0\n133 -29 0 124 55 0\n134 -24 0 131 128 110 129 63 0\n135 -30 0 133 128 110 129 68 0\n136 -33 0 134 127 126 125 130 76 0\n137 -34 0 135 132 77 0\n138 -37 0 136 80 0\n139 -38 0 137 81 0\n140 0 138 139 103 82 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00004.record059
