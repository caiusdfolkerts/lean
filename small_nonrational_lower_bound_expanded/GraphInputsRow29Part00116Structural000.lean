module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00116Frames
public import GraphInputsRow29Part00116Leaves
public import GraphInputsRow29Part00116Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record019
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2ccb296a5693ab19c669966659564da8e938ce8b86e8785eb256956539b15c569565655554d68d934cd8b46d8745de0ec368d6364d53a2e4b52ccb8ad2b1ae1b46c5b61e4751e2749ca719e1745c9715c8f0f1c24c83aa18c60da0e1382e079c14c439a14c50d60d1342d0768360d4330d2344c3382c4b0ac1b81c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6926db4924926da49b6d2492492492492492492492492489249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 51), (facetIndex 54), (facetIndex 57), (facetIndex 80), (facetIndex 98)]))
 (.leaf ([(facetIndex 41), (facetIndex 45), (facetIndex 47), (facetIndex 49), (facetIndex 73), (facetIndex 78), (facetIndex 91), (facetIndex 96)])))
 (.branch 3
 (.leaf ([(facetIndex 38), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 84), (facetIndex 85), (facetIndex 86), (facetIndex 87), (facetIndex 88), (facetIndex 89), (facetIndex 90)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 65)]))
 (.leaf ([(facetIndex 40), (facetIndex 44), (facetIndex 48), (facetIndex 64), (facetIndex 79), (facetIndex 97)])))
 (.branch 7
 (.leaf ([(facetIndex 50), (facetIndex 52), (facetIndex 53), (facetIndex 55), (facetIndex 56), (facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 39), (facetIndex 42), (facetIndex 43), (facetIndex 46)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "290002db6db000a4000a4924a5924d86c3618d3cdfcde8z1c;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 83)]))
 (.branch 2
 (.leaf ([(facetIndex 101)]))
 (.leaf ([(facetIndex 102)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 81), (facetIndex 82)]))
 (.leaf ([(facetIndex 99), (facetIndex 100)])))
 (.branch 6
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 92), (facetIndex 93), (facetIndex 94), (facetIndex 95)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "8c800db60000000d802db4z37;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
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
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record019" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record019" 57

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record019" "{\"ridges\":[[11,259],[12,259],[25,273],[25,289],[35,290],[51,259],[51,273],[54,259],[54,289],[65,259],[73,273],[73,304],[80,273],[80,289],[92,340],[93,404],[94,356],[95,420],[98,274],[98,290],[100,360]],\"owners\":[[25,273,[11,41,51,60,61,74,75,81],[73,80]],[51,273,[25,73,74,75],[11,41,60,61,80,81]],[73,273,[11,51,60,61,81],[25,41,74,75,80]],[80,273,[11,41,60,61,74,75],[25,51,73,81]],[98,274,[11,41,60,61,92,93],[35,51,91,99]],[25,289,[12,45,54,62,63,76,77,82],[73,80]],[54,289,[25,73,76,77],[12,45,62,63,80,82]],[80,289,[12,45,62,63,76,77],[25,54,73,82]],[35,290,[12,45,54,62,63,94,95,100],[91,98]],[98,290,[12,45,62,63,94,95],[35,54,91,100]],[73,304,[35,98],[25,80,91]],[92,340,[74],[]],[93,404,[75],[]],[94,356,[76],[]],[95,420,[77],[]],[100,360,[82],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record019" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record019\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-6,-5],[-7,-6],[-8,-6],[-9,-5],[-9,-7],[-9,-8],[-10,-6],[-10,-9],[-17,-14],[-20,-13],[-20,-15],[-20,-16],[-20,-18],[-20,-19],[-21,-20],[-23,-2],[-23,-14],[-23,-17],[-23,-20],[-24,-2],[-24,-14],[-24,-17],[-24,-20],[-25,-1],[-25,-14],[-25,-17],[-25,-20],[-25,-23],[-25,-24],[-26,-1],[-26,-14],[-26,-17],[-26,-20],[-26,-23],[-26,-24],[-27,-22],[-29,-6],[-29,-9],[-29,-11],[-29,-12],[-29,-28],[-30,-6],[-30,-9],[-30,-11],[-30,-12],[-30,-28],[-31,-6],[-31,-9],[-31,-11],[-31,-12],[-31,-28],[-32,-6],[-32,-9],[-32,-11],[-32,-12],[-32,-28],[-33,-29],[-33,-30],[-33,-31],[-33,-32],[-35,-14],[-35,-17],[-35,-20],[-35,-34],[-36,-14],[-36,-17],[-36,-20],[-36,-34],[-37,-29],[-37,-30],[-37,-31],[-37,-32],[-42,-29],[-42,-30],[-42,-31],[-42,-32],[-43,-35],[-43,-36],[-1,-2,-27],[-1,-17,-27],[-2,-14,-27],[-3,1,6,14,23,24,29,30,35],[-14,3,28,29,30],[-28,1,14,23,24,35],[-34,1,6,23,24,29,30],[-43,1,6,23,24,38,39],[-3,2,9,17,25,26,31,32,36],[-17,3,28,31,32],[-34,2,9,25,26,31,32],[-4,2,9,17,25,26,40,41,44],[-43,2,9,25,26,40,41],[-28,4,43],[-38,29],[-39,30],[-40,31],[-41,32],[-44,36],[-45,14,17,20,34,43],[-46,6,9,11,12,28,33,37,42],[-47,23,24,25,26,27],[-48,13,15,16,18,19,21,22],[-49,5,7,8,10],[-50,45],[-50,46],[-51,50],[-52,47],[-53,48],[-53,49],[-54,52],[-54,53],[-55,51],[-55,54],[55],[-56,35,36],[-35,56],[-36,56],[-57,29,30,31,32],[-29,57],[-30,57],[-31,57],[-32,57]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":41,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":45,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":42},{\"tag\":\"incompatible\",\"a\":45,\"b\":43},{\"tag\":\"incompatible\",\"a\":46,\"b\":41},{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":54,\"b\":51},{\"tag\":\"incompatible\",\"a\":57,\"b\":50},{\"tag\":\"incompatible\",\"a\":57,\"b\":52},{\"tag\":\"incompatible\",\"a\":57,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":60,\"b\":12},{\"tag\":\"incompatible\",\"a\":60,\"b\":51},{\"tag\":\"incompatible\",\"a\":60,\"b\":54},{\"tag\":\"incompatible\",\"a\":60,\"b\":57},{\"tag\":\"incompatible\",\"a\":61,\"b\":12},{\"tag\":\"incompatible\",\"a\":61,\"b\":51},{\"tag\":\"incompatible\",\"a\":61,\"b\":54},{\"tag\":\"incompatible\",\"a\":61,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":11},{\"tag\":\"incompatible\",\"a\":62,\"b\":51},{\"tag\":\"incompatible\",\"a\":62,\"b\":54},{\"tag\":\"incompatible\",\"a\":62,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":11},{\"tag\":\"incompatible\",\"a\":63,\"b\":51},{\"tag\":\"incompatible\",\"a\":63,\"b\":54},{\"tag\":\"incompatible\",\"a\":63,\"b\":57},{\"tag\":\"incompatible\",\"a\":63,\"b\":60},{\"tag\":\"incompatible\",\"a\":63,\"b\":61},{\"tag\":\"incompatible\",\"a\":65,\"b\":59},{\"tag\":\"incompatible\",\"a\":74,\"b\":41},{\"tag\":\"incompatible\",\"a\":74,\"b\":45},{\"tag\":\"incompatible\",\"a\":74,\"b\":47},{\"tag\":\"incompatible\",\"a\":74,\"b\":49},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":41},{\"tag\":\"incompatible\",\"a\":75,\"b\":45},{\"tag\":\"incompatible\",\"a\":75,\"b\":47},{\"tag\":\"incompatible\",\"a\":75,\"b\":49},{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":76,\"b\":41},{\"tag\":\"incompatible\",\"a\":76,\"b\":45},{\"tag\":\"incompatible\",\"a\":76,\"b\":47},{\"tag\":\"incompatible\",\"a\":76,\"b\":49},{\"tag\":\"incompatible\",\"a\":76,\"b\":73},{\"tag\":\"incompatible\",\"a\":77,\"b\":41},{\"tag\":\"incompatible\",\"a\":77,\"b\":45},{\"tag\":\"incompatible\",\"a\":77,\"b\":47},{\"tag\":\"incompatible\",\"a\":77,\"b\":49},{\"tag\":\"incompatible\",\"a\":77,\"b\":73},{\"tag\":\"incompatible\",\"a\":78,\"b\":74},{\"tag\":\"incompatible\",\"a\":78,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":76},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":51},{\"tag\":\"incompatible\",\"a\":81,\"b\":54},{\"tag\":\"incompatible\",\"a\":81,\"b\":57},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":51},{\"tag\":\"incompatible\",\"a\":82,\"b\":54},{\"tag\":\"incompatible\",\"a\":82,\"b\":57},{\"tag\":\"incompatible\",\"a\":82,\"b\":80},{\"tag\":\"incompatible\",\"a\":91,\"b\":74},{\"tag\":\"incompatible\",\"a\":91,\"b\":75},{\"tag\":\"incompatible\",\"a\":91,\"b\":76},{\"tag\":\"incompatible\",\"a\":91,\"b\":77},{\"tag\":\"incompatible\",\"a\":96,\"b\":74},{\"tag\":\"incompatible\",\"a\":96,\"b\":75},{\"tag\":\"incompatible\",\"a\":96,\"b\":76},{\"tag\":\"incompatible\",\"a\":96,\"b\":77},{\"tag\":\"incompatible\",\"a\":98,\"b\":81},{\"tag\":\"incompatible\",\"a\":98,\"b\":82},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[11,12,65]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[11,54,65]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[12,51,65]},{\"tag\":\"mate\",\"ridge\":273,\"a\":25,\"owners\":[11,41,51,60,61,74,75,81]},{\"tag\":\"mate\",\"ridge\":273,\"a\":51,\"owners\":[25,73,74,75]},{\"tag\":\"mate\",\"ridge\":273,\"a\":73,\"owners\":[11,51,60,61,81]},{\"tag\":\"mate\",\"ridge\":273,\"a\":80,\"owners\":[11,41,60,61,74,75]},{\"tag\":\"mate\",\"ridge\":274,\"a\":98,\"owners\":[11,41,60,61,92,93]},{\"tag\":\"mate\",\"ridge\":289,\"a\":25,\"owners\":[12,45,54,62,63,76,77,82]},{\"tag\":\"mate\",\"ridge\":289,\"a\":54,\"owners\":[25,73,76,77]},{\"tag\":\"mate\",\"ridge\":289,\"a\":80,\"owners\":[12,45,62,63,76,77]},{\"tag\":\"mate\",\"ridge\":290,\"a\":35,\"owners\":[12,45,54,62,63,94,95,100]},{\"tag\":\"mate\",\"ridge\":290,\"a\":98,\"owners\":[12,45,62,63,94,95]},{\"tag\":\"mate\",\"ridge\":304,\"a\":73,\"owners\":[35,98]},{\"tag\":\"mate\",\"ridge\":340,\"a\":92,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":404,\"a\":93,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":356,\"a\":94,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":420,\"a\":95,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":360,\"a\":100,\"owners\":[82]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[51,54,57,80,98],\"full_literals\":[-45,14,17,20,34,43]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[41,45,47,49,73,78,91,96],\"full_literals\":[-46,6,9,11,12,28,33,37,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[60,61,62,63,65],\"full_literals\":[-47,23,24,25,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[50,52,53,55,56,58,59],\"full_literals\":[-48,13,15,16,18,19,21,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[39,42,43,46],\"full_literals\":[-49,5,7,8,10]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-51,50,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,48,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-54,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-55,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-55,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[81,82],\"full_literals\":[-56,35,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":81,\"full_literals\":[-35,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-36,56]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[74,75,76,77],\"full_literals\":[-57,29,30,31,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-29,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":75,\"full_literals\":[-30,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":76,\"full_literals\":[-31,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":77,\"full_literals\":[-32,57]}]}"
  "122 51 0 113 111 0\n123 54 0 113 112 0\n124 50 0 122 105 0\n125 52 0 123 109 0\n126 53 0 123 110 0\n127 45 0 124 103 0\n128 46 0 124 104 0\n129 47 0 125 106 0\n130 48 0 126 107 0\n131 49 0 126 108 0\n132 -33 -57 0 57 58 59 60 117 0\n133 -28 30 32 -57 0 41 51 117 0\n134 -42 32 -57 0 73 74 75 117 0\n135 -29 28 42 33 0 128 37 38 39 40 69 99 0\n136 30 32 -57 0 128 134 132 133 135 117 47 48 49 50 71 99 0\n137 32 -57 0 128 132 134 136 42 43 44 45 46 70 99 0\n138 -57 0 128 132 137 52 53 54 55 56 72 76 99 0\n139 -29 0 138 118 0\n140 -30 0 138 119 0\n141 -31 0 138 120 0\n142 -32 0 138 121 0\n143 -38 0 139 93 0\n144 -39 0 140 94 0\n145 -40 0 141 95 0\n146 -41 0 142 96 0\n147 -6 0 131 1 2 3 7 102 0\n148 -9 0 131 4 5 6 8 102 0\n149 -26 34 0 127 144 143 147 30 31 32 33 34 35 98 86 0\n150 -43 -56 0 77 78 114 0\n151 -35 34 43 0 127 61 62 63 98 0\n152 34 -56 0 127 150 151 114 65 66 67 98 0\n153 -56 0 152 64 68 114 0\n154 -35 0 153 115 0\n155 -36 0 153 116 0\n156 -44 0 155 97 0\n157 -26 -34 0 140 139 147 30 34 35 85 0\n158 23 24 -34 0 140 139 147 142 141 148 129 157 85 24 89 100 79 0\n159 -23 -34 0 142 141 148 157 16 28 89 0\n160 -34 0 142 141 148 157 159 158 20 29 89 0\n161 -26 0 160 149 0\n162 -24 43 0 160 127 21 22 23 98 0\n163 17 20 28 43 0 160 127 140 139 129 155 142 141 161 148 162 98 17 25 83 100 87 81 0\n164 -17 28 24 0 142 141 161 129 154 140 139 147 9 18 26 88 100 82 80 0\n165 -20 24 0 130 161 129 10 11 12 13 14 15 19 27 101 100 36 0\n166 17 43 0 160 127 146 145 156 148 161 129 162 165 163 98 92 17 25 90 100 81 0\n167 43 0 154 161 129 162 166 9 18 26 164 84 100 80 0\n168 23 24 0 148 167 161 145 146 129 147 143 144 86 24 100 91 79 0\n169 -23 0 146 145 161 167 148 16 28 91 0\n170 24 0 169 168 0\n171 -2 0 170 20 0\n172 -25 0 170 29 0\n173 0 171 172 148 167 161 145 146 91 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record019_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1f26aa687ab19362d876a3a4e4789e17a69a6479b15352d475a364d4749d17783b0e63a4d332cc73a2e2b86d1b26c5ba1e4751cc749ca715e0f43c8f6506c0f1929286a0e98619916258361382e07991924690e58519515254351342d0768360e4318d1324c3382c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "49a69269249a692692492492492492492492249249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 58), (facetIndex 64), (facetIndex 78), (facetIndex 90)]))
 (.leaf ([(facetIndex 46), (facetIndex 52), (facetIndex 53), (facetIndex 70), (facetIndex 82)])))
 (.branch 3
 (.leaf ([(facetIndex 59), (facetIndex 63), (facetIndex 65), (facetIndex 66)]))
 (.leaf ([(facetIndex 47), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72), (facetIndex 73), (facetIndex 74)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 79), (facetIndex 80), (facetIndex 81), (facetIndex 84), (facetIndex 85), (facetIndex 86)]))
 (.leaf ([(facetIndex 60), (facetIndex 76), (facetIndex 88), (facetIndex 91)])))
 (.branch 7
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51)]))
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 61), (facetIndex 62)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "a051240648050db05b6905fd43fe09db6676z21;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 71), (facetIndex 75)]))
 (.leaf ([(facetIndex 77), (facetIndex 83)])))
 (.branch 3
 (.leaf ([(facetIndex 87)]))
 (.leaf ([(facetIndex 89)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "c804004z26;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
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
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0016 : List Nat := [1]
def grouped3_0017 : List Nat := [2]
def grouped3_0018 : List Nat := [2, 3]
def grouped3_0019 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record003" 69

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record003" "{\"ridges\":[[15,131],[15,259],[21,145],[22,273],[25,25],[28,145],[33,146],[34,274],[40,146],[43,148],[45,259],[48,131],[51,259],[53,642],[56,25],[61,145],[61,146],[62,259],[65,131],[66,259],[67,25],[69,273],[72,49],[73,49],[74,49],[74,273],[75,708],[76,25],[77,25],[77,145],[81,274],[86,274],[89,146],[89,664]],\"owners\":[[65,131,[4,11,15,44,48,55,61],[16,50,59]],[62,259,[5,15,45,51,66],[12,49,56]],[72,49,[10,25,61,62],[20,60,73,74,76]],[73,49,[10,25,60,62,76],[20,61,72,74]],[74,49,[10,25,60,61,76],[20,62,72,73]],[22,273,[12,28,56,62],[69,74]],[69,273,[12,28,62],[22,56,74]],[74,273,[12,28,56],[22,62,69]],[34,274,[12,40,56,62],[81,86]],[81,274,[12,40,62],[34,56,86]],[86,274,[12,40,56],[34,62,81]],[53,642,[89],[16,59,63,65,66,83,87]],[43,148,[21,33,68,73,80,85],[]],[75,708,[87],[]],[89,664,[77],[]]],\"edges\":[[33,[12,22,28,34,40,43,56,62,69,74,81,86]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-16,-1],[-19,-2],[-19,-16],[-22,-1],[-22,-19],[-26,-3],[-26,-18],[-29,-26],[-30,-5],[-30,-26],[-31,-4],[-31,-20],[-31,-26],[-31,-30],[-33,-21],[-34,-19],[-34,-21],[-37,-26],[-39,-17],[-39,-23],[-39,-38],[-41,-30],[-48,-39],[-49,-30],[-51,-17],[-51,-23],[-51,-38],[-51,-48],[-52,-15],[-52,-25],[-52,-27],[-52,-28],[-52,-32],[-52,-36],[-52,-46],[-33,1,4,6,15,19,25,30],[-6,-19,-33],[-31,2,6,16,22,34],[-6,-16,-31],[-6,-22,-31],[-16,-31,-34],[-22,-31,-34],[-9,-26,-45],[-26,-35,-45],[-26,-44,-45],[-40,3,9,30,31],[-41,3,9,29,31,44],[-42,3,9,29,30,44],[-7,-30,-45],[-10,-30,-45],[-11,-30,-52],[-13,-30,-52],[-8,5,10,26,31],[-37,5,10,31],[-42,5,10,26],[-12,5,13,26,31],[-47,5,13,31],[-50,5,13,26],[-24,52],[-14,7,11,36,41,46,49],[-43,51],[-52,45],[-53,17,23,24,38,48],[-54,28,32,33,34],[-55,18,35,36,37,40,41,42],[-56,15,16,19,20,21,22],[-57,25,26,27,30,31],[-58,53],[-59,54],[-59,55],[-60,58],[-60,59],[-61,56],[-61,57],[-62,61],[-63,60],[-63,62],[63],[-64,39,43],[-65,51],[-66,52],[-67,64],[-68,65,66],[-69,67,68],[69],[5,8,10,12,13,14,26,31,37,42,47,50]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":45,\"b\":4},{\"tag\":\"incompatible\",\"a\":48,\"b\":5},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":51,\"b\":4},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":56,\"b\":10},{\"tag\":\"incompatible\",\"a\":56,\"b\":47},{\"tag\":\"incompatible\",\"a\":60,\"b\":56},{\"tag\":\"incompatible\",\"a\":61,\"b\":12},{\"tag\":\"incompatible\",\"a\":61,\"b\":56},{\"tag\":\"incompatible\",\"a\":62,\"b\":11},{\"tag\":\"incompatible\",\"a\":62,\"b\":49},{\"tag\":\"incompatible\",\"a\":62,\"b\":56},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":65,\"b\":50},{\"tag\":\"incompatible\",\"a\":66,\"b\":48},{\"tag\":\"incompatible\",\"a\":66,\"b\":50},{\"tag\":\"incompatible\",\"a\":69,\"b\":56},{\"tag\":\"incompatible\",\"a\":71,\"b\":46},{\"tag\":\"incompatible\",\"a\":71,\"b\":52},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":61},{\"tag\":\"incompatible\",\"a\":82,\"b\":71},{\"tag\":\"incompatible\",\"a\":85,\"b\":61},{\"tag\":\"incompatible\",\"a\":87,\"b\":46},{\"tag\":\"incompatible\",\"a\":87,\"b\":52},{\"tag\":\"incompatible\",\"a\":87,\"b\":70},{\"tag\":\"incompatible\",\"a\":87,\"b\":82},{\"tag\":\"incompatible\",\"a\":89,\"b\":44},{\"tag\":\"incompatible\",\"a\":89,\"b\":55},{\"tag\":\"incompatible\",\"a\":89,\"b\":57},{\"tag\":\"incompatible\",\"a\":89,\"b\":59},{\"tag\":\"incompatible\",\"a\":89,\"b\":63},{\"tag\":\"incompatible\",\"a\":89,\"b\":68},{\"tag\":\"incompatible\",\"a\":89,\"b\":80},{\"tag\":\"mate\",\"ridge\":131,\"a\":65,\"owners\":[4,11,15,44,48,55,61]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[15,48,65]},{\"tag\":\"mate\",\"ridge\":259,\"a\":62,\"owners\":[5,15,45,51,66]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[15,45,62]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[15,51,62]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[45,62,66]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[51,62,66]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[25,56,77]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[56,67,77]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[56,76,77]},{\"tag\":\"mate\",\"ridge\":49,\"a\":72,\"owners\":[10,25,61,62]},{\"tag\":\"mate\",\"ridge\":49,\"a\":73,\"owners\":[10,25,60,62,76]},{\"tag\":\"mate\",\"ridge\":49,\"a\":74,\"owners\":[10,25,60,61,76]},{\"tag\":\"three\",\"ridge\":145,\"vertices\":[21,61,77]},{\"tag\":\"three\",\"ridge\":145,\"vertices\":[28,61,77]},{\"tag\":\"three\",\"ridge\":146,\"vertices\":[33,61,89]},{\"tag\":\"three\",\"ridge\":146,\"vertices\":[40,61,89]},{\"tag\":\"mate\",\"ridge\":273,\"a\":22,\"owners\":[12,28,56,62]},{\"tag\":\"mate\",\"ridge\":273,\"a\":69,\"owners\":[12,28,62]},{\"tag\":\"mate\",\"ridge\":273,\"a\":74,\"owners\":[12,28,56]},{\"tag\":\"mate\",\"ridge\":274,\"a\":34,\"owners\":[12,40,56,62]},{\"tag\":\"mate\",\"ridge\":274,\"a\":81,\"owners\":[12,40,62]},{\"tag\":\"mate\",\"ridge\":274,\"a\":86,\"owners\":[12,40,56]},{\"tag\":\"mate\",\"ridge\":642,\"a\":53,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":148,\"a\":43,\"owners\":[21,33,68,73,80,85]},{\"tag\":\"mate\",\"ridge\":708,\"a\":75,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":664,\"a\":89,\"owners\":[77]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[46,52,53,70,82],\"full_literals\":[-53,17,23,24,38,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[59,63,65,66],\"full_literals\":[-54,28,32,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[47,67,68,69,72,73,74],\"full_literals\":[-55,18,35,36,37,40,41,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[44,45,48,49,50,51],\"full_literals\":[-56,15,16,19,20,21,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[55,56,57,61,62],\"full_literals\":[-57,25,26,27,30,31]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-60,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-63,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-63,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[71,75],\"full_literals\":[-64,39,43]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[87],\"full_literals\":[-65,51]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[89],\"full_literals\":[-66,52]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,64,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-69,67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[12,22,28,34,40,43,56,62,69,74,81,86]}]}"
  "87 60 0 78 76 0\n88 62 0 78 77 0\n89 58 0 87 71 0\n90 59 0 87 72 0\n91 61 0 88 75 0\n92 53 0 89 68 0\n93 54 0 90 69 0\n94 55 0 90 70 0\n95 56 0 91 73 0\n96 57 0 91 74 0\n97 -34 19 -31 15 0 95 12 17 42 41 66 0\n98 -1 21 19 20 15 0 95 1 4 66 0\n99 19 -31 30 -52 0 93 95 12 11 33 32 30 29 97 64 15 98 36 39 40 66 0\n100 30 26 -52 0 96 93 33 32 31 30 67 99 2 3 5 16 38 64 37 0\n101 26 -52 0 62 35 34 100 9 14 22 24 49 50 51 52 54 53 55 60 56 57 58 86 0\n102 -52 0 94 34 62 101 6 7 8 10 13 18 43 44 45 47 46 65 48 0\n103 -24 0 102 59 0\n104 -66 0 102 81 0\n105 -51 0 103 92 25 26 27 28 63 0\n106 -43 0 105 61 0\n107 -65 0 105 80 0\n108 -68 0 107 104 83 0\n109 67 0 108 85 84 0\n110 64 0 109 82 0\n111 39 0 110 106 79 0\n112 -17 0 111 19 0\n113 -23 0 111 20 0\n114 -38 0 111 21 0\n115 -48 0 111 23 0\n116 0 114 115 92 103 113 112 63 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "19c1f2ca668ba1eb8699a96659361da8e63a4e4789e17ac9664b91e78599695655351d68d6364d4749d17783b0e63a4d332cc73a2d8b92ccb2ad1b16f07a1d8751e2749e1725c5783d0f23c6c0f1921a89a0ea46199160d84e0b81e644692643991465454351342d0768360e4318d1324c3322c4b0ac1b81d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "34d24d34936924d24d3493692492492492492492492491249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 44), (facetIndex 48), (facetIndex 49), (facetIndex 64), (facetIndex 77), (facetIndex 93)]))
 (.leaf ([(facetIndex 43), (facetIndex 57), (facetIndex 59), (facetIndex 70), (facetIndex 86)])))
 (.branch 3
 (.leaf ([(facetIndex 53), (facetIndex 60), (facetIndex 67), (facetIndex 73), (facetIndex 79), (facetIndex 83), (facetIndex 89), (facetIndex 95), (facetIndex 99)]))
 (.leaf ([(facetIndex 54), (facetIndex 55), (facetIndex 61), (facetIndex 80), (facetIndex 96)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 62), (facetIndex 74), (facetIndex 90)]))
 (.leaf ([(facetIndex 51), (facetIndex 52), (facetIndex 65), (facetIndex 66)])))
 (.branch 7
 (.leaf ([(facetIndex 41), (facetIndex 50), (facetIndex 68), (facetIndex 75), (facetIndex 84), (facetIndex 91)]))
 (.branch 8
 (.leaf ([(facetIndex 42), (facetIndex 58), (facetIndex 69), (facetIndex 81), (facetIndex 85), (facetIndex 97)]))
 (.leaf ([(facetIndex 56), (facetIndex 63)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "20732000642001762073200064200176255084321718332556004440176z29;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 72), (facetIndex 82)]))
 (.leaf ([(facetIndex 88), (facetIndex 98)])))
 (.branch 3
 (.leaf ([(facetIndex 71), (facetIndex 76), (facetIndex 78)]))
 (.branch 4
 (.leaf ([(facetIndex 87), (facetIndex 92), (facetIndex 94)]))
 (.leaf ([(facetIndex 100)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "40400c30016000000820004z35;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
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
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [2]
def grouped3_0020 : List Nat := [2, 3, 4]
def grouped3_0021 : List Nat := [3]
def grouped3_0022 : List Nat := [3, 4]
def grouped3_0023 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record004" 62

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record004" "{\"ridges\":[[16,642],[27,385],[38,386],[51,642],[59,642],[63,642],[65,642],[66,642],[72,652],[75,385],[76,660],[78,900],[82,712],[91,386],[92,660],[98,712]],\"owners\":[[27,385,[15,50,58,66,71,78],[75,81]],[75,385,[15,58,66],[27,50,71,78,81]],[38,386,[15,50,58,66,87,94],[91,97]],[91,386,[15,58,66],[38,50,87,94,97]],[16,642,[88,92,94,98],[51,59,63,65,66]],[51,642,[98],[16,59,63,65,66,88,92,94]],[59,642,[92,94],[16,51,63,65,66,88,98]],[63,642,[88,94,98],[16,51,59,65,66,92]],[65,642,[88,92,94],[16,51,59,63,66,98]],[66,642,[88,92,98],[16,51,59,63,65,94]],[72,652,[88],[]],[76,660,[92],[]],[92,660,[76],[]],[78,900,[94],[]],[82,712,[98],[]],[98,712,[82],[]]],\"edges\":[[42,[15,27,38,50,58,66,71,75,78,81,87,91,94,97,100]],[43,[16,51,59,63,65,66,72,76,78,82,88,92,94,98]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-6],[-13,-11],[-15,-1],[-15,-8],[-15,-13],[-16,-11],[-16,-15],[-17,-15],[-24,-19],[-26,-15],[-26,-24],[-32,-5],[-32,-7],[-32,-8],[-32,-12],[-32,-14],[-32,-18],[-32,-20],[-32,-23],[-32,-28],[-32,-30],[-33,-32],[-34,-5],[-34,-8],[-34,-18],[-34,-23],[-34,-28],[-34,-29],[-34,-33],[-35,-5],[-35,-8],[-35,-10],[-35,-17],[-35,-18],[-35,-23],[-35,-28],[-35,-33],[-36,-15],[-36,-34],[-37,-7],[-37,-11],[-37,-12],[-37,-14],[-37,-20],[-37,-30],[-3,1,8,13,17,21,25],[-23,1,13,17],[-4,1,8,13,17,31,35],[-33,1,13,17],[-2,32,34,35,37],[-9,37],[-14,34,35],[-15,32,35,37],[-16,32,34,35],[-17,32,34,37],[-22,32],[-24,34],[-34,24],[-25,35],[-27,37],[-37,27],[-39,7,12,14,20,30],[-40,9,10,16,17],[-41,5,8,18,23,28,33],[-42,6,13,19,26,29,36],[-43,11,15],[-44,39],[-45,44],[-46,40],[-47,42],[-47,43],[-48,41,47],[-49,41],[-49,47],[-50,46,49],[-50,48],[-51,49],[-52,45,51],[-52,50],[52],[-53,22,27],[-22,53],[-27,53],[-54,32,37],[-32,54],[-37,54],[-21,55],[-25,55],[-31,56],[-35,56],[-38,57],[-58,53,54],[-54,58],[-53,58],[-53,-54,59],[-57,60],[-56,60],[-60,61],[-55,61],[-59,-61,62],[-62],[1,3,4,8,13,17,21,23,25,26,31,33,35,36,38],[2,9,14,15,16,17,22,24,25,27,32,34,35,37]],\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":56,\"b\":42},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":63,\"b\":15},{\"tag\":\"incompatible\",\"a\":63,\"b\":50},{\"tag\":\"incompatible\",\"a\":63,\"b\":58},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":65,\"b\":63},{\"tag\":\"incompatible\",\"a\":66,\"b\":63},{\"tag\":\"incompatible\",\"a\":76,\"b\":69},{\"tag\":\"incompatible\",\"a\":81,\"b\":63},{\"tag\":\"incompatible\",\"a\":81,\"b\":76},{\"tag\":\"incompatible\",\"a\":88,\"b\":41},{\"tag\":\"incompatible\",\"a\":88,\"b\":43},{\"tag\":\"incompatible\",\"a\":88,\"b\":50},{\"tag\":\"incompatible\",\"a\":88,\"b\":57},{\"tag\":\"incompatible\",\"a\":88,\"b\":59},{\"tag\":\"incompatible\",\"a\":88,\"b\":68},{\"tag\":\"incompatible\",\"a\":88,\"b\":70},{\"tag\":\"incompatible\",\"a\":88,\"b\":75},{\"tag\":\"incompatible\",\"a\":88,\"b\":84},{\"tag\":\"incompatible\",\"a\":88,\"b\":86},{\"tag\":\"incompatible\",\"a\":91,\"b\":88},{\"tag\":\"incompatible\",\"a\":92,\"b\":41},{\"tag\":\"incompatible\",\"a\":92,\"b\":50},{\"tag\":\"incompatible\",\"a\":92,\"b\":68},{\"tag\":\"incompatible\",\"a\":92,\"b\":75},{\"tag\":\"incompatible\",\"a\":92,\"b\":84},{\"tag\":\"incompatible\",\"a\":92,\"b\":85},{\"tag\":\"incompatible\",\"a\":92,\"b\":91},{\"tag\":\"incompatible\",\"a\":94,\"b\":41},{\"tag\":\"incompatible\",\"a\":94,\"b\":50},{\"tag\":\"incompatible\",\"a\":94,\"b\":52},{\"tag\":\"incompatible\",\"a\":94,\"b\":66},{\"tag\":\"incompatible\",\"a\":94,\"b\":68},{\"tag\":\"incompatible\",\"a\":94,\"b\":75},{\"tag\":\"incompatible\",\"a\":94,\"b\":84},{\"tag\":\"incompatible\",\"a\":94,\"b\":91},{\"tag\":\"incompatible\",\"a\":97,\"b\":63},{\"tag\":\"incompatible\",\"a\":97,\"b\":92},{\"tag\":\"incompatible\",\"a\":98,\"b\":43},{\"tag\":\"incompatible\",\"a\":98,\"b\":56},{\"tag\":\"incompatible\",\"a\":98,\"b\":57},{\"tag\":\"incompatible\",\"a\":98,\"b\":59},{\"tag\":\"incompatible\",\"a\":98,\"b\":70},{\"tag\":\"incompatible\",\"a\":98,\"b\":86},{\"tag\":\"mate\",\"ridge\":385,\"a\":27,\"owners\":[15,50,58,66,71,78]},{\"tag\":\"mate\",\"ridge\":385,\"a\":75,\"owners\":[15,58,66]},{\"tag\":\"mate\",\"ridge\":386,\"a\":38,\"owners\":[15,50,58,66,87,94]},{\"tag\":\"mate\",\"ridge\":386,\"a\":91,\"owners\":[15,58,66]},{\"tag\":\"mate\",\"ridge\":642,\"a\":16,\"owners\":[88,92,94,98]},{\"tag\":\"mate\",\"ridge\":642,\"a\":51,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":642,\"a\":59,\"owners\":[92,94]},{\"tag\":\"mate\",\"ridge\":642,\"a\":63,\"owners\":[88,94,98]},{\"tag\":\"mate\",\"ridge\":642,\"a\":65,\"owners\":[88,92,94]},{\"tag\":\"mate\",\"ridge\":642,\"a\":66,\"owners\":[88,92,98]},{\"tag\":\"mate\",\"ridge\":652,\"a\":72,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":660,\"a\":76,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":660,\"a\":92,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":900,\"a\":78,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":712,\"a\":82,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":712,\"a\":98,\"owners\":[82]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[43,57,59,70,86],\"full_literals\":[-39,7,12,14,20,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[51,52,65,66],\"full_literals\":[-40,9,10,16,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[41,50,68,75,84,91],\"full_literals\":[-41,5,8,18,23,28,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[42,58,69,81,85,97],\"full_literals\":[-42,6,13,19,26,29,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[56,63],\"full_literals\":[-43,11,15]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-45,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,41,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-49,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-50,46,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-51,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-52,45,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-52,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[72,82],\"full_literals\":[-53,22,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":72,\"full_literals\":[-22,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":82,\"full_literals\":[-27,53]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[88,98],\"full_literals\":[-54,32,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":88,\"full_literals\":[-32,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":98,\"full_literals\":[-37,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":71,\"full_literals\":[-21,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":78,\"full_literals\":[-25,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":87,\"full_literals\":[-31,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":94,\"full_literals\":[-35,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":100,\"full_literals\":[-38,57]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,53,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-54,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[15,27,38,50,58,66,71,75,78,81,87,91,94,97,100]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[16,51,59,63,65,66,72,76,78,82,88,92,94,98]}]}"
  "104 50 0 80 79 0\n105 48 0 104 76 0\n106 34 35 58 0 93 86 85 53 59 51 94 83 82 52 57 50 54 55 103 0\n107 35 58 0 105 93 86 85 53 106 23 24 25 26 27 28 29 39 58 64 9 11 72 70 71 66 1 2 65 0\n108 58 0 105 104 93 86 51 107 30 31 32 33 34 35 36 37 64 72 73 71 75 69 63 6 7 66 0\n109 32 37 0 108 60 56 84 81 92 0\n110 -32 0 80 12 13 14 15 16 17 18 19 20 21 22 62 64 67 73 68 77 78 0\n111 37 0 110 109 0\n112 -7 0 111 40 0\n113 -11 0 111 41 0\n114 -12 0 111 42 0\n115 -14 0 111 43 0\n116 -20 0 111 44 0\n117 -30 0 111 45 0\n118 27 0 111 61 0\n119 54 0 111 86 0\n120 -39 0 117 112 115 114 116 62 0\n121 53 0 118 83 0\n122 -44 0 120 67 0\n123 59 0 121 119 95 0\n124 -45 0 122 68 0\n125 -61 0 123 101 100 0\n126 51 0 124 80 78 0\n127 -60 0 125 98 0\n128 -55 0 125 99 0\n129 49 0 126 77 0\n130 -57 0 127 96 0\n131 -56 0 127 97 0\n132 -21 0 128 87 0\n133 -25 0 128 88 0\n134 47 0 129 74 0\n135 -38 0 130 91 0\n136 -31 0 131 89 0\n137 -35 0 131 90 0\n138 43 0 134 71 0\n139 15 0 138 113 66 0\n140 -1 0 139 3 0\n141 -8 0 139 4 0\n142 -13 0 139 5 0\n143 -17 0 139 8 0\n144 -26 0 139 10 0\n145 -36 0 139 38 0\n146 -23 0 140 142 143 47 0\n147 -33 0 140 142 143 49 0\n148 -3 0 140 141 142 143 132 133 46 0\n149 -4 0 140 141 142 143 136 137 48 0\n150 0 149 148 140 141 142 143 132 146 133 144 136 147 137 145 135 102 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e326ca719c9707c668ba1e996a398e9392e1b91e2785eb47899a699666592e479e1665a55959570da358d9362d4b46d8751d2745db0d9334cb3a2e4b4acab1ad1b16e8761e4751d2745c9783c8f13c740f0726289a0e866158364382e07871a25892643991465154358350d0b41d60c6324c530cd0b22c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6da49369a49269a4d269b4924924926924d2493492492449249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 78), (facetIndex 81)]))
 (.branch 2
 (.leaf ([(facetIndex 89), (facetIndex 97), (facetIndex 100)]))
 (.leaf ([(facetIndex 59), (facetIndex 83)]))))
 (.branch 4
 (.leaf ([(facetIndex 48), (facetIndex 72), (facetIndex 73), (facetIndex 75)]))
 (.branch 5
 (.leaf ([(facetIndex 91), (facetIndex 92), (facetIndex 99), (facetIndex 101)]))
 (.leaf ([(facetIndex 98)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2194800480800040000061b000000000400000003z24;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4, 5]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record005" 37

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record005" "{\"ridges\":[[21,577],[25,641],[46,577],[48,646],[55,641],[59,706],[67,580],[69,648],[71,577],[72,404],[73,660],[74,577],[75,900],[80,641],[82,641],[83,720],[91,646],[99,660],[101,900]],\"owners\":[[21,577,[54,59,78,81,83],[46,67,71,74]],[46,577,[78,81,83],[21,54,59,67,71,74]],[71,577,[54,59,81],[21,46,67,74,78,83]],[74,577,[54,59,78,83],[21,46,67,71,81]],[67,580,[],[21,46,71,74,89,97,100]],[25,641,[48,59,73,75,83],[55,69,80,82]],[55,641,[73,75,83],[25,48,59,69,80,82]],[80,641,[48,59,75],[25,55,69,73,82,83]],[82,641,[48,59,73,83],[25,55,69,75,80]],[69,648,[],[25,55,80,82,91,99,101]],[48,646,[91],[]],[91,646,[48],[]],[59,706,[],[]],[72,404,[92,98],[]],[73,660,[99],[]],[99,660,[73],[]],[75,900,[101],[]],[101,900,[75],[]],[83,720,[],[]]],\"edges\":[[41,[21,46,54,59,67,71,74,78,81,83,89,97,100]],[43,[25,48,55,59,69,73,75,80,82,83,91,99,101]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,5,7,15,17,19],[-3,15,17,19],[-10,5,7,17],[-13,5,7,15,19],[-8],[-2,4,7,12,14,19],[-6,12,14,19],[-16,4,7,14],[-18,4,7,12,19],[-9],[-4,21],[-21,4],[-7],[-11,22,24],[-12,25],[-25,12],[-14,27],[-27,14],[-19],[-5,28],[-15,28],[-17,28],[-20,29],[-23,29],[-26,29],[-30,4,11,12,14],[-4,30],[-12,30],[-14,30],[-21,31],[-22,31],[-25,31],[-27,31],[-24,32],[-29,33],[-33,34],[-28,34],[-32,35],[-31,35],[-30,-35,36],[-34,-36,37],[-37],[1,3,5,7,8,10,13,15,17,19,20,23,26],[2,4,6,7,9,12,14,16,18,19,21,25,27]],\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":577,\"a\":21,\"owners\":[54,59,78,81,83]},{\"tag\":\"mate\",\"ridge\":577,\"a\":46,\"owners\":[78,81,83]},{\"tag\":\"mate\",\"ridge\":577,\"a\":71,\"owners\":[54,59,81]},{\"tag\":\"mate\",\"ridge\":577,\"a\":74,\"owners\":[54,59,78,83]},{\"tag\":\"mate\",\"ridge\":580,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":641,\"a\":25,\"owners\":[48,59,73,75,83]},{\"tag\":\"mate\",\"ridge\":641,\"a\":55,\"owners\":[73,75,83]},{\"tag\":\"mate\",\"ridge\":641,\"a\":80,\"owners\":[48,59,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":82,\"owners\":[48,59,73,83]},{\"tag\":\"mate\",\"ridge\":648,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":646,\"a\":48,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":646,\"a\":91,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":706,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":404,\"a\":72,\"owners\":[92,98]},{\"tag\":\"mate\",\"ridge\":660,\"a\":73,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":660,\"a\":99,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":900,\"a\":75,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":900,\"a\":101,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":720,\"a\":83,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":54,\"full_literals\":[-5,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":78,\"full_literals\":[-15,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":81,\"full_literals\":[-17,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":89,\"full_literals\":[-20,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":97,\"full_literals\":[-23,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":100,\"full_literals\":[-26,29]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[48,72,73,75],\"full_literals\":[-30,4,11,12,14]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":48,\"full_literals\":[-4,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-12,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":75,\"full_literals\":[-14,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":91,\"full_literals\":[-21,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":92,\"full_literals\":[-22,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":99,\"full_literals\":[-25,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":101,\"full_literals\":[-27,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":98,\"full_literals\":[-24,32]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-30,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-34,-36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[21,46,54,59,67,71,74,78,81,83,89,97,100]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[25,48,55,59,69,73,75,80,82,83,91,99,101]}]}"
  "45 1 3 5 10 13 15 17 20 23 26 0 13 5 19 43 0\n46 2 4 6 12 14 16 18 21 25 27 0 13 10 19 44 0\n47 34 0 19 13 36 37 35 20 21 22 23 24 25 2 1 4 3 45 0\n48 -36 0 47 42 41 0\n49 30 0 19 13 27 28 29 12 7 16 6 9 18 8 46 0\n50 -35 0 49 48 40 0\n51 -32 0 50 38 0\n52 -31 0 50 39 0\n53 -24 0 51 34 0\n54 -21 0 52 30 0\n55 -22 0 52 31 0\n56 -25 0 52 32 0\n57 -27 0 52 33 0\n58 -4 0 54 11 0\n59 -11 0 55 53 14 0\n60 -12 0 56 15 0\n61 -14 0 57 17 0\n62 0 59 58 49 60 61 26 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5d1cc5713cb49caaa9aaa68da8e9c659a361d98e538ce4b85ee86d15c5c9aa5a9a6559366394e5c5595558d5351d58d534cd4745db0dc3a8da358e9394cd31ce8b62d4b32e2b4acab86c9b16d8751cc789d2719e1743c8f13d2c0f2320e8560d82e079c18c5894a43951525154354342d0768330e2384c530cc8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6da6db6d36936d26da69b6924924934924da4924d24924d2492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 76), (facetIndex 81)]))
 (.leaf ([(facetIndex 75), (facetIndex 77), (facetIndex 82)])))
 (.branch 3
 (.leaf ([(facetIndex 58), (facetIndex 79), (facetIndex 83)]))
 (.branch 4
 (.leaf ([(facetIndex 94), (facetIndex 95), (facetIndex 99)]))
 (.leaf ([(facetIndex 101), (facetIndex 103)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 42), (facetIndex 50), (facetIndex 57), (facetIndex 96)]))
 (.branch 7
 (.leaf ([(facetIndex 64), (facetIndex 87), (facetIndex 88)]))
 (.leaf ([(facetIndex 86), (facetIndex 92), (facetIndex 98)]))))
 (.branch 9
 (.leaf ([(facetIndex 97)]))
 (.branch 10
 (.leaf ([(facetIndex 91)]))
 (.leaf ([(facetIndex 102)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "4a403785330790066700210020101000000000060000025000000500000005z2a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3, 4]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6, 7]
def grouped3_0012 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0013 : List Nat := [6]
def grouped3_0014 : List Nat := [6, 7]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [8, 9, 10]
def grouped3_0018 : List Nat := [9, 10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record011" 49

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record011" "{\"ridges\":[[12,641],[22,392],[24,448],[51,392],[52,641],[56,641],[56,642],[58,418],[59,641],[60,448],[61,641],[66,392],[72,448],[75,216],[77,664],[78,392],[79,680],[80,448],[82,720],[83,928],[95,664],[97,680],[99,720],[102,204]],\"owners\":[[12,641,[77,79,82,83],[52,56,59,61]],[52,641,[82,83],[12,56,59,61,77,79]],[56,641,[79,83],[12,52,59,61,77,82]],[59,641,[77,82],[12,52,56,61,79,83]],[61,641,[77,79,83],[12,52,56,59,82]],[56,642,[97],[12,52,59,61,95,99]],[22,392,[88,96,98,102],[51,66,78,80]],[51,392,[102],[22,66,78,80,88,96,98]],[66,392,[96,98],[22,51,78,80,88,102]],[78,392,[88,98,102],[22,51,66,80,96]],[24,448,[92,98,102],[60,72,80]],[60,448,[102],[24,72,80,92,98]],[72,448,[98],[24,60,80,92,102]],[80,448,[92],[24,60,72,98,102]],[58,418,[96],[]],[102,204,[64,86],[]],[75,216,[94],[]],[77,664,[95],[]],[95,664,[77],[]],[79,680,[97],[]],[97,680,[79],[]],[82,720,[99],[]],[99,720,[82],[]],[83,928,[],[]]],\"edges\":[[42,[22,24,42,51,58,60,66,72,78,80,83,88,92,96,98,102]],[43,[12,52,56,59,61,77,79,82,83,95,97,99]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,16,18,20,21],[-6,20,21],[-7,18,21],[-9,16,20],[-11,16,18,21],[-7,28],[-2,23,27,29,31],[-5,31],[-13,27,29],[-17,23,29,31],[-3,24,29,31],[-10,31],[-14,29],[-19,24],[-8,27],[-31,12,22],[-15,25],[-16,26],[-26,16],[-18,28],[-28,18],[-20,30],[-30,20],[-21],[-32,15,16,20],[-16,32],[-20,32],[-18,33],[-25,34],[-26,34],[-30,34],[-4,35],[-27,35],[-12,36],[-23,36],[-22,37],[-24,37],[-29,37],[-28,38],[-32,39],[-34,40],[-40,41],[-33,41],[-41,42],[-39,42],[-39,-41,43],[-37,44],[-36,44],[-44,45],[-35,45],[-38,46],[-45,47],[-45,-46,48],[-42,-48,49],[-43,-47,49],[-49],[2,3,4,5,8,10,13,14,17,19,21,23,24,27,29,31],[1,6,7,9,11,16,18,20,21,26,28,30]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":641,\"a\":12,\"owners\":[77,79,82,83]},{\"tag\":\"mate\",\"ridge\":641,\"a\":52,\"owners\":[82,83]},{\"tag\":\"mate\",\"ridge\":641,\"a\":56,\"owners\":[79,83]},{\"tag\":\"mate\",\"ridge\":641,\"a\":59,\"owners\":[77,82]},{\"tag\":\"mate\",\"ridge\":641,\"a\":61,\"owners\":[77,79,83]},{\"tag\":\"mate\",\"ridge\":642,\"a\":56,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":392,\"a\":22,\"owners\":[88,96,98,102]},{\"tag\":\"mate\",\"ridge\":392,\"a\":51,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":392,\"a\":66,\"owners\":[96,98]},{\"tag\":\"mate\",\"ridge\":392,\"a\":78,\"owners\":[88,98,102]},{\"tag\":\"mate\",\"ridge\":448,\"a\":24,\"owners\":[92,98,102]},{\"tag\":\"mate\",\"ridge\":448,\"a\":60,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":448,\"a\":72,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":448,\"a\":80,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":418,\"a\":58,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":204,\"a\":102,\"owners\":[64,86]},{\"tag\":\"mate\",\"ridge\":216,\"a\":75,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":664,\"a\":77,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":664,\"a\":95,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":680,\"a\":79,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":680,\"a\":97,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":720,\"a\":82,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":720,\"a\":99,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":928,\"a\":83,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[75,77,82],\"full_literals\":[-32,15,16,20]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-16,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-20,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":79,\"full_literals\":[-18,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":94,\"full_literals\":[-25,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":95,\"full_literals\":[-26,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":99,\"full_literals\":[-30,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":42,\"full_literals\":[-4,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":96,\"full_literals\":[-27,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":64,\"full_literals\":[-12,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-23,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-22,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":92,\"full_literals\":[-24,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":98,\"full_literals\":[-29,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":97,\"full_literals\":[-28,38]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-46,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-42,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-47,49],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[22,24,42,51,58,60,66,72,78,80,83,88,92,96,98,102]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[12,52,56,59,61,77,79,82,83,95,97,99]}]}"
  "59 2 3 4 5 8 10 13 14 17 19 23 24 27 29 31 0 24 57 0\n60 1 6 7 9 11 16 18 20 26 28 30 0 24 58 0\n61 42 0 24 44 45 42 43 40 41 28 26 27 30 31 3 21 1 4 5 2 60 0\n62 -48 0 61 56 54 0\n63 45 0 49 50 47 48 32 33 36 37 38 34 35 15 16 14 13 9 8 12 7 10 11 59 0\n64 47 0 63 52 0\n65 -46 0 63 62 53 0\n66 -43 0 64 56 55 0\n67 -38 0 65 51 0\n68 -28 0 67 39 0\n69 -7 0 68 6 0\n70 -18 0 68 20 0\n71 16 20 0 69 70 68 24 1 4 5 19 2 23 60 0\n72 32 0 26 27 71 0\n73 39 0 72 40 0\n74 -41 0 73 66 46 0\n75 -40 0 74 42 0\n76 -34 0 75 41 0\n77 -25 0 76 29 0\n78 -26 0 76 30 0\n79 -30 0 76 31 0\n80 -15 0 77 17 0\n81 -16 0 78 18 0\n82 -20 0 79 22 0\n83 0 80 81 72 82 25 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00116.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00116.record011
