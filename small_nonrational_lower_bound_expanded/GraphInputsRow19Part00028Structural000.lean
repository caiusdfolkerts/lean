module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00028Frames
public import GraphInputsRow19Part00028Leaves
public import GraphInputsRow19Part00028Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00028.record045
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "d8ad29a96a968da8e9c68d94e3392e2783ed86d19a569964d98e5c58d54d3352d2743dd0ec370f2398d63a4e5334e3392d4b32e2b4ac6b86c9b16c3b61d4731e2729e1745c3743c8f13d262582e079252542d0764350cc388d2384c9312c2b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6926db6db6da492492492492492492492492449249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 24), (facetIndex 26), (facetIndex 27), (facetIndex 28), (facetIndex 36), (facetIndex 55), (facetIndex 69)]))
 (.branch 2
 (.leaf ([(facetIndex 25), (facetIndex 29), (facetIndex 30), (facetIndex 39), (facetIndex 56), (facetIndex 70)]))
 (.leaf ([(facetIndex 34), (facetIndex 44), (facetIndex 54), (facetIndex 68)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 23), (facetIndex 31), (facetIndex 32), (facetIndex 33), (facetIndex 51)]))
 (.leaf ([(facetIndex 35), (facetIndex 37), (facetIndex 45), (facetIndex 46), (facetIndex 47)])))
 (.branch 6
 (.leaf ([(facetIndex 38), (facetIndex 40), (facetIndex 48), (facetIndex 49), (facetIndex 50)]))
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 52), (facetIndex 53)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "420000000010b676d922db536089b6480086z11;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00028.record045" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00028.record045" 56

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00028.record045" "{\"ridges\":[[12,193],[31,193],[37,529],[41,193],[44,529],[45,193],[50,545],[51,193],[52,193],[57,193],[57,204],[59,529],[66,529],[66,720],[71,204],[74,452],[76,216],[80,720]],\"owners\":[[44,529,[63,66],[9,28,37,46,47,59,61]],[50,545,[59,61,65],[11,30,40,44,49,67]],[12,193,[57,60,62,66],[31,41,45,51,52]],[31,193,[62,66],[12,41,45,51,52,57,60]],[41,193,[60,66],[12,31,45,51,52,57,62]],[45,193,[57,60],[12,31,41,51,52,62,66]],[51,193,[57,62,66],[12,31,41,45,52,60]],[52,193,[57,60,62],[12,31,41,45,51,66]],[57,193,[12,45,51,52,66],[31,41,60,62]],[57,204,[71],[]],[71,204,[57],[]],[74,452,[60],[]],[76,216,[62],[]],[66,720,[80],[]],[80,720,[66],[]]],\"edges\":[[39,[12,31,41,45,51,52,57,60,62,66,71,74,76,80]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00028.record045" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00028.record045\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-4],[-9,-5],[-9,-6],[-10,-2],[-13,-10],[-14,-13],[-15,-13],[-17,-1],[-17,-7],[-17,-8],[-18,-1],[-18,-7],[-18,-8],[-18,-13],[-20,-9],[-23,-16],[-23,-17],[-24,-13],[-26,-17],[-26,-18],[-26,-20],[-27,-7],[-27,-8],[-27,-11],[-27,-19],[-27,-21],[-27,-22],[-27,-26],[-28,-1],[-28,-7],[-28,-8],[-28,-23],[-28,-26],[-29,-2],[-31,-2],[-31,-8],[-31,-29],[-33,-2],[-33,-8],[-33,-9],[-33,-26],[-34,-13],[-35,-3],[-35,-12],[-35,-16],[-35,-30],[-36,-35],[-37,-13],[-39,-2],[-40,-35],[-41,-39],[-44,-11],[-44,-20],[-44,-21],[-44,-22],[-44,-27],[-19,36,38],[-13,-32,-38],[-25,32,34,37],[-1,31,33,35,38],[-7,35,38],[-16,33,38],[-20,31,33],[-26,31,35,38],[-27,31,33,35],[-31,1,20,26,27,38],[-31,41],[-41,31],[-42,33],[-43,35],[-38,44],[-44,38],[-45,3,4,5,6,12,30,40],[-46,10,19,29,39],[-47,2,7,8,9,26],[-48,11,13,20,21,22],[-49,14,15,23,24,25],[-50,16,17,18,27,28],[-51,46],[-52,45],[-52,51],[-53,47],[-53,48],[-54,49],[-54,50],[-55,53],[-55,54],[-56,52],[-56,55],[56],[1,7,16,20,26,27,31,33,35,38,41,42,43,44]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":33,\"b\":26},{\"tag\":\"incompatible\",\"a\":33,\"b\":27},{\"tag\":\"incompatible\",\"a\":33,\"b\":28},{\"tag\":\"incompatible\",\"a\":34,\"b\":23},{\"tag\":\"incompatible\",\"a\":37,\"b\":34},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":12},{\"tag\":\"incompatible\",\"a\":42,\"b\":31},{\"tag\":\"incompatible\",\"a\":42,\"b\":32},{\"tag\":\"incompatible\",\"a\":43,\"b\":12},{\"tag\":\"incompatible\",\"a\":43,\"b\":31},{\"tag\":\"incompatible\",\"a\":43,\"b\":32},{\"tag\":\"incompatible\",\"a\":43,\"b\":37},{\"tag\":\"incompatible\",\"a\":45,\"b\":33},{\"tag\":\"incompatible\",\"a\":48,\"b\":41},{\"tag\":\"incompatible\",\"a\":48,\"b\":42},{\"tag\":\"incompatible\",\"a\":49,\"b\":37},{\"tag\":\"incompatible\",\"a\":51,\"b\":42},{\"tag\":\"incompatible\",\"a\":51,\"b\":43},{\"tag\":\"incompatible\",\"a\":51,\"b\":45},{\"tag\":\"incompatible\",\"a\":52,\"b\":31},{\"tag\":\"incompatible\",\"a\":52,\"b\":32},{\"tag\":\"incompatible\",\"a\":52,\"b\":35},{\"tag\":\"incompatible\",\"a\":52,\"b\":44},{\"tag\":\"incompatible\",\"a\":52,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":47},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":12},{\"tag\":\"incompatible\",\"a\":53,\"b\":31},{\"tag\":\"incompatible\",\"a\":53,\"b\":32},{\"tag\":\"incompatible\",\"a\":53,\"b\":48},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":23},{\"tag\":\"incompatible\",\"a\":57,\"b\":23},{\"tag\":\"incompatible\",\"a\":57,\"b\":32},{\"tag\":\"incompatible\",\"a\":57,\"b\":54},{\"tag\":\"incompatible\",\"a\":60,\"b\":23},{\"tag\":\"incompatible\",\"a\":60,\"b\":32},{\"tag\":\"incompatible\",\"a\":60,\"b\":33},{\"tag\":\"incompatible\",\"a\":60,\"b\":51},{\"tag\":\"incompatible\",\"a\":61,\"b\":37},{\"tag\":\"incompatible\",\"a\":62,\"b\":24},{\"tag\":\"incompatible\",\"a\":62,\"b\":36},{\"tag\":\"incompatible\",\"a\":62,\"b\":41},{\"tag\":\"incompatible\",\"a\":62,\"b\":55},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":37},{\"tag\":\"incompatible\",\"a\":68,\"b\":23},{\"tag\":\"incompatible\",\"a\":69,\"b\":62},{\"tag\":\"incompatible\",\"a\":71,\"b\":68},{\"tag\":\"incompatible\",\"a\":80,\"b\":35},{\"tag\":\"incompatible\",\"a\":80,\"b\":45},{\"tag\":\"incompatible\",\"a\":80,\"b\":46},{\"tag\":\"incompatible\",\"a\":80,\"b\":47},{\"tag\":\"incompatible\",\"a\":80,\"b\":52},{\"tag\":\"mate\",\"ridge\":529,\"a\":44,\"owners\":[63,66]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[37,59,66]},{\"tag\":\"mate\",\"ridge\":545,\"a\":50,\"owners\":[59,61,65]},{\"tag\":\"mate\",\"ridge\":193,\"a\":12,\"owners\":[57,60,62,66]},{\"tag\":\"mate\",\"ridge\":193,\"a\":31,\"owners\":[62,66]},{\"tag\":\"mate\",\"ridge\":193,\"a\":41,\"owners\":[60,66]},{\"tag\":\"mate\",\"ridge\":193,\"a\":45,\"owners\":[57,60]},{\"tag\":\"mate\",\"ridge\":193,\"a\":51,\"owners\":[57,62,66]},{\"tag\":\"mate\",\"ridge\":193,\"a\":52,\"owners\":[57,60,62]},{\"tag\":\"mate\",\"ridge\":193,\"a\":57,\"owners\":[12,45,51,52,66]},{\"tag\":\"mate\",\"ridge\":204,\"a\":57,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":204,\"a\":71,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":452,\"a\":74,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":216,\"a\":76,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":720,\"a\":66,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":720,\"a\":80,\"owners\":[66]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[24,26,27,28,36,55,69],\"full_literals\":[-45,3,4,5,6,12,30,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[34,44,54,68],\"full_literals\":[-46,10,19,29,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[23,31,32,33,51],\"full_literals\":[-47,2,7,8,9,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[35,37,45,46,47],\"full_literals\":[-48,11,13,20,21,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[38,40,48,49,50],\"full_literals\":[-49,14,15,23,24,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[41,42,43,52,53],\"full_literals\":[-50,16,17,18,27,28]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-52,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-55,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-56,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-56,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[12,31,41,45,51,52,57,60,62,66,71,74,76,80]}]}"
  "92 52 0 90 88 0\n93 55 0 90 89 0\n94 45 0 92 80 0\n95 51 0 92 81 0\n96 53 0 93 86 0\n97 54 0 93 87 0\n98 46 0 95 79 0\n99 47 0 96 82 0\n100 48 0 96 83 0\n101 49 0 97 84 0\n102 50 0 97 85 0\n103 31 33 35 44 0 71 62 69 70 61 68 64 63 60 65 91 0\n104 -1 27 16 0 102 8 11 29 78 0\n105 27 20 -31 16 38 0 102 104 66 19 20 33 78 0\n106 20 -31 16 38 0 98 100 67 51 37 105 24 25 26 27 74 76 5 0\n107 33 35 44 0 99 71 61 62 103 35 36 106 15 21 75 0\n108 35 44 0 99 71 61 107 38 39 40 41 75 0\n109 -2 19 0 98 4 34 49 74 0\n110 -8 16 0 102 10 13 23 31 78 0\n111 -9 -35 0 94 50 46 44 43 1 2 3 73 0\n112 -7 16 0 102 9 12 22 30 78 0\n113 44 0 99 102 71 108 45 47 57 109 110 111 112 75 19 20 28 33 78 0\n114 -11 0 113 52 0\n115 -20 0 113 53 0\n116 -21 0 113 54 0\n117 -22 0 113 55 0\n118 -27 0 113 56 0\n119 38 0 113 72 0\n120 13 0 117 100 115 116 114 76 0\n121 -14 0 120 6 0\n122 -15 0 120 7 0\n123 -18 0 120 14 0\n124 -24 0 120 18 0\n125 -34 0 120 42 0\n126 -37 0 120 48 0\n127 -32 0 120 119 58 0\n128 -25 0 126 127 125 59 0\n129 23 0 128 101 121 124 122 77 0\n130 -16 0 129 16 0\n131 -17 0 129 17 0\n132 -28 0 129 32 0\n133 0 132 131 102 123 130 118 78 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00028.record045
