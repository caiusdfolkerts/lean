module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00071Frames
public import GraphInputsRow26Part00071Leaves
public import GraphInputsRow26Part00071Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00071.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3b19c3aa5a368e68d8b6338ae1b89eb86d1ac4e966659364e5656352d58d334ad1b4e3c4e5334e332ce4b52ccb2ac6b86c9b16cc789d2729c6785c970dc8f13c2f4709c9891a4590e07a61384c946499295152550d2341d90e2318e1344d0b12c1b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a6db6db69369349349269269a49a493492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 70), (facetIndex 80)]))
 (.leaf ([(facetIndex 54), (facetIndex 62), (facetIndex 66), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 35), (facetIndex 43), (facetIndex 50), (facetIndex 52), (facetIndex 53)]))
 (.leaf ([(facetIndex 30), (facetIndex 33), (facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 39)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 31), (facetIndex 41), (facetIndex 44), (facetIndex 46), (facetIndex 47), (facetIndex 48)]))
 (.leaf ([(facetIndex 34), (facetIndex 56), (facetIndex 59), (facetIndex 61)])))
 (.branch 7
 (.leaf ([(facetIndex 57), (facetIndex 58), (facetIndex 63), (facetIndex 65)]))
 (.leaf ([(facetIndex 32), (facetIndex 42)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "8070c68bb50520849045e06db55f8cz16;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00071.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00071.record004" 66

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00071.record004" "{\"ridges\":[[8,530],[20,73],[31,73],[35,530],[36,37],[38,37],[43,529],[44,73],[47,73],[50,530],[52,529],[53,530],[54,224],[56,37],[56,164],[57,73],[57,200],[60,37],[62,164],[62,193],[64,73],[64,600],[66,73],[66,200],[67,688],[68,720],[69,193],[69,224],[75,564],[78,600],[81,200]],\"owners\":[[43,529,[60,67,68],[8,35,50,52,53,64]],[52,529,[60,67],[8,35,43,50,53,64,68]],[8,530,[75,78],[35,43,50,52,53]],[35,530,[78],[8,43,50,52,53,75]],[50,530,[78],[8,35,43,52,53,75]],[53,530,[75,78],[8,35,43,50,52]],[56,164,[74,76],[17,37,59,62,72,81]],[62,164,[72,74],[17,37,56,59,76,81]],[62,193,[20,46,51,63,68],[21,40,54,57,69]],[69,193,[20,40,46,51,57,63],[21,54,62,68]],[57,200,[77,79],[20,46,63,66,73,81]],[66,200,[73,77],[20,46,57,63,79,81]],[81,200,[20,46,63,77],[57,66,73,79]],[54,224,[81],[21,62,66,69,76,79]],[69,224,[76,79,81],[21,54,62,66]],[75,564,[60],[]],[64,600,[78],[]],[78,600,[64],[]],[67,688,[],[]],[68,720,[],[]]],\"edges\":[[34,[8,35,43,50,52,53,60,64,67,68,75,78]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00071.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00071.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-7,-5],[-13,-7],[-15,-7],[-19,-3],[-19,-5],[-19,-15],[-26,-5],[-26,-13],[-27,-5],[-27,-15],[-27,-26],[-28,-4],[-28,-5],[-29,-5],[-29,-13],[-29,-27],[-30,-6],[-30,-7],[-30,-10],[-30,-12],[-30,-29],[-31,-30],[-33,-5],[-33,-15],[-33,-26],[-34,-15],[-34,-18],[-35,-15],[-35,-34],[-36,-17],[-40,-5],[-40,-7],[-40,-13],[-40,-15],[-40,-25],[-41,-40],[-42,-40],[-43,-15],[-43,-40],[-45,-15],[-45,-40],[-46,-7],[-46,-40],[-47,-14],[-47,-20],[-47,-22],[-47,-33],[-47,-46],[-48,-7],[-48,-40],[-49,-28],[-49,-31],[-49,-35],[-50,-4],[-50,-17],[-9,-26,-30],[-11,-26,-30],[-2,-4,-34],[-2,-17,-34],[-2,-19,-34],[-19,-27,-34],[-19,-34,-36],[-16,30,37,38],[-23,30,37],[-1,44,47],[-8,47],[-21,47],[-24,44,47],[-26,43,45],[-32,41,43],[-32,2,18,22,33,38],[-39,2,13,18,22,27,33],[-27,46,48],[-36,42,46],[-50,2,18,33,46],[-25,50],[-39,45,48,50],[-44,30],[-34,47],[-47,34],[-37],[-38],[-51,40,49],[-52,25,32,36,39],[-53,3,6,9,10,11,12],[-54,4,14,17,18,19,20],[-55,7,26,29,31],[-56,27,28,33,35],[-57,5,15],[-58,51],[-58,52],[-59,53],[-60,58],[-60,59],[-61,54],[-61,55],[-62,56,57],[-63,56],[-63,57],[-64,61,63],[-65,61],[-64,62],[-65,63],[-66,60,65],[-66,64],[66],[1,8,16,21,23,24,30,34,37,38,44,47]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":34,\"b\":32},{\"tag\":\"incompatible\",\"a\":40,\"b\":34},{\"tag\":\"incompatible\",\"a\":42,\"b\":34},{\"tag\":\"incompatible\",\"a\":47,\"b\":30},{\"tag\":\"incompatible\",\"a\":47,\"b\":32},{\"tag\":\"incompatible\",\"a\":47,\"b\":42},{\"tag\":\"incompatible\",\"a\":56,\"b\":32},{\"tag\":\"incompatible\",\"a\":56,\"b\":40},{\"tag\":\"incompatible\",\"a\":57,\"b\":32},{\"tag\":\"incompatible\",\"a\":57,\"b\":42},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":31},{\"tag\":\"incompatible\",\"a\":58,\"b\":32},{\"tag\":\"incompatible\",\"a\":59,\"b\":32},{\"tag\":\"incompatible\",\"a\":59,\"b\":40},{\"tag\":\"incompatible\",\"a\":59,\"b\":57},{\"tag\":\"incompatible\",\"a\":60,\"b\":33},{\"tag\":\"incompatible\",\"a\":60,\"b\":34},{\"tag\":\"incompatible\",\"a\":60,\"b\":37},{\"tag\":\"incompatible\",\"a\":60,\"b\":39},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":63,\"b\":32},{\"tag\":\"incompatible\",\"a\":63,\"b\":42},{\"tag\":\"incompatible\",\"a\":63,\"b\":56},{\"tag\":\"incompatible\",\"a\":64,\"b\":42},{\"tag\":\"incompatible\",\"a\":64,\"b\":46},{\"tag\":\"incompatible\",\"a\":65,\"b\":42},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":44},{\"tag\":\"incompatible\",\"a\":70,\"b\":32},{\"tag\":\"incompatible\",\"a\":70,\"b\":34},{\"tag\":\"incompatible\",\"a\":70,\"b\":40},{\"tag\":\"incompatible\",\"a\":70,\"b\":42},{\"tag\":\"incompatible\",\"a\":70,\"b\":54},{\"tag\":\"incompatible\",\"a\":72,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":42},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":76,\"b\":42},{\"tag\":\"incompatible\",\"a\":76,\"b\":70},{\"tag\":\"incompatible\",\"a\":77,\"b\":34},{\"tag\":\"incompatible\",\"a\":77,\"b\":70},{\"tag\":\"incompatible\",\"a\":78,\"b\":41},{\"tag\":\"incompatible\",\"a\":78,\"b\":48},{\"tag\":\"incompatible\",\"a\":78,\"b\":51},{\"tag\":\"incompatible\",\"a\":78,\"b\":63},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":34},{\"tag\":\"incompatible\",\"a\":79,\"b\":70},{\"tag\":\"incompatible\",\"a\":80,\"b\":58},{\"tag\":\"incompatible\",\"a\":80,\"b\":61},{\"tag\":\"incompatible\",\"a\":80,\"b\":65},{\"tag\":\"incompatible\",\"a\":81,\"b\":31},{\"tag\":\"incompatible\",\"a\":81,\"b\":44},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[36,56,60]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[38,56,60]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[20,31,64]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[20,44,64]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[20,47,64]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[47,57,64]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[47,64,66]},{\"tag\":\"mate\",\"ridge\":529,\"a\":43,\"owners\":[60,67,68]},{\"tag\":\"mate\",\"ridge\":529,\"a\":52,\"owners\":[60,67]},{\"tag\":\"mate\",\"ridge\":530,\"a\":8,\"owners\":[75,78]},{\"tag\":\"mate\",\"ridge\":530,\"a\":35,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":530,\"a\":50,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":530,\"a\":53,\"owners\":[75,78]},{\"tag\":\"mate\",\"ridge\":164,\"a\":56,\"owners\":[74,76]},{\"tag\":\"mate\",\"ridge\":164,\"a\":62,\"owners\":[72,74]},{\"tag\":\"mate\",\"ridge\":193,\"a\":62,\"owners\":[20,46,51,63,68]},{\"tag\":\"mate\",\"ridge\":193,\"a\":69,\"owners\":[20,40,46,51,57,63]},{\"tag\":\"mate\",\"ridge\":200,\"a\":57,\"owners\":[77,79]},{\"tag\":\"mate\",\"ridge\":200,\"a\":66,\"owners\":[73,77]},{\"tag\":\"mate\",\"ridge\":200,\"a\":81,\"owners\":[20,46,63,77]},{\"tag\":\"mate\",\"ridge\":224,\"a\":54,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":224,\"a\":69,\"owners\":[76,79,81]},{\"tag\":\"mate\",\"ridge\":564,\"a\":75,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":600,\"a\":64,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":600,\"a\":78,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":688,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":720,\"a\":68,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[70,80],\"full_literals\":[-51,40,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[54,62,66,69],\"full_literals\":[-52,25,32,36,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[30,33,36,37,38,39],\"full_literals\":[-53,3,6,9,10,11,12]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[31,41,44,46,47,48],\"full_literals\":[-54,4,14,17,18,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[34,56,59,61],\"full_literals\":[-55,7,26,29,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[57,58,63,65],\"full_literals\":[-56,27,28,33,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[32,42],\"full_literals\":[-57,5,15]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-60,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,56,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,61,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-66,60,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[8,35,43,50,52,53,60,64,67,68,75,78]}]}"
  "p cnf 66 107\n-7 -5 0\n-13 -7 0\n-15 -7 0\n-19 -3 0\n-19 -5 0\n-19 -15 0\n-26 -5 0\n-26 -13 0\n-27 -5 0\n-27 -15 0\n-27 -26 0\n-28 -4 0\n-28 -5 0\n-29 -5 0\n-29 -13 0\n-29 -27 0\n-30 -6 0\n-30 -7 0\n-30 -10 0\n-30 -12 0\n-30 -29 0\n-31 -30 0\n-33 -5 0\n-33 -15 0\n-33 -26 0\n-34 -15 0\n-34 -18 0\n-35 -15 0\n-35 -34 0\n-36 -17 0\n-40 -5 0\n-40 -7 0\n-40 -13 0\n-40 -15 0\n-40 -25 0\n-41 -40 0\n-42 -40 0\n-43 -15 0\n-43 -40 0\n-45 -15 0\n-45 -40 0\n-46 -7 0\n-46 -40 0\n-47 -14 0\n-47 -20 0\n-47 -22 0\n-47 -33 0\n-47 -46 0\n-48 -7 0\n-48 -40 0\n-49 -28 0\n-49 -31 0\n-49 -35 0\n-50 -4 0\n-50 -17 0\n-9 -26 -30 0\n-11 -26 -30 0\n-2 -4 -34 0\n-2 -17 -34 0\n-2 -19 -34 0\n-19 -27 -34 0\n-19 -34 -36 0\n-16 30 37 38 0\n-23 30 37 0\n-1 44 47 0\n-8 47 0\n-21 47 0\n-24 44 47 0\n-26 43 45 0\n-32 41 43 0\n-32 2 18 22 33 38 0\n-39 2 13 18 22 27 33 0\n-27 46 48 0\n-36 42 46 0\n-50 2 18 33 46 0\n-25 50 0\n-39 45 48 50 0\n-44 30 0\n-34 47 0\n-47 34 0\n-37 0\n-38 0\n-51 40 49 0\n-52 25 32 36 39 0\n-53 3 6 9 10 11 12 0\n-54 4 14 17 18 19 20 0\n-55 7 26 29 31 0\n-56 27 28 33 35 0\n-57 5 15 0\n-58 51 0\n-58 52 0\n-59 53 0\n-60 58 0\n-60 59 0\n-61 54 0\n-61 55 0\n-62 56 57 0\n-63 56 0\n-63 57 0\n-64 61 63 0\n-65 61 0\n-64 62 0\n-65 63 0\n-66 60 65 0\n-66 64 0\n66 0\n1 8 16 21 23 24 30 34 37 38 44 47 0\n"
  "108 64 0 106 105 0\n109 62 0 108 102 0\n110 1 8 16 21 23 24 30 34 44 47 0 81 82 107 0\n111 47 30 0 82 81 78 64 63 66 67 79 68 65 110 0\n112 -63 -47 0 80 29 26 47 98 99 89 9 13 88 0\n113 -50 -47 0 108 112 100 95 80 27 48 47 45 44 54 55 75 86 60 0\n114 -19 13 -47 0 106 82 113 76 112 103 104 93 91 80 27 47 46 60 61 62 71 72 84 0\n115 27 2 -56 13 -47 0 108 106 82 47 46 80 27 71 114 113 76 112 103 104 93 91 100 95 29 45 44 88 72 12 84 86 30 0\n116 -2 19 -47 0 108 112 100 95 80 27 45 44 58 59 86 0\n117 -13 63 0 108 106 103 104 93 90 100 96 2 8 15 33 87 83 52 0\n118 -19 0 108 106 4 5 6 89 99 103 100 104 96 94 92 117 114 111 17 18 19 20 21 22 87 56 57 85 0\n119 -40 63 0 108 106 103 104 93 91 100 96 32 35 36 37 39 41 43 50 70 74 69 84 77 113 111 21 22 87 0\n120 -7 -56 13 0 118 18 42 49 111 73 116 115 0\n121 -26 57 0 109 106 99 103 104 93 90 119 83 53 51 97 11 25 88 0\n122 57 13 0 109 108 106 99 97 103 100 104 96 93 90 119 83 51 52 53 120 121 87 16 21 88 111 47 0\n123 -29 -57 0 14 21 89 111 26 80 0\n124 -5 31 -55 29 0 1 7 87 0\n125 31 -55 -57 0 123 124 89 3 38 40 87 69 0\n126 -31 0 106 22 52 111 112 103 119 104 83 93 90 0\n127 -5 61 0 108 106 101 104 93 90 100 98 9 13 23 31 88 83 53 0\n128 -57 0 126 108 106 125 96 100 101 98 104 93 90 127 89 10 24 28 34 88 83 51 0\n129 -63 0 128 99 0\n130 13 0 128 122 0\n131 0 130 129 117 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00071.record004
