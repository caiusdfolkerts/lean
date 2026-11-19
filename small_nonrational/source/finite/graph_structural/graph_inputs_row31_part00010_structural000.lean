module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow31Part00010Frames
public import GraphInputsRow31Part00010Leaves
public import GraphInputsRow31Part00010Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "6e364e332c9b29c6725c4f07cb4b8aca9aa9aa9a968ba1eb86c9a66a5a56c3a8e63a4e8b92e1ba1e2785e6c7896a5994e4b91e785d156565535c368d6364d1b51d2745de0ec368cd32cf0ba2d8b92d2b2ac6b16f07a1d8791d2725e0f43c8f13f881d30c4b03c1ca8a2683a91866158368382e07871625292643949465154354342d0746324c530cc8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6d26db49a6da69369a49a49249a4924da6934d249b69349a4936d2492449249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 59), (facetIndex 81)]))
 (.leaf ([(facetIndex 102), (facetIndex 115)])))
 (.branch 3
 (.leaf ([(facetIndex 93), (facetIndex 99), (facetIndex 105)]))
 (.branch 4
 (.leaf ([(facetIndex 95), (facetIndex 101), (facetIndex 114)]))
 (.leaf ([(facetIndex 53), (facetIndex 108), (facetIndex 111)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 47), (facetIndex 48), (facetIndex 60), (facetIndex 66), (facetIndex 73)]))
 (.leaf ([(facetIndex 46), (facetIndex 68), (facetIndex 71), (facetIndex 110)])))
 (.branch 8
 (.leaf ([(facetIndex 56), (facetIndex 89), (facetIndex 103)]))
 (.branch 9
 (.leaf ([(facetIndex 74), (facetIndex 96), (facetIndex 109)]))
 (.leaf ([(facetIndex 61)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "1300468400207130200830200070000000000000085060060500009500070040000556z2e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
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
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0013 : List Nat := [6]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8, 9]
def grouped3_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [8, 9]
def grouped3_0018 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record003" 69

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record003" "{\"ridges\":[[21,392],[29,578],[32,642],[38,896],[45,580],[46,390],[54,392],[55,642],[59,418],[60,705],[61,771],[66,585],[67,385],[67,392],[71,404],[73,833],[74,645],[78,385],[78,392],[79,385],[79,392],[80,385],[80,896],[81,432],[88,578],[90,642],[92,580],[93,660],[94,578],[96,390],[100,642],[104,642],[104,896],[105,720],[109,404],[113,896],[114,864]],\"owners\":[[67,385,[59,61,81],[21,46,54,71,74,78,79,80]],[78,385,[46,59,61,74],[21,54,67,71,79,80,81]],[79,385,[46,61,71,74],[21,54,59,67,78,80,81]],[80,385,[46,59,71,81],[21,54,61,67,74,78,79]],[21,392,[38,89,102,104,109,113,115],[54,67,78,79]],[54,392,[38,109,113,115],[21,67,78,79,89,102,104]],[67,392,[38,102,104,115],[21,54,78,79,89,109,113]],[78,392,[38,89,102,104,113],[21,54,67,79,109,115]],[79,392,[38,89,104,109,113],[21,54,67,78,102,115]],[29,578,[53,60,99,101,105],[45,88,92,94]],[88,578,[60,105],[29,45,53,92,94,99,101]],[94,578,[53,60,99,105],[29,45,88,92,101]],[45,580,[108,111,114],[29,66,73,88,92,94]],[92,580,[66,73,111,114],[29,45,88,94,108]],[32,642,[47,60,61,93,96,105],[55,90,100,104]],[55,642,[93,96,105],[32,47,60,61,90,100,104]],[90,642,[60,61,105],[32,47,55,93,96,100,104]],[100,642,[47,60,61,96],[32,55,90,93,104,105]],[104,642,[47,60,93,105],[32,55,61,90,96,100]],[38,896,[61,74,96],[80,104,113]],[80,896,[96],[38,61,74,104,113]],[104,896,[74],[38,61,80,96,113]],[113,896,[61],[38,74,80,96,104]],[46,390,[89,96],[]],[96,390,[46,89],[]],[74,645,[47,68],[]],[61,771,[48,56],[]],[66,585,[53],[]],[59,418,[102],[]],[60,705,[],[]],[71,404,[109],[]],[109,404,[71],[]],[73,833,[],[]],[81,432,[115],[]],[93,660,[110],[]],[105,720,[],[]],[114,864,[],[]]],\"edges\":[[41,[29,45,53,60,66,73,88,92,94,99,101,105,108,111,114]],[42,[21,38,46,54,59,61,67,71,74,78,79,80,81,89,96,102,104,109,113,115]],[43,[32,38,47,55,60,61,68,74,80,90,93,96,100,104,105,110,113]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-17,13,15,25],[-22,6,13,15,21],[-23,6,15,19,21],[-24,6,13,19,25],[-1,4,27,36,37,40,43,45],[-10,4,40,43,45],[-17,4,36,37,45],[-22,4,27,36,37,43],[-23,4,27,37,40,43],[-2,9,14,33,35,38],[-26,14,38],[-31,9,14,33,38],[-5,39,42,44],[-29,16,20,42,44],[-3,7,14,15,30,32,38],[-11,30,32,38],[-28,14,15,38],[-34,7,14,15,32],[-37,7,14,30,38],[-4,15,21,32],[-24,32],[-37,21],[-43,15],[-6,27,32],[-32,6,27],[-21,7,18],[-15,8,12],[-16,9],[-13,36],[-14],[-19,40],[-40,19],[-20],[-25,45],[-30,41],[-38],[-44],[-13,46],[-25,46],[-36,47],[-45,47],[-33,48],[-35,49],[-9,50],[-39,50],[-42,50],[-7,51],[-8,51],[-6,52],[-18,52],[-19,52],[-41,52],[-12,53],[-27,53],[-54,21,32,40],[-21,54],[-32,54],[-40,54],[-55,15],[-15,55],[-47,56],[-46,56],[-46,-47,57],[-50,58],[-49,58],[-58,59],[-48,59],[-59,60],[-56,-59,61],[-57,-59,62],[-52,63],[-51,63],[-64,54,55],[-55,64],[-54,64],[-64,65],[-53,65],[-53,-64,66],[-65,67],[-66,68],[-63,67],[-63,-65,68],[-60,-68,69],[-61,-67,69],[-62,69],[-69],[2,5,9,14,16,20,26,29,31,33,35,38,39,42,44],[1,4,6,10,13,15,17,19,21,22,23,24,25,27,32,36,37,40,43,45],[3,4,7,11,14,15,18,21,24,28,30,32,34,37,38,41,43]],\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":385,\"a\":67,\"owners\":[59,61,81]},{\"tag\":\"mate\",\"ridge\":385,\"a\":78,\"owners\":[46,59,61,74]},{\"tag\":\"mate\",\"ridge\":385,\"a\":79,\"owners\":[46,61,71,74]},{\"tag\":\"mate\",\"ridge\":385,\"a\":80,\"owners\":[46,59,71,81]},{\"tag\":\"mate\",\"ridge\":392,\"a\":21,\"owners\":[38,89,102,104,109,113,115]},{\"tag\":\"mate\",\"ridge\":392,\"a\":54,\"owners\":[38,109,113,115]},{\"tag\":\"mate\",\"ridge\":392,\"a\":67,\"owners\":[38,102,104,115]},{\"tag\":\"mate\",\"ridge\":392,\"a\":78,\"owners\":[38,89,102,104,113]},{\"tag\":\"mate\",\"ridge\":392,\"a\":79,\"owners\":[38,89,104,109,113]},{\"tag\":\"mate\",\"ridge\":578,\"a\":29,\"owners\":[53,60,99,101,105]},{\"tag\":\"mate\",\"ridge\":578,\"a\":88,\"owners\":[60,105]},{\"tag\":\"mate\",\"ridge\":578,\"a\":94,\"owners\":[53,60,99,105]},{\"tag\":\"mate\",\"ridge\":580,\"a\":45,\"owners\":[108,111,114]},{\"tag\":\"mate\",\"ridge\":580,\"a\":92,\"owners\":[66,73,111,114]},{\"tag\":\"mate\",\"ridge\":642,\"a\":32,\"owners\":[47,60,61,93,96,105]},{\"tag\":\"mate\",\"ridge\":642,\"a\":55,\"owners\":[93,96,105]},{\"tag\":\"mate\",\"ridge\":642,\"a\":90,\"owners\":[60,61,105]},{\"tag\":\"mate\",\"ridge\":642,\"a\":100,\"owners\":[47,60,61,96]},{\"tag\":\"mate\",\"ridge\":642,\"a\":104,\"owners\":[47,60,93,105]},{\"tag\":\"mate\",\"ridge\":896,\"a\":38,\"owners\":[61,74,96]},{\"tag\":\"mate\",\"ridge\":896,\"a\":80,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":896,\"a\":104,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":896,\"a\":113,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":390,\"a\":46,\"owners\":[89,96]},{\"tag\":\"mate\",\"ridge\":390,\"a\":96,\"owners\":[46,89]},{\"tag\":\"mate\",\"ridge\":645,\"a\":74,\"owners\":[47,68]},{\"tag\":\"mate\",\"ridge\":771,\"a\":61,\"owners\":[48,56]},{\"tag\":\"mate\",\"ridge\":585,\"a\":66,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":418,\"a\":59,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":705,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":404,\"a\":71,\"owners\":[109]},{\"tag\":\"mate\",\"ridge\":404,\"a\":109,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":833,\"a\":73,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":432,\"a\":81,\"owners\":[115]},{\"tag\":\"mate\",\"ridge\":660,\"a\":93,\"owners\":[110]},{\"tag\":\"mate\",\"ridge\":720,\"a\":105,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":864,\"a\":114,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":59,\"full_literals\":[-13,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":81,\"full_literals\":[-25,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":102,\"full_literals\":[-36,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":115,\"full_literals\":[-45,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":99,\"full_literals\":[-33,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":101,\"full_literals\":[-35,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":53,\"full_literals\":[-9,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":108,\"full_literals\":[-39,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":111,\"full_literals\":[-42,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":47,\"full_literals\":[-7,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":48,\"full_literals\":[-8,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":46,\"full_literals\":[-6,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":68,\"full_literals\":[-18,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":71,\"full_literals\":[-19,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":110,\"full_literals\":[-41,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":56,\"full_literals\":[-12,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":89,\"full_literals\":[-27,53]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[74,96,109],\"full_literals\":[-54,21,32,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":74,\"full_literals\":[-21,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":96,\"full_literals\":[-32,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":109,\"full_literals\":[-40,54]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[61],\"full_literals\":[-55,15]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":61,\"full_literals\":[-15,55]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-47,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-59,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-65,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-60,-68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[29,45,53,60,66,73,88,92,94,99,101,105,108,111,114]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[21,38,46,54,59,61,67,71,74,78,79,80,81,89,96,102,104,109,113,115]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[32,38,47,55,60,61,68,74,80,90,93,96,100,104,105,110,113]}]}"
  "p cnf 69 89\n-17 13 15 25 0\n-22 6 13 15 21 0\n-23 6 15 19 21 0\n-24 6 13 19 25 0\n-1 4 27 36 37 40 43 45 0\n-10 4 40 43 45 0\n-17 4 36 37 45 0\n-22 4 27 36 37 43 0\n-23 4 27 37 40 43 0\n-2 9 14 33 35 38 0\n-26 14 38 0\n-31 9 14 33 38 0\n-5 39 42 44 0\n-29 16 20 42 44 0\n-3 7 14 15 30 32 38 0\n-11 30 32 38 0\n-28 14 15 38 0\n-34 7 14 15 32 0\n-37 7 14 30 38 0\n-4 15 21 32 0\n-24 32 0\n-37 21 0\n-43 15 0\n-6 27 32 0\n-32 6 27 0\n-21 7 18 0\n-15 8 12 0\n-16 9 0\n-13 36 0\n-14 0\n-19 40 0\n-40 19 0\n-20 0\n-25 45 0\n-30 41 0\n-38 0\n-44 0\n-13 46 0\n-25 46 0\n-36 47 0\n-45 47 0\n-33 48 0\n-35 49 0\n-9 50 0\n-39 50 0\n-42 50 0\n-7 51 0\n-8 51 0\n-6 52 0\n-18 52 0\n-19 52 0\n-41 52 0\n-12 53 0\n-27 53 0\n-54 21 32 40 0\n-21 54 0\n-32 54 0\n-40 54 0\n-55 15 0\n-15 55 0\n-47 56 0\n-46 56 0\n-46 -47 57 0\n-50 58 0\n-49 58 0\n-58 59 0\n-48 59 0\n-59 60 0\n-56 -59 61 0\n-57 -59 62 0\n-52 63 0\n-51 63 0\n-64 54 55 0\n-55 64 0\n-54 64 0\n-64 65 0\n-53 65 0\n-53 -64 66 0\n-65 67 0\n-66 68 0\n-63 67 0\n-63 -65 68 0\n-60 -68 69 0\n-61 -67 69 0\n-62 69 0\n-69 0\n2 5 9 14 16 20 26 29 31 33 35 38 39 42 44 0\n1 4 6 10 13 15 17 19 21 22 23 24 25 27 32 36 37 40 43 45 0\n3 4 7 11 14 15 18 21 24 28 30 32 34 37 38 41 43 0\n"
  "90 -26 0 36 30 11 0\n91 -62 0 86 85 0\n92 2 5 9 16 29 31 33 35 39 42 0 30 33 90 36 37 87 0\n93 3 4 7 11 15 18 21 24 28 30 32 34 37 41 43 0 30 36 89 0\n94 59 0 36 30 37 33 66 67 64 65 42 44 45 46 43 10 12 28 13 14 92 0\n95 60 0 94 68 0\n96 -57 0 94 91 70 0\n97 -68 0 95 86 83 0\n98 -66 0 97 80 0\n99 -64 63 0 98 71 51 32 72 47 50 26 48 49 78 53 54 27 25 59 55 73 0\n100 63 46 0 36 30 39 38 71 72 49 50 51 52 47 4 26 35 19 99 74 75 60 57 23 17 15 16 18 20 93 0\n101 56 0 97 61 62 40 41 38 39 100 82 76 77 74 75 54 60 56 57 58 23 1 22 21 24 20 31 2 5 6 9 88 0\n102 61 0 101 94 69 0\n103 -67 0 102 86 84 0\n104 -65 0 103 79 0\n105 -63 0 103 81 0\n106 -64 0 104 76 0\n107 -53 0 104 77 0\n108 -52 0 105 71 0\n109 -51 0 105 72 0\n110 46 0 105 100 0\n111 -55 0 106 74 0\n112 -54 0 106 75 0\n113 -27 0 107 54 0\n114 -6 0 108 49 0\n115 -19 0 108 51 0\n116 -41 0 108 52 0\n117 -7 0 109 47 0\n118 -47 0 110 96 63 0\n119 -15 0 111 60 0\n120 -21 0 112 56 0\n121 -32 0 112 57 0\n122 -40 0 112 58 0\n123 -23 0 115 114 120 119 3 0\n124 -30 0 116 35 0\n125 -37 0 117 30 124 36 19 0\n126 -36 0 118 40 0\n127 -45 0 118 41 0\n128 -43 0 119 23 0\n129 -24 0 121 21 0\n130 -4 0 121 119 120 20 0\n131 -13 0 126 29 0\n132 -25 0 127 34 0\n133 -1 0 130 113 126 125 122 128 127 5 0\n134 -10 0 130 122 128 127 6 0\n135 -17 0 130 126 125 127 7 0\n136 -22 0 130 113 126 125 128 8 0\n137 0 130 133 114 134 131 119 135 115 120 136 123 129 132 113 121 126 125 122 128 127 88 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "398ce394cd2cca723c1f392d4b8ab29aac6a9a66a5a4e87ae1ac669b16a5996959361da8e938ce2b86e8789ee4751e26c96a719a6599965391e785b15a5c5695656554d475a364d334ad1b61d275a364d531cd8b32d2b2ac6b46c9b61cc749ca719d1725e589528c9321c1703c4c85a0e8560d88e1382e0793116439154352344d0b41d60d2344c530cc8b12c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6924db6db6926db6d24924926db6db4936db692492492492492492492449249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 46), (facetIndex 47), (facetIndex 53), (facetIndex 54), (facetIndex 55)]))
 (.leaf ([(facetIndex 57), (facetIndex 58), (facetIndex 84), (facetIndex 85), (facetIndex 111), (facetIndex 112), (facetIndex 113)])))
 (.branch 3
 (.leaf ([(facetIndex 43), (facetIndex 45), (facetIndex 65), (facetIndex 92)]))
 (.leaf ([(facetIndex 62), (facetIndex 63), (facetIndex 66), (facetIndex 75)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 50), (facetIndex 52), (facetIndex 74), (facetIndex 101)]))
 (.leaf ([(facetIndex 89), (facetIndex 90), (facetIndex 93), (facetIndex 102)])))
 (.branch 7
 (.leaf ([(facetIndex 44), (facetIndex 51), (facetIndex 61), (facetIndex 88), (facetIndex 114)]))
 (.branch 8
 (.leaf ([(facetIndex 42), (facetIndex 49), (facetIndex 56), (facetIndex 60), (facetIndex 87)]))
 (.leaf ([(facetIndex 41), (facetIndex 48), (facetIndex 59), (facetIndex 64), (facetIndex 73), (facetIndex 86), (facetIndex 91), (facetIndex 100)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "61110000000054800000052855678110000000034800000032833678117000464780026278z29;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 67), (facetIndex 69), (facetIndex 70), (facetIndex 96), (facetIndex 115)]))
 (.leaf ([(facetIndex 68), (facetIndex 71), (facetIndex 72), (facetIndex 78), (facetIndex 82)])))
 (.branch 3
 (.leaf ([(facetIndex 80), (facetIndex 98)]))
 (.leaf ([(facetIndex 79), (facetIndex 97)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 95), (facetIndex 99), (facetIndex 105), (facetIndex 107), (facetIndex 109)]))
 (.leaf ([(facetIndex 76), (facetIndex 81), (facetIndex 106), (facetIndex 108), (facetIndex 117)])))
 (.branch 7
 (.leaf ([(facetIndex 77), (facetIndex 94), (facetIndex 103), (facetIndex 104)]))
 (.leaf ([(facetIndex 83), (facetIndex 110), (facetIndex 116), (facetIndex 118)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1ef0001e5966c00898980000000e6a675001201z33;"⟩
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
def grouped2_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6, 7, 8]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2, 3]
def grouped3_0017 : List Nat := [4]
def grouped3_0018 : List Nat := [4, 5]
def grouped3_0019 : List Nat := [4, 5, 6, 7]
def grouped3_0020 : List Nat := [5]
def grouped3_0021 : List Nat := [6]
def grouped3_0022 : List Nat := [6, 7]
def grouped3_0023 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record008" 61

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record008" "{\"ridges\":[[45,385],[45,386],[63,648],[69,784],[72,896],[78,777],[78,784],[79,424],[81,777],[81,896],[82,833],[83,896],[96,774],[99,774],[99,896],[103,408],[105,778],[109,834],[110,784],[115,804],[116,896],[117,808],[118,408],[118,784]],\"owners\":[[45,385,[76,79,81,83],[13,52,55,56,67,70,72]],[45,386,[103,106,108,110],[13,52,55,56,94,97,99]],[63,648,[104,107,108,118],[36,77,80,81,90,113,114]],[69,784,[105,109,110,117,118],[78,82,83,96,115,116]],[78,784,[96,109,110,115,116],[69,82,83,105,117,118]],[110,784,[69,78,82,115,117],[83,96,105,109,116,118]],[118,784,[69,82,96,109,115],[78,83,105,110,116,117]],[72,896,[108,110,118],[81,83,99,116]],[81,896,[99,110,116],[72,83,108,118]],[83,896,[99,108],[72,81,110,116,118]],[99,896,[81,83,118],[72,108,110,116]],[116,896,[81,108],[72,83,99,110,118]],[103,408,[76,118],[]],[118,408,[76,103],[]],[78,777,[81],[]],[81,777,[78],[]],[79,424,[106],[]],[82,833,[],[]],[96,774,[99],[]],[99,774,[96],[]],[105,778,[108],[]],[109,834,[],[]],[115,804,[],[]],[117,808,[],[]]],\"edges\":[[44,[69,72,78,81,82,83,96,99,105,108,109,110,115,116,117,118]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-1],[-9,-5],[-9,-6],[-9,-7],[-9,-8],[-12,-9],[-18,-5],[-18,-8],[-18,-12],[-21,-9],[-24,-1],[-24,-7],[-24,-21],[-28,-24],[-31,-24],[-32,-3],[-32,-4],[-32,-11],[-32,-19],[-32,-20],[-32,-22],[-32,-25],[-32,-26],[-34,-18],[-2,13,15,16,18],[-2,27,30,32,34],[-6,28,31,32,38],[-9,29,33,34,37,38],[-14,23,33,34,35,36],[-34,9,14,17,35,37],[-38,9,17,23,33,35],[-10,32,34,38],[-16,24,34,36],[-18,24,32],[-24,16,18,38],[-36,16,32],[-27,13,38],[-38,13,27],[-14,16],[-16,14],[-15,30],[-17],[-23,24],[-24,23],[-29,32],[-33],[-35],[-37],[-39,1,2,7,21],[-40,5,6,8,12],[-41,3,4,11,25],[-42,19,20,22,26],[-43,39,40],[-44,43],[-45,41,42],[-46,45],[-47,44],[-47,46],[47],[-9,48],[-23,48],[-10,49],[-14,49],[-24,50],[-13,51],[-16,51],[-30,51],[-27,52],[-34,53],[-36,53],[-38,53],[-49,54],[-48,54],[-54,55],[-51,56],[-50,-51,57],[-53,58],[-52,-53,59],[-59,60],[-56,-58,60],[-57,60],[-55,-60,61],[-61],[9,10,14,16,17,18,23,24,29,32,33,34,35,36,37,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":69,\"b\":43},{\"tag\":\"incompatible\",\"a\":69,\"b\":62},{\"tag\":\"incompatible\",\"a\":69,\"b\":63},{\"tag\":\"incompatible\",\"a\":69,\"b\":65},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":75,\"b\":69},{\"tag\":\"incompatible\",\"a\":83,\"b\":62},{\"tag\":\"incompatible\",\"a\":83,\"b\":66},{\"tag\":\"incompatible\",\"a\":83,\"b\":75},{\"tag\":\"incompatible\",\"a\":92,\"b\":69},{\"tag\":\"incompatible\",\"a\":99,\"b\":43},{\"tag\":\"incompatible\",\"a\":99,\"b\":65},{\"tag\":\"incompatible\",\"a\":99,\"b\":92},{\"tag\":\"incompatible\",\"a\":104,\"b\":99},{\"tag\":\"incompatible\",\"a\":107,\"b\":99},{\"tag\":\"incompatible\",\"a\":108,\"b\":50},{\"tag\":\"incompatible\",\"a\":108,\"b\":52},{\"tag\":\"incompatible\",\"a\":108,\"b\":74},{\"tag\":\"incompatible\",\"a\":108,\"b\":89},{\"tag\":\"incompatible\",\"a\":108,\"b\":90},{\"tag\":\"incompatible\",\"a\":108,\"b\":93},{\"tag\":\"incompatible\",\"a\":108,\"b\":101},{\"tag\":\"incompatible\",\"a\":108,\"b\":102},{\"tag\":\"incompatible\",\"a\":110,\"b\":83},{\"tag\":\"mate\",\"ridge\":385,\"a\":45,\"owners\":[76,79,81,83]},{\"tag\":\"mate\",\"ridge\":386,\"a\":45,\"owners\":[103,106,108,110]},{\"tag\":\"mate\",\"ridge\":648,\"a\":63,\"owners\":[104,107,108,118]},{\"tag\":\"mate\",\"ridge\":784,\"a\":69,\"owners\":[105,109,110,117,118]},{\"tag\":\"mate\",\"ridge\":784,\"a\":78,\"owners\":[96,109,110,115,116]},{\"tag\":\"mate\",\"ridge\":784,\"a\":110,\"owners\":[69,78,82,115,117]},{\"tag\":\"mate\",\"ridge\":784,\"a\":118,\"owners\":[69,82,96,109,115]},{\"tag\":\"mate\",\"ridge\":896,\"a\":72,\"owners\":[108,110,118]},{\"tag\":\"mate\",\"ridge\":896,\"a\":81,\"owners\":[99,110,116]},{\"tag\":\"mate\",\"ridge\":896,\"a\":83,\"owners\":[99,108]},{\"tag\":\"mate\",\"ridge\":896,\"a\":99,\"owners\":[81,83,118]},{\"tag\":\"mate\",\"ridge\":896,\"a\":116,\"owners\":[81,108]},{\"tag\":\"mate\",\"ridge\":408,\"a\":103,\"owners\":[76,118]},{\"tag\":\"mate\",\"ridge\":408,\"a\":118,\"owners\":[76,103]},{\"tag\":\"mate\",\"ridge\":777,\"a\":78,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":777,\"a\":81,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":424,\"a\":79,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":833,\"a\":82,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":774,\"a\":96,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":774,\"a\":99,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":778,\"a\":105,\"owners\":[108]},{\"tag\":\"mate\",\"ridge\":834,\"a\":109,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":804,\"a\":115,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":808,\"a\":117,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[43,45,65,92],\"full_literals\":[-39,1,2,7,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[62,63,66,75],\"full_literals\":[-40,5,6,8,12]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[50,52,74,101],\"full_literals\":[-41,3,4,11,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[89,90,93,102],\"full_literals\":[-42,19,20,22,26]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,39,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,41,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-46,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-47,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-47,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":69,\"full_literals\":[-9,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":96,\"full_literals\":[-23,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":72,\"full_literals\":[-10,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-14,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":99,\"full_literals\":[-24,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":76,\"full_literals\":[-13,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-16,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":106,\"full_literals\":[-30,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":103,\"full_literals\":[-27,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":110,\"full_literals\":[-34,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":116,\"full_literals\":[-36,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":118,\"full_literals\":[-38,53]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-51,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-53,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-55,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":44,\"owners\":[69,72,78,81,82,83,96,99,105,108,109,110,115,116,117,118]}]}"
  "p cnf 61 84\n-9 -1 0\n-9 -5 0\n-9 -6 0\n-9 -7 0\n-9 -8 0\n-12 -9 0\n-18 -5 0\n-18 -8 0\n-18 -12 0\n-21 -9 0\n-24 -1 0\n-24 -7 0\n-24 -21 0\n-28 -24 0\n-31 -24 0\n-32 -3 0\n-32 -4 0\n-32 -11 0\n-32 -19 0\n-32 -20 0\n-32 -22 0\n-32 -25 0\n-32 -26 0\n-34 -18 0\n-2 13 15 16 18 0\n-2 27 30 32 34 0\n-6 28 31 32 38 0\n-9 29 33 34 37 38 0\n-14 23 33 34 35 36 0\n-34 9 14 17 35 37 0\n-38 9 17 23 33 35 0\n-10 32 34 38 0\n-16 24 34 36 0\n-18 24 32 0\n-24 16 18 38 0\n-36 16 32 0\n-27 13 38 0\n-38 13 27 0\n-14 16 0\n-16 14 0\n-15 30 0\n-17 0\n-23 24 0\n-24 23 0\n-29 32 0\n-33 0\n-35 0\n-37 0\n-39 1 2 7 21 0\n-40 5 6 8 12 0\n-41 3 4 11 25 0\n-42 19 20 22 26 0\n-43 39 40 0\n-44 43 0\n-45 41 42 0\n-46 45 0\n-47 44 0\n-47 46 0\n47 0\n-9 48 0\n-23 48 0\n-10 49 0\n-14 49 0\n-24 50 0\n-13 51 0\n-16 51 0\n-30 51 0\n-27 52 0\n-34 53 0\n-36 53 0\n-38 53 0\n-49 54 0\n-48 54 0\n-54 55 0\n-51 56 0\n-50 -51 57 0\n-53 58 0\n-52 -53 59 0\n-59 60 0\n-56 -58 60 0\n-57 60 0\n-55 -60 61 0\n-61 0\n9 10 14 16 17 18 23 24 29 32 33 34 35 36 37 38 0\n"
  "85 44 0 59 57 0\n86 46 0 59 58 0\n87 43 0 85 54 0\n88 45 0 86 56 0\n89 9 10 14 16 18 23 24 29 32 34 36 38 0 42 46 47 48 84 0\n90 32 54 0 48 42 46 47 73 61 44 60 31 72 63 30 40 62 45 36 34 89 0\n91 -32 0 88 16 17 18 19 20 21 22 23 51 52 55 0\n92 -29 0 91 45 0\n93 54 0 91 90 0\n94 55 0 93 74 0\n95 -60 0 94 83 82 0\n96 -59 0 95 79 0\n97 -57 0 95 81 0\n98 -51 0 97 95 47 48 46 91 92 75 76 80 64 77 43 34 69 70 71 29 32 28 33 89 0\n99 -13 0 98 65 0\n100 -16 0 98 66 0\n101 -30 0 98 67 0\n102 -14 0 100 39 0\n103 -36 0 100 91 36 0\n104 -15 0 101 41 0\n105 24 34 38 0 46 48 103 91 92 100 102 28 32 43 34 89 0\n106 34 38 0 99 101 100 91 87 37 26 105 11 12 13 14 15 35 49 27 7 8 9 53 50 0\n107 -34 0 48 47 42 102 99 100 104 87 24 30 25 1 2 3 4 5 6 10 50 49 53 0\n108 38 0 107 106 0\n109 27 0 108 99 38 0\n110 53 0 108 71 0\n111 52 0 109 68 0\n112 0 111 110 96 78 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record008
