module
prelude
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow31Part00005Frames
public import GraphInputsRow31Part00005Leaves
public import GraphInputsRow31Part00005Metadata
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
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "dc364d53349d174ab26c6715c1f3c2d4a72b2aaa9ab86d1aa699b1665a5655a361da8e93a2e2b86e2785ef07615c5c966559e1745c96a599565655554d4756354d2b46d4749d17783d0ec370ea398d9354ccb2ac9bc1e8761e4751e2729c6745c9715c4f1e3840f2621c86a1683aa1a260d88e0b81e544711a4590e585454352342d0746314c3322c4b0ac1b21c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6d369b49a4db69269249b4da4db6d24934924db6d3492693692492249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 64), (facetIndex 77), (facetIndex 78)]))
 (.branch 2
 (.leaf ([(facetIndex 87), (facetIndex 100), (facetIndex 101)]))
 (.leaf ([(facetIndex 52), (facetIndex 107)]))))
 (.branch 4
 (.leaf ([(facetIndex 54), (facetIndex 109)]))
 (.branch 5
 (.leaf ([(facetIndex 92), (facetIndex 94), (facetIndex 112)]))
 (.leaf ([(facetIndex 103), (facetIndex 111), (facetIndex 115)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 47), (facetIndex 55), (facetIndex 93)]))
 (.branch 8
 (.leaf ([(facetIndex 56), (facetIndex 57), (facetIndex 104)]))
 (.leaf ([(facetIndex 44), (facetIndex 58), (facetIndex 72), (facetIndex 73), (facetIndex 81)]))))
 (.branch 10
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 91), (facetIndex 106), (facetIndex 108), (facetIndex 113)]))
 (.branch 11
 (.leaf ([(facetIndex 74), (facetIndex 80), (facetIndex 110)]))
 (.leaf ([(facetIndex 97), (facetIndex 114)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5b945a392907501100b0046490001000008a00000a8899000000000008776302000060086z2b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [1, 2]
def grouped3_0006 : List Nat := [2]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4, 5]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [4, 5]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [7, 8]
def grouped3_0017 : List Nat := [8]
def grouped3_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [9, 10, 11]
def grouped3_0020 : List Nat := [10]
def grouped3_0021 : List Nat := [10, 11]
def grouped3_0022 : List Nat := [11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record003" 89

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record003" "{\"ridges\":[[16,385],[16,388],[21,321],[27,642],[32,608],[34,896],[44,581],[45,385],[45,388],[46,642],[47,771],[51,321],[52,402],[53,578],[53,608],[54,673],[55,450],[56,578],[56,705],[57,771],[57,832],[58,771],[65,385],[65,388],[69,385],[69,388],[74,832],[75,896],[77,408],[78,456],[79,321],[80,801],[81,705],[81,832],[88,644],[93,402],[95,578],[95,608],[96,642],[97,832],[98,642],[98,896],[99,608],[100,680],[101,712],[102,608],[103,832],[104,450],[104,832],[107,408],[108,588],[109,680],[113,596],[113,772],[114,832],[115,832]],\"owners\":[[16,385,[52,55,58,77,78,81],[45,65,69,75]],[45,385,[77,78,81],[16,52,55,58,65,69,75]],[65,385,[52,55,58,81],[16,45,69,75,77,78]],[69,385,[55,58,78,81],[16,45,52,65,75,77]],[16,388,[34,93,98,107],[45,65,69]],[45,388,[34,107],[16,65,69,93,98]],[65,388,[34,93,98],[16,45,69,107]],[69,388,[34,98],[16,45,65,93,107]],[21,321,[43,55,57,64,70,74,78,80,81],[51,68,76,79]],[51,321,[64,70,74,78,80,81],[21,43,55,57,68,76,79]],[79,321,[43,55,57,64,74,78,81],[21,51,68,70,76,80]],[27,642,[54,56,58,100,101,104],[46,88,96,98]],[46,642,[100,101,104],[27,54,56,58,88,96,98]],[96,642,[56,58,101,104],[27,46,54,88,98,100]],[98,642,[54,56,100,101],[27,46,58,88,96,104]],[88,644,[34,72,75],[27,46,96,109]],[53,578,[87,92,97,101,103,104],[32,44,56,57,95,99,102]],[56,578,[32,87,92,95,97,99,102,103],[44,53,57,101,104]],[95,578,[56,57,101,103,104],[32,44,53,87,92,97,99,102]],[32,608,[71,80,108,111,114,115],[53,95,99,102]],[53,608,[108,111,114,115],[32,71,80,95,99,102]],[95,608,[80,115],[32,53,71,99,102,108,111,114]],[99,608,[71,80,111,114,115],[32,53,95,102,108]],[102,608,[71,80,108,114],[32,53,95,99,111,115]],[113,772,[34,47,73,75,98],[74,94,97,112,114]],[34,896,[58,81,104],[75,98]],[75,896,[104],[34,58,81,98]],[98,896,[81],[34,58,75,104]],[44,581,[71,74],[]],[47,771,[57,58],[]],[57,771,[47,58],[]],[58,771,[47,57],[]],[52,402,[93],[]],[93,402,[52],[]],[54,673,[72],[]],[55,450,[104],[]],[104,450,[55],[]],[56,705,[81],[]],[81,705,[56],[]],[57,832,[113,114,115],[74,80,81,97,103,104]],[74,832,[103,104,115],[57,80,81,97,113,114]],[81,832,[97,103,113,114,115],[57,74,80,104]],[97,832,[80,81,115],[57,74,103,104,113,114]],[103,832,[74,80,81,114],[57,97,104,113,115]],[104,832,[74,80,113,114,115],[57,81,97,103]],[114,832,[57,81,103,104],[74,80,97,113,115]],[115,832,[57,74,81,97,104],[80,103,113,114]],[80,801,[73],[]],[77,408,[107],[]],[107,408,[77],[]],[78,456,[],[]],[108,588,[87],[]],[113,596,[92,111],[]],[100,680,[109],[]],[109,680,[100],[]],[101,712,[],[]]],\"edges\":[[40,[21,43,51,55,57,64,68,70,74,76,78,79,80,81,91,97,103,104,106,110,113,114,115]],[41,[32,44,53,56,57,71,74,80,81,87,92,95,97,99,101,102,103,104,108,111,113,114,115]],[42,[16,34,45,52,55,58,65,69,75,77,78,81,93,98,104,107]],[43,[27,34,46,54,56,58,72,75,81,88,96,98,100,101,104,109]],[44,[34,47,57,58,73,74,75,80,81,94,97,98,103,104,112,113,114,115]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-30,-21],[-52,-19],[-52,-29],[-1,12,15,18,30,31,34],[-8,30,31,34],[-20,12,15,18,34],[-22,15,18,31,34],[-1,5,39,44,52],[-8,5,52],[-20,5,39,44],[-22,5,44],[-2,6,15,17,19,23,27,31,33,34],[-11,19,23,27,31,33,34],[-32,6,15,17,19,27,31,34],[-3,14,16,18,46,47,50],[-9,46,47,50],[-42,16,18,47,50],[-44,14,16,46,47],[-36,5,25,28],[-13,35,38,43,47,49,50],[-16,4,35,38,41,43,45,48,49],[-41,16,17,47,49,50],[-4,24,33,53,56,59,60],[-13,53,56,59,60],[-41,33,60],[-45,24,33,56,59,60],[-48,24,33,53,59],[-58,5,10,26,28,44],[-5,18,34,50],[-28,50],[-44,34],[-7,24,27],[-10,17,18],[-17,10,18],[-18,10,17],[-12,39],[-39,12],[-14,25],[-15,50],[-50,15],[-16,34],[-34,16],[-17,58,59,60],[-27,49,50,60],[-34,43,49,58,59,60],[-43,33,34,60],[-49,27,33,34,59],[-50,27,33,58,59,60],[-59,17,34,49,50],[-60,17,27,34,43,50],[-33,26],[-30,52],[-52,30],[-31],[-53,35],[-58,38,56],[-46,54],[-54,46],[-47],[-30,61],[-35,62],[-12,63],[-52,63],[-14,64],[-54,64],[-38,65],[-40,65],[-57,65],[-49,66],[-56,66],[-60,66],[-6,67],[-10,67],[-15,67],[-39,67],[-68,16,17,50],[-16,68],[-17,68],[-50,68],[-18,69],[-25,69],[-26,69],[-34,69],[-23,70],[-24,70],[-37,70],[-51,70],[-58,70],[-27,71],[-33,71],[-55,71],[-43,72],[-59,72],[-63,73],[-62,73],[-73,74],[-61,74],[-66,75],[-65,75],[-75,76],[-64,76],[-64,-75,77],[-76,78],[-74,78],[-74,-77,79],[-69,80],[-68,80],[-68,-69,81],[-80,82],[-81,83],[-67,-80,83],[-67,-81,84],[-72,85],[-71,85],[-85,86],[-70,86],[-82,-86,87],[-83,87],[-83,-86,88],[-84,88],[-88,89],[-78,-87,89],[-79,89],[-89],[2,6,11,15,17,19,21,23,27,29,31,32,33,34,37,43,49,50,51,55,58,59,60],[4,7,13,16,17,24,27,33,34,35,38,41,43,45,47,48,49,50,53,56,58,59,60],[1,5,8,12,15,18,20,22,28,30,31,34,39,44,50,52],[3,5,9,14,16,18,25,28,34,36,42,44,46,47,50,54],[5,10,17,18,26,27,28,33,34,40,43,44,49,50,57,58,59,60]],\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":77,\"b\":68},{\"tag\":\"incompatible\",\"a\":107,\"b\":64},{\"tag\":\"incompatible\",\"a\":107,\"b\":76},{\"tag\":\"mate\",\"ridge\":385,\"a\":16,\"owners\":[52,55,58,77,78,81]},{\"tag\":\"mate\",\"ridge\":385,\"a\":45,\"owners\":[77,78,81]},{\"tag\":\"mate\",\"ridge\":385,\"a\":65,\"owners\":[52,55,58,81]},{\"tag\":\"mate\",\"ridge\":385,\"a\":69,\"owners\":[55,58,78,81]},{\"tag\":\"mate\",\"ridge\":388,\"a\":16,\"owners\":[34,93,98,107]},{\"tag\":\"mate\",\"ridge\":388,\"a\":45,\"owners\":[34,107]},{\"tag\":\"mate\",\"ridge\":388,\"a\":65,\"owners\":[34,93,98]},{\"tag\":\"mate\",\"ridge\":388,\"a\":69,\"owners\":[34,98]},{\"tag\":\"mate\",\"ridge\":321,\"a\":21,\"owners\":[43,55,57,64,70,74,78,80,81]},{\"tag\":\"mate\",\"ridge\":321,\"a\":51,\"owners\":[64,70,74,78,80,81]},{\"tag\":\"mate\",\"ridge\":321,\"a\":79,\"owners\":[43,55,57,64,74,78,81]},{\"tag\":\"mate\",\"ridge\":642,\"a\":27,\"owners\":[54,56,58,100,101,104]},{\"tag\":\"mate\",\"ridge\":642,\"a\":46,\"owners\":[100,101,104]},{\"tag\":\"mate\",\"ridge\":642,\"a\":96,\"owners\":[56,58,101,104]},{\"tag\":\"mate\",\"ridge\":642,\"a\":98,\"owners\":[54,56,100,101]},{\"tag\":\"mate\",\"ridge\":644,\"a\":88,\"owners\":[34,72,75]},{\"tag\":\"mate\",\"ridge\":578,\"a\":53,\"owners\":[87,92,97,101,103,104]},{\"tag\":\"mate\",\"ridge\":578,\"a\":56,\"owners\":[32,87,92,95,97,99,102,103]},{\"tag\":\"mate\",\"ridge\":578,\"a\":95,\"owners\":[56,57,101,103,104]},{\"tag\":\"mate\",\"ridge\":608,\"a\":32,\"owners\":[71,80,108,111,114,115]},{\"tag\":\"mate\",\"ridge\":608,\"a\":53,\"owners\":[108,111,114,115]},{\"tag\":\"mate\",\"ridge\":608,\"a\":95,\"owners\":[80,115]},{\"tag\":\"mate\",\"ridge\":608,\"a\":99,\"owners\":[71,80,111,114,115]},{\"tag\":\"mate\",\"ridge\":608,\"a\":102,\"owners\":[71,80,108,114]},{\"tag\":\"mate\",\"ridge\":772,\"a\":113,\"owners\":[34,47,73,75,98]},{\"tag\":\"mate\",\"ridge\":896,\"a\":34,\"owners\":[58,81,104]},{\"tag\":\"mate\",\"ridge\":896,\"a\":75,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":896,\"a\":98,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":581,\"a\":44,\"owners\":[71,74]},{\"tag\":\"mate\",\"ridge\":771,\"a\":47,\"owners\":[57,58]},{\"tag\":\"mate\",\"ridge\":771,\"a\":57,\"owners\":[47,58]},{\"tag\":\"mate\",\"ridge\":771,\"a\":58,\"owners\":[47,57]},{\"tag\":\"mate\",\"ridge\":402,\"a\":52,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":402,\"a\":93,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":673,\"a\":54,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":450,\"a\":55,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":450,\"a\":104,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":705,\"a\":56,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":705,\"a\":81,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":832,\"a\":57,\"owners\":[113,114,115]},{\"tag\":\"mate\",\"ridge\":832,\"a\":74,\"owners\":[103,104,115]},{\"tag\":\"mate\",\"ridge\":832,\"a\":81,\"owners\":[97,103,113,114,115]},{\"tag\":\"mate\",\"ridge\":832,\"a\":97,\"owners\":[80,81,115]},{\"tag\":\"mate\",\"ridge\":832,\"a\":103,\"owners\":[74,80,81,114]},{\"tag\":\"mate\",\"ridge\":832,\"a\":104,\"owners\":[74,80,113,114,115]},{\"tag\":\"mate\",\"ridge\":832,\"a\":114,\"owners\":[57,81,103,104]},{\"tag\":\"mate\",\"ridge\":832,\"a\":115,\"owners\":[57,74,81,97,104]},{\"tag\":\"mate\",\"ridge\":801,\"a\":80,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":408,\"a\":77,\"owners\":[107]},{\"tag\":\"mate\",\"ridge\":408,\"a\":107,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":456,\"a\":78,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":588,\"a\":108,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":596,\"a\":113,\"owners\":[92,111]},{\"tag\":\"mate\",\"ridge\":680,\"a\":100,\"owners\":[109]},{\"tag\":\"mate\",\"ridge\":680,\"a\":109,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":712,\"a\":101,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":77,\"full_literals\":[-30,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-35,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":52,\"full_literals\":[-12,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":107,\"full_literals\":[-52,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":54,\"full_literals\":[-14,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":109,\"full_literals\":[-54,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":92,\"full_literals\":[-38,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":94,\"full_literals\":[-40,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":112,\"full_literals\":[-57,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":103,\"full_literals\":[-49,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":111,\"full_literals\":[-56,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":115,\"full_literals\":[-60,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":43,\"full_literals\":[-6,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":47,\"full_literals\":[-10,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":55,\"full_literals\":[-15,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":93,\"full_literals\":[-39,67]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[56,57,104],\"full_literals\":[-68,16,17,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":56,\"full_literals\":[-16,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":57,\"full_literals\":[-17,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":104,\"full_literals\":[-50,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":58,\"full_literals\":[-18,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":72,\"full_literals\":[-25,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":73,\"full_literals\":[-26,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":81,\"full_literals\":[-34,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":70,\"full_literals\":[-23,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":71,\"full_literals\":[-24,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":91,\"full_literals\":[-37,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":106,\"full_literals\":[-51,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":113,\"full_literals\":[-58,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":74,\"full_literals\":[-27,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":80,\"full_literals\":[-33,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":110,\"full_literals\":[-55,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":97,\"full_literals\":[-43,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":114,\"full_literals\":[-59,72]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-73,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-75,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-76,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-74,-77,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-69,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-80,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-81,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-67,-80,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-67,-81,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-85,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-82,-86,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-83,false,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-83,-86,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-84,false,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-88,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-78,-87,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-79,false,89],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[21,43,51,55,57,64,68,70,74,76,78,79,80,81,91,97,103,104,106,110,113,114,115]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[32,44,53,56,57,71,74,80,81,87,92,95,97,99,101,102,103,104,108,111,113,114,115]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[16,34,45,52,55,58,65,69,75,77,78,81,93,98,104,107]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[27,34,46,54,56,58,72,75,81,88,96,98,100,101,104,109]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[34,47,57,58,73,74,75,80,81,94,97,98,103,104,112,113,114,115]}]}"
  "130 -88 0 124 121 0\n131 -79 0 124 123 0\n132 -84 0 130 120 0\n133 2 6 11 15 17 19 21 23 27 29 32 33 34 37 43 49 50 51 55 58 59 60 0 54 125 0\n134 4 7 13 16 17 24 27 33 34 35 38 41 43 45 48 49 50 53 56 58 59 60 0 59 126 0\n135 1 5 8 12 15 18 20 22 28 30 34 39 44 50 52 0 54 127 0\n136 3 5 9 14 16 18 25 28 34 36 42 44 46 50 54 0 59 128 0\n137 80 74 0 54 96 94 62 37 63 97 60 106 107 80 83 79 29 31 5 30 39 8 10 11 135 0\n138 50 69 74 0 54 97 60 83 5 31 80 96 94 62 37 63 30 39 29 7 4 6 135 0\n139 69 78 0 130 104 137 103 100 99 66 98 70 56 71 82 51 138 40 74 111 119 115 113 114 93 89 48 0\n140 -50 -69 0 132 40 79 74 108 112 0\n141 -67 78 0 132 130 59 103 100 98 71 69 139 140 44 104 137 96 95 61 55 99 66 70 56 111 112 119 108 115 116 77 78 113 114 85 42 49 22 92 90 23 27 32 24 26 134 0\n142 68 78 0 59 54 141 73 139 140 39 30 104 96 94 62 37 63 103 101 65 57 97 60 64 77 78 42 18 35 5 29 7 4 6 135 0\n143 78 0 130 59 103 104 100 96 98 99 95 69 70 71 66 61 56 55 139 140 44 142 108 110 119 115 116 113 114 85 92 93 90 23 27 32 26 45 20 43 25 21 134 0\n144 -87 0 143 124 122 0\n145 -83 0 144 118 0\n146 -81 0 145 110 0\n147 -68 50 0 146 145 107 108 111 80 83 73 34 41 76 0\n148 52 39 18 50 0 54 147 77 42 31 29 10 36 39 7 30 52 8 9 135 0\n149 46 25 18 50 0 59 30 147 77 42 29 19 38 17 31 58 16 15 136 0\n150 69 18 50 0 131 147 78 33 77 42 29 31 30 81 82 138 51 28 105 149 57 65 102 98 99 69 71 67 68 44 49 46 129 0\n151 18 50 0 145 144 54 147 77 42 78 39 150 106 109 111 117 72 75 115 116 148 113 114 84 86 87 88 2 3 53 92 93 89 90 91 13 12 1 47 50 14 133 0\n152 -18 17 0 145 35 80 73 106 111 0\n153 50 0 147 78 151 152 0\n154 15 0 153 40 0\n155 68 0 153 79 0\n156 67 0 154 74 0\n157 80 0 155 107 0\n158 0 156 157 145 111 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9707cf0b525cb4a5aa5a1e9c6699662d8762b86ef07a1d4731ac571d2729aa5698e479b15c569565a56552d475a364d2b46d87783d0ec370d63c4e9394d534ccb31cf0ba2e4b52d2b2ac6b86d8751cc749c6725c8f9605c0f1a21683a298560d84e0b81ee0741686519261916439294550d44d0b41d60d4348ca314c3312c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "49b6da4d34924936d36d26d369269249349b4924da492492492249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008.data.quota

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":107}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record008" 29

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record008" "{\"ridges\":[[22,521],[23,577],[26,577],[27,641],[39,584],[53,650],[60,658],[64,577],[64,706],[66,896],[67,521],[70,577],[71,652],[75,660],[79,708],[81,521],[83,680],[84,808],[87,688],[90,641],[91,896],[105,706],[105,832],[107,584]],\"owners\":[[22,521,[23,52,53,54,70,71,83,84,85],[47,67,81]],[67,521,[23,52,53,54,83,84,85],[22,47,70,71,81]],[81,521,[23,52,53,54,70,71,85],[22,47,67,83,84]],[39,584,[23,52,70,85,102],[100,107]],[107,584,[23,52,85,102],[39,70,100]],[105,832,[26,85,89],[65,91,102,104]],[27,641,[53,60,64,71,75,79,83,87],[66,90,91]],[90,641,[53,60,64,71,75,79],[27,66,83,87,91]],[66,896,[],[27,90,91,105]],[91,896,[],[27,66,90,105]],[53,650,[],[]],[60,658,[],[]],[64,706,[105],[]],[105,706,[64],[]],[71,652,[],[]],[75,660,[],[]],[79,708,[],[]],[83,680,[],[]],[84,808,[],[]],[87,688,[],[]]],\"edges\":[[29,[22,23,39,47,52,53,54,67,70,71,81,83,84,85,100,102,107]],[43,[27,53,60,64,66,71,75,79,83,87,90,91,105]]],\"groupings\":[]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-6],[-11,-7],[-11,-9],[-21,-11],[-23,-11],[-26,-11],[-27,-11],[-1,2,7,8,9,14,15,19,20,21],[-13,2,7,8,9,19,20,21],[-18,2,7,8,9,14,15,21],[-2,-3,-11],[-3,-11,-14],[-5,2,7,14,21,27],[-29,2,7,21,27],[-28,3,21,23],[-4,8,10,11,15,16,17,19,22],[-24,8,10,11,15,16,17],[-12],[-25],[-8],[-10],[-11,28],[-28,11],[-15],[-16],[-17],[-19],[-20],[-22],[1,2,5,6,7,8,9,13,14,15,18,19,20,21,26,27,29],[4,8,10,11,12,15,16,17,19,22,24,25,28]],\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":107}],\"rules\":[{\"tag\":\"incompatible\",\"a\":64,\"b\":47},{\"tag\":\"incompatible\",\"a\":64,\"b\":52},{\"tag\":\"incompatible\",\"a\":64,\"b\":54},{\"tag\":\"incompatible\",\"a\":85,\"b\":64},{\"tag\":\"incompatible\",\"a\":89,\"b\":64},{\"tag\":\"incompatible\",\"a\":100,\"b\":64},{\"tag\":\"incompatible\",\"a\":102,\"b\":64},{\"tag\":\"mate\",\"ridge\":521,\"a\":22,\"owners\":[23,52,53,54,70,71,83,84,85]},{\"tag\":\"mate\",\"ridge\":521,\"a\":67,\"owners\":[23,52,53,54,83,84,85]},{\"tag\":\"mate\",\"ridge\":521,\"a\":81,\"owners\":[23,52,53,54,70,71,85]},{\"tag\":\"three\",\"ridge\":577,\"vertices\":[23,26,64]},{\"tag\":\"three\",\"ridge\":577,\"vertices\":[26,64,70]},{\"tag\":\"mate\",\"ridge\":584,\"a\":39,\"owners\":[23,52,70,85,102]},{\"tag\":\"mate\",\"ridge\":584,\"a\":107,\"owners\":[23,52,85,102]},{\"tag\":\"mate\",\"ridge\":832,\"a\":105,\"owners\":[26,85,89]},{\"tag\":\"mate\",\"ridge\":641,\"a\":27,\"owners\":[53,60,64,71,75,79,83,87]},{\"tag\":\"mate\",\"ridge\":641,\"a\":90,\"owners\":[53,60,64,71,75,79]},{\"tag\":\"mate\",\"ridge\":896,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":896,\"a\":91,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":650,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":658,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":706,\"a\":64,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":706,\"a\":105,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":652,\"a\":71,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":660,\"a\":75,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":708,\"a\":79,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":680,\"a\":83,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":808,\"a\":84,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":688,\"a\":87,\"owners\":[]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[22,23,39,47,52,53,54,67,70,71,81,83,84,85,100,102,107]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[27,53,60,64,66,71,75,79,83,87,90,91,105]}]}"
  "32 1 2 5 6 7 9 13 14 18 21 26 27 29 0 20 24 27 28 30 0\n33 4 11 24 28 0 20 21 18 24 25 26 27 29 19 31 0\n34 11 0 29 27 26 25 24 21 20 16 17 23 33 0\n35 -6 0 34 1 0\n36 -7 0 34 2 0\n37 -9 0 34 3 0\n38 -21 0 34 4 0\n39 -23 0 34 5 0\n40 -26 0 34 6 0\n41 -27 0 34 7 0\n42 28 0 34 22 0\n43 3 0 42 38 39 15 0\n44 -2 0 43 34 11 0\n45 -14 0 43 34 12 0\n46 -1 0 44 36 20 37 45 24 27 28 38 8 0\n47 -13 0 44 36 20 37 27 28 38 9 0\n48 -18 0 44 36 20 37 45 24 38 10 0\n49 -5 0 44 36 45 38 41 13 0\n50 -29 0 44 36 38 41 14 0\n51 0 46 44 49 35 36 37 47 45 48 38 40 41 50 32 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record015
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f0ea398ae0f89d0f46b0ec670dc2f07cf0ba2b8b92b4ab29c8f2e2b2aaa9aa3ab1aa699a36a3a2e87ad1b2699b1695a361d92e1b91e1783ef07a1b8791b46b19c4f16a4e9664d92e479715a539595354b51d58d3352d2b46d4749d1743de0f43b0dc3c8ea368e6338f13a4d9394cd38ccb31cd8b32d2b2ac6b46c9b16c3b51d2745c3713ee0b4262948661590e0b81e384d1624a9264651550d0b41d18c5342c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9b6db6db6db4d34db6db6db6db4d349249b4d36924936d34d26924926db6da4db49b49a492492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 96), (facetIndex 98), (facetIndex 100), (facetIndex 101)]))
 (.branch 2
 (.leaf ([(facetIndex 67), (facetIndex 70), (facetIndex 72), (facetIndex 74), (facetIndex 75)]))
 (.leaf ([(facetIndex 104), (facetIndex 107), (facetIndex 108), (facetIndex 112)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 123), (facetIndex 124), (facetIndex 125), (facetIndex 127)]))
 (.leaf ([(facetIndex 76), (facetIndex 126), (facetIndex 128)])))
 (.branch 6
 (.leaf ([(facetIndex 111), (facetIndex 131), (facetIndex 132), (facetIndex 133)]))
 (.leaf ([(facetIndex 45), (facetIndex 49), (facetIndex 50), (facetIndex 55), (facetIndex 58)])))))
 (.branch 10
 (.branch 8
 (.leaf ([(facetIndex 54), (facetIndex 83), (facetIndex 86), (facetIndex 88), (facetIndex 89)]))
 (.branch 9
 (.leaf ([(facetIndex 41), (facetIndex 44), (facetIndex 48), (facetIndex 53), (facetIndex 56), (facetIndex 57), (facetIndex 113)]))
 (.leaf ([(facetIndex 59), (facetIndex 103), (facetIndex 105), (facetIndex 106), (facetIndex 110), (facetIndex 121)]))))
 (.branch 12
 (.branch 11
 (.leaf ([(facetIndex 84), (facetIndex 102), (facetIndex 114), (facetIndex 129)]))
 (.leaf ([(facetIndex 109), (facetIndex 116), (facetIndex 122)])))
 (.branch 13
 (.leaf ([(facetIndex 130)]))
 (.leaf ([(facetIndex 118), (facetIndex 120)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "555ca434333b9d0d0b0a8259b229929a00000000000077070a7000000411010100100000009688678006680068008z29;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 14
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4, 5, 6]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [1, 2]
def grouped3_0006 : List Nat := [2]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [3, 4, 5, 6]
def grouped3_0009 : List Nat := [5]
def grouped3_0010 : List Nat := [5, 6]
def grouped3_0011 : List Nat := [6]
def grouped3_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [7, 8, 9]
def grouped3_0014 : List Nat := [7, 8, 9, 10, 11, 12, 13]
def grouped3_0015 : List Nat := [8]
def grouped3_0016 : List Nat := [8, 9]
def grouped3_0017 : List Nat := [9]
def grouped3_0018 : List Nat := [10, 11]
def grouped3_0019 : List Nat := [10, 11, 12, 13]
def grouped3_0020 : List Nat := [12]
def grouped3_0021 : List Nat := [12, 13]
def grouped3_0022 : List Nat := [13]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record015" "{\"atoms\":[{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"facet\",\"index\":132},{\"tag\":\"facet\",\"index\":133},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":13},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record015" 43

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record015" "{\"ridges\":[[50,770],[50,785],[55,770],[55,801],[58,770],[58,833],[59,770],[59,896],[86,785],[88,801],[89,833],[98,788],[100,804],[101,836],[108,770],[108,792],[112,770],[112,808],[113,770],[113,896],[118,402],[118,896],[120,418],[120,896],[121,770],[121,896],[132,792],[132,896],[133,808],[133,896]],\"owners\":[[118,402,[48,106],[]],[50,770,[100,101,112,113,120,121],[55,58,59,98,108,118]],[55,770,[98,101,108,113,118,121],[50,58,59,100,112,120]],[58,770,[98,100,108,112,113,118,120],[50,55,59,101,121]],[59,770,[98,100,101,108,112],[50,55,58,113,118,120,121]],[108,770,[55,58,59,100,101,120,121],[50,98,112,113,118]],[112,770,[50,58,59,98,101,118,121],[55,100,108,113,120]],[113,770,[50,55,58,98,100,101],[59,108,112,118,120,121]],[121,770,[50,55,98,100,108,112],[58,59,101,113,118,120]],[50,785,[86],[]],[86,785,[50],[]],[120,418,[53,110],[]],[55,801,[88],[]],[88,801,[55],[]],[58,833,[89],[]],[89,833,[58],[]],[59,896,[132,133],[86,88,89,113,118,120,121]],[113,896,[86,88,89],[59,118,120,121,132,133]],[118,896,[88,89,133],[59,86,113,120,121,132]],[120,896,[86,89,132],[59,88,113,118,121,133]],[121,896,[86,88,132,133],[59,89,113,118,120]],[132,896,[59,88,89,120,121],[86,113,118,133]],[133,896,[59,86,89,118,121],[88,113,120,132]],[98,788,[],[]],[100,804,[],[]],[101,836,[],[]],[108,792,[132],[]],[132,792,[108],[]],[112,808,[133],[]],[133,808,[112],[]]],\"edges\":[[44,[50,55,58,59,86,88,89,98,100,101,108,112,113,118,120,121,132,133]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record015" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record015\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-18,1,13],[-2,11,12,16,17,19,20],[-4,10,12,14,17,18,20],[-5,10,11,14,16,17,18,19],[-6,10,11,12,14,16],[-14,4,5,6,11,12,19,20],[-16,2,5,6,10,12,18,20],[-17,2,4,5,10,11,12],[-20,2,4,10,11,14,16],[-2,7],[-7,2],[-19,3,15],[-4,8],[-8,4],[-5,9],[-9,5],[-6,21,22],[-17,7,8,9],[-18,8,9,22],[-19,7,9,21],[-20,7,8,21,22],[-21,6,8,9,19,20],[-22,6,7,9,18,20],[-10],[-11],[-12],[-14,21],[-21,14],[-16,22],[-22,16],[-14,23],[-16,23],[-21,24],[-22,24],[-2,25],[-4,25],[-5,25],[-7,26],[-8,26],[-9,26],[-1,27],[-3,27],[-17,27],[-6,28],[-13,28],[-15,28],[-20,28],[-18,29],[-19,29],[-23,30],[-30,31],[-25,32],[-24,32],[-32,33],[-33,34],[-31,34],[-31,-33,35],[-28,36],[-27,36],[-36,37],[-26,37],[-26,-36,38],[-29,39],[-39,40],[-37,41],[-37,-40,42],[-38,42],[-34,-42,43],[-35,-41,43],[-43],[2,4,5,6,7,8,9,10,11,12,14,16,17,18,19,20,21,22]],\"atoms\":[{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"facet\",\"index\":132},{\"tag\":\"facet\",\"index\":133},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":13,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":402,\"a\":118,\"owners\":[48,106]},{\"tag\":\"mate\",\"ridge\":770,\"a\":50,\"owners\":[100,101,112,113,120,121]},{\"tag\":\"mate\",\"ridge\":770,\"a\":55,\"owners\":[98,101,108,113,118,121]},{\"tag\":\"mate\",\"ridge\":770,\"a\":58,\"owners\":[98,100,108,112,113,118,120]},{\"tag\":\"mate\",\"ridge\":770,\"a\":59,\"owners\":[98,100,101,108,112]},{\"tag\":\"mate\",\"ridge\":770,\"a\":108,\"owners\":[55,58,59,100,101,120,121]},{\"tag\":\"mate\",\"ridge\":770,\"a\":112,\"owners\":[50,58,59,98,101,118,121]},{\"tag\":\"mate\",\"ridge\":770,\"a\":113,\"owners\":[50,55,58,98,100,101]},{\"tag\":\"mate\",\"ridge\":770,\"a\":121,\"owners\":[50,55,98,100,108,112]},{\"tag\":\"mate\",\"ridge\":785,\"a\":50,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":785,\"a\":86,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":418,\"a\":120,\"owners\":[53,110]},{\"tag\":\"mate\",\"ridge\":801,\"a\":55,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":801,\"a\":88,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":833,\"a\":58,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":833,\"a\":89,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":896,\"a\":59,\"owners\":[132,133]},{\"tag\":\"mate\",\"ridge\":896,\"a\":113,\"owners\":[86,88,89]},{\"tag\":\"mate\",\"ridge\":896,\"a\":118,\"owners\":[88,89,133]},{\"tag\":\"mate\",\"ridge\":896,\"a\":120,\"owners\":[86,89,132]},{\"tag\":\"mate\",\"ridge\":896,\"a\":121,\"owners\":[86,88,132,133]},{\"tag\":\"mate\",\"ridge\":896,\"a\":132,\"owners\":[59,88,89,120,121]},{\"tag\":\"mate\",\"ridge\":896,\"a\":133,\"owners\":[59,86,89,118,121]},{\"tag\":\"mate\",\"ridge\":788,\"a\":98,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":804,\"a\":100,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":836,\"a\":101,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":792,\"a\":108,\"owners\":[132]},{\"tag\":\"mate\",\"ridge\":792,\"a\":132,\"owners\":[108]},{\"tag\":\"mate\",\"ridge\":808,\"a\":112,\"owners\":[133]},{\"tag\":\"mate\",\"ridge\":808,\"a\":133,\"owners\":[112]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":108,\"full_literals\":[-14,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":112,\"full_literals\":[-16,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":132,\"full_literals\":[-21,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":133,\"full_literals\":[-22,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":50,\"full_literals\":[-2,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":55,\"full_literals\":[-4,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":58,\"full_literals\":[-5,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-7,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":88,\"full_literals\":[-8,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":89,\"full_literals\":[-9,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":48,\"full_literals\":[-1,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":53,\"full_literals\":[-3,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":113,\"full_literals\":[-17,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":59,\"full_literals\":[-6,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":106,\"full_literals\":[-13,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":110,\"full_literals\":[-15,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":121,\"full_literals\":[-20,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":13,\"member\":118,\"full_literals\":[-18,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":13,\"member\":120,\"full_literals\":[-19,29]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-23,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-25,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-24,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-33,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-26,-36,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7,8,9],\"right\":[10,11,12,13],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7,8,9],\"right\":[10,11,12,13],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-37,-40,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7,8,9],\"right\":[10,11,12,13],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6],\"right\":[7,8,9,10,11,12,13],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-34,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6],\"right\":[7,8,9,10,11,12,13],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-35,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":44,\"owners\":[50,55,58,59,86,88,89,98,100,101,108,112,113,118,120,121,132,133]}]}"
  "72 2 4 5 6 7 8 9 14 16 17 18 19 20 21 22 0 24 25 26 71 0\n73 34 0 26 25 24 55 56 54 51 52 53 50 35 36 37 33 34 31 32 11 14 16 8 17 21 20 19 72 0\n74 -42 0 73 70 68 0\n75 -38 0 74 67 0\n76 37 0 24 26 25 60 61 58 59 38 39 40 44 45 46 47 41 42 43 10 13 15 1 12 7 23 6 22 72 0\n77 41 0 76 65 0\n78 -40 0 76 74 66 0\n79 -35 0 77 70 69 0\n80 -39 0 78 64 0\n81 -29 0 80 63 0\n82 -18 0 81 48 0\n83 -19 0 81 49 0\n84 32 36 0 24 26 25 82 83 59 43 58 47 44 52 53 35 36 37 33 34 11 14 16 7 6 72 0\n85 36 0 79 24 26 25 82 83 58 59 44 47 43 84 54 57 51 50 31 32 4 3 28 2 30 16 14 11 72 0\n86 -26 0 85 75 62 0\n87 -7 0 86 38 0\n88 -8 0 86 39 0\n89 -9 0 86 40 0\n90 -2 0 87 10 0\n91 -4 0 88 13 0\n92 -5 0 89 15 0\n93 -17 0 89 87 88 18 0\n94 14 16 0 92 90 87 88 89 91 93 83 82 24 25 26 5 28 9 30 72 0\n95 23 0 31 32 94 0\n96 30 0 95 50 0\n97 31 0 96 51 0\n98 -33 0 97 79 57 0\n99 -32 0 98 54 0\n100 -24 0 99 53 0\n101 -21 0 100 33 0\n102 -22 0 100 34 0\n103 -6 0 101 102 17 0\n104 -14 0 101 27 0\n105 -20 0 101 87 88 102 21 0\n106 -16 0 102 29 0\n107 0 102 106 92 90 87 88 89 91 101 93 103 83 105 82 104 72 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record016
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f0ea398ae0f89d0f46b0ec670dc2f07c9c8f26a8ea668da2e87a1d92e1b91e1783ef07a1e46b19c4f1e2729aa5a93a719a6599366392e479d15c5c95a5994e5c5595954d58d4b51d58d3352d2b46d4749d1743dd0dc3c8da398ce3c4d9394cd38ccb31cd8b32d2b2ac6b46c9b16c3b51d2745c3713ee0b40661590e0b81ee06c1a866138691944d1624a9264651550d0b41d18c5342c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9b6db6db6db6db6d24924924934934934db6d26d26d26924926db49b49b49a492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37)]))
 (.leaf ([(facetIndex 100), (facetIndex 101), (facetIndex 102), (facetIndex 103), (facetIndex 104)])))
 (.branch 3
 (.leaf ([(facetIndex 39), (facetIndex 50), (facetIndex 51), (facetIndex 61), (facetIndex 72), (facetIndex 73), (facetIndex 85)]))
 (.leaf ([(facetIndex 42), (facetIndex 54), (facetIndex 55), (facetIndex 64), (facetIndex 76), (facetIndex 77), (facetIndex 89)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 87), (facetIndex 91), (facetIndex 93), (facetIndex 96), (facetIndex 97), (facetIndex 98), (facetIndex 99)]))
 (.leaf ([(facetIndex 38), (facetIndex 47), (facetIndex 60), (facetIndex 69), (facetIndex 83), (facetIndex 94), (facetIndex 95), (facetIndex 105), (facetIndex 126)])))
 (.branch 7
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 43), (facetIndex 44), (facetIndex 46)]))
 (.branch 8
 (.leaf ([(facetIndex 62), (facetIndex 63), (facetIndex 65), (facetIndex 66), (facetIndex 68)]))
 (.leaf ([(facetIndex 86), (facetIndex 90)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5z14;51111144445540483048205000003300220057077377250000330022005606636625z26;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 58), (facetIndex 59), (facetIndex 80), (facetIndex 81)]))
 (.leaf ([(facetIndex 52), (facetIndex 53), (facetIndex 74), (facetIndex 75), (facetIndex 88)])))
 (.branch 3
 (.leaf ([(facetIndex 84), (facetIndex 92), (facetIndex 124)]))
 (.branch 4
 (.leaf ([(facetIndex 56), (facetIndex 57), (facetIndex 78), (facetIndex 79), (facetIndex 125)]))
 (.leaf ([(facetIndex 45), (facetIndex 48), (facetIndex 109), (facetIndex 111)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 67), (facetIndex 82), (facetIndex 108)]))
 (.leaf ([(facetIndex 106), (facetIndex 110), (facetIndex 116)])))
 (.branch 8
 (.leaf ([(facetIndex 49), (facetIndex 70), (facetIndex 71), (facetIndex 107), (facetIndex 114), (facetIndex 123)]))
 (.branch 9
 (.leaf ([(facetIndex 112), (facetIndex 113), (facetIndex 115), (facetIndex 121), (facetIndex 122)]))
 (.leaf ([(facetIndex 117), (facetIndex 118), (facetIndex 119), (facetIndex 120)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "327889999687884645760000000000000200010002050033001100770050000000003300110074004z2d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4, 5]
def grouped2_0003 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0004 : List Nat := [6]
def grouped2_0005 : List Nat := [6, 7, 8]
def grouped2_0006 : List Nat := [7]
def grouped2_0007 : List Nat := [7, 8]
def grouped2_0008 : List Nat := [8]
def grouped3_0009 : List Nat := [0]
def grouped3_0010 : List Nat := [0, 1]
def grouped3_0011 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0013 : List Nat := [1]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [2, 3, 4]
def grouped3_0016 : List Nat := [3]
def grouped3_0017 : List Nat := [3, 4]
def grouped3_0018 : List Nat := [4]
def grouped3_0019 : List Nat := [5]
def grouped3_0020 : List Nat := [5, 6]
def grouped3_0021 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0022 : List Nat := [6]
def grouped3_0023 : List Nat := [7]
def grouped3_0024 : List Nat := [7, 8, 9]
def grouped3_0025 : List Nat := [8]
def grouped3_0026 : List Nat := [8, 9]
def grouped3_0027 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record016" "{\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":122},{\"tag\":\"facet\",\"index\":123},{\"tag\":\"facet\",\"index\":124},{\"tag\":\"facet\",\"index\":125},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record016" 70

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record016" "{\"ridges\":[[17,265],[25,769],[25,896],[40,152],[41,265],[43,168],[53,786],[57,802],[59,834],[75,788],[79,804],[81,836],[84,568],[86,152],[88,792],[90,168],[92,265],[92,808],[93,896],[97,769],[98,769],[98,896],[99,769],[99,896],[124,792],[125,392],[125,808]],\"owners\":[[40,152,[115,116,117,122,123,124],[15,62,83,85,86,87,107,108,109]],[86,152,[107,108,115,116,122,123],[15,40,62,83,85,87,109,117,124]],[43,168,[115,118,119,122,123,125],[16,65,83,89,90,91,107,110,111]],[90,168,[107,110,115,118,122,123],[16,43,65,83,89,91,111,119,125]],[125,392,[17,46,68,86,109,117],[90,93,111,119,124]],[25,769,[53,57,59,75,79,81,88,92],[93,97,98,99]],[97,769,[57,59,79,81,92],[25,53,75,88,93,98,99]],[98,769,[53,59,75,81,88],[25,57,79,92,93,97,99]],[99,769,[53,57,75,79,88,92],[25,59,81,93,97,98]],[25,896,[124,125],[93,97,98,99]],[93,896,[],[25,97,98,99,124,125]],[98,896,[124],[25,93,97,99,125]],[99,896,[124,125],[25,93,97,98]],[53,786,[],[]],[57,802,[],[]],[59,834,[],[]],[75,788,[],[]],[79,804,[],[]],[81,836,[],[]],[84,568,[123],[]],[88,792,[124],[]],[124,792,[88],[]],[92,808,[125],[]],[125,808,[92],[]]],\"edges\":[[44,[25,53,57,59,75,79,81,88,92,93,97,98,99,124,125]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record016" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record016\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-6],[-14,-6],[-21,-3],[-21,-7],[-21,-11],[-21,-15],[-23,-5],[-23,-7],[-23,-15],[-23,-19],[-39,-4],[-39,-12],[-40,-6],[-40,-39],[-1,-4,-23],[-3,32,33,34,37,38,39],[-20,28,29,32,33,37,38],[-5,32,35,36,37,38,40],[-22,28,31,32,35,37,38],[-40,1,7,15,20,30,34],[-2,8,9,10,16,17,18,21,23],[-25,9,10,17,18,23],[-26,8,10,16,18,21],[-27,8,9,16,17,21,23],[-2,39,40],[-24],[-26,39],[-27,39,40],[-8],[-9],[-10],[-16],[-17],[-18],[-19,38],[-21,39],[-39,21],[-23,40],[-40,23],[-41,3,4,5,6,7],[-42,11,12,13,14,15],[-43,20,22],[-44,42,43],[-45,43],[-46,41,45],[-46,44],[-47,46],[-48,47],[48],[-21,49],[-50,19,23,39],[-23,50],[-39,50],[-40,51],[-30,52],[-29,53],[-31,54],[-33,54],[-28,55],[-38,55],[-32,56],[-37,56],[-34,57],[-35,57],[-36,57],[-49,58],[-51,59],[-51,-52,60],[-61,50,59],[-59,61],[-50,61],[-50,-59,62],[-50,-60,63],[-62,64],[-63,65],[-58,-61,64],[-54,66],[-53,66],[-57,67],[-56,67],[-67,68],[-55,68],[-68,69],[-66,69],[-64,-69,70],[-65,70],[-70],[2,8,9,10,16,17,18,21,23,24,25,26,27,39,40]],\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":122},{\"tag\":\"facet\",\"index\":123},{\"tag\":\"facet\",\"index\":124},{\"tag\":\"facet\",\"index\":125},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":65,\"b\":44},{\"tag\":\"incompatible\",\"a\":66,\"b\":44},{\"tag\":\"incompatible\",\"a\":88,\"b\":40},{\"tag\":\"incompatible\",\"a\":88,\"b\":46},{\"tag\":\"incompatible\",\"a\":88,\"b\":62},{\"tag\":\"incompatible\",\"a\":88,\"b\":68},{\"tag\":\"incompatible\",\"a\":92,\"b\":43},{\"tag\":\"incompatible\",\"a\":92,\"b\":46},{\"tag\":\"incompatible\",\"a\":92,\"b\":68},{\"tag\":\"incompatible\",\"a\":92,\"b\":84},{\"tag\":\"incompatible\",\"a\":124,\"b\":41},{\"tag\":\"incompatible\",\"a\":124,\"b\":63},{\"tag\":\"incompatible\",\"a\":125,\"b\":44},{\"tag\":\"incompatible\",\"a\":125,\"b\":124},{\"tag\":\"three\",\"ridge\":265,\"vertices\":[17,41,92]},{\"tag\":\"mate\",\"ridge\":152,\"a\":40,\"owners\":[115,116,117,122,123,124]},{\"tag\":\"mate\",\"ridge\":152,\"a\":86,\"owners\":[107,108,115,116,122,123]},{\"tag\":\"mate\",\"ridge\":168,\"a\":43,\"owners\":[115,118,119,122,123,125]},{\"tag\":\"mate\",\"ridge\":168,\"a\":90,\"owners\":[107,110,115,118,122,123]},{\"tag\":\"mate\",\"ridge\":392,\"a\":125,\"owners\":[17,46,68,86,109,117]},{\"tag\":\"mate\",\"ridge\":769,\"a\":25,\"owners\":[53,57,59,75,79,81,88,92]},{\"tag\":\"mate\",\"ridge\":769,\"a\":97,\"owners\":[57,59,79,81,92]},{\"tag\":\"mate\",\"ridge\":769,\"a\":98,\"owners\":[53,59,75,81,88]},{\"tag\":\"mate\",\"ridge\":769,\"a\":99,\"owners\":[53,57,75,79,88,92]},{\"tag\":\"mate\",\"ridge\":896,\"a\":25,\"owners\":[124,125]},{\"tag\":\"mate\",\"ridge\":896,\"a\":93,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":896,\"a\":98,\"owners\":[124]},{\"tag\":\"mate\",\"ridge\":896,\"a\":99,\"owners\":[124,125]},{\"tag\":\"mate\",\"ridge\":786,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":802,\"a\":57,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":834,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":788,\"a\":75,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":804,\"a\":79,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":836,\"a\":81,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":568,\"a\":84,\"owners\":[123]},{\"tag\":\"mate\",\"ridge\":792,\"a\":88,\"owners\":[124]},{\"tag\":\"mate\",\"ridge\":792,\"a\":124,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":808,\"a\":92,\"owners\":[125]},{\"tag\":\"mate\",\"ridge\":808,\"a\":125,\"owners\":[92]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[40,41,43,44,46],\"full_literals\":[-41,3,4,5,6,7]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[62,63,65,66,68],\"full_literals\":[-42,11,12,13,14,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[86,90],\"full_literals\":[-43,20,22]},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,42,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0005\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,41,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0005\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-48,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":88,\"full_literals\":[-21,49]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[84,92,124],\"full_literals\":[-50,19,23,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":92,\"full_literals\":[-23,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":124,\"full_literals\":[-39,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":125,\"full_literals\":[-40,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":109,\"full_literals\":[-30,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":108,\"full_literals\":[-29,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":110,\"full_literals\":[-31,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":116,\"full_literals\":[-33,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":107,\"full_literals\":[-28,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":123,\"full_literals\":[-38,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":115,\"full_literals\":[-32,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":122,\"full_literals\":[-37,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":117,\"full_literals\":[-34,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":118,\"full_literals\":[-35,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":119,\"full_literals\":[-36,57]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-52,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,50,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-59,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-50,-60,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-61,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":44,\"owners\":[25,53,57,59,75,79,81,88,92,93,97,98,99,124,125]}]}"
  "89 47 0 49 48 0\n90 46 0 89 47 0\n91 44 0 90 46 0\n92 -65 0 87 86 0\n93 -63 0 92 75 0\n94 2 21 23 25 26 27 39 40 0 29 30 31 32 33 34 26 88 0\n95 61 0 34 33 31 30 70 71 67 52 53 54 22 25 27 28 36 94 0\n96 59 19 39 0 95 67 69 54 51 38 0\n97 23 21 0 34 33 32 31 30 29 37 23 22 39 24 21 94 0\n98 64 0 95 74 76 66 50 37 97 10 52 96 72 0\n99 -69 0 98 87 85 0\n100 -68 0 99 83 0\n101 -66 0 99 84 0\n102 -67 0 100 81 0\n103 -55 0 100 82 0\n104 -54 0 101 77 0\n105 -53 0 101 78 0\n106 -57 0 102 79 0\n107 -56 0 102 80 0\n108 -28 0 103 59 0\n109 -38 0 103 60 0\n110 -31 0 104 57 0\n111 -33 0 104 58 0\n112 -29 0 105 56 0\n113 -34 0 106 63 0\n114 -35 0 106 64 0\n115 -36 0 106 65 0\n116 -32 0 107 61 0\n117 -37 0 107 62 0\n118 -19 0 109 35 0\n119 -20 0 116 112 108 111 117 109 17 0\n120 -22 0 116 110 108 114 117 109 19 0\n121 -43 0 119 120 42 0\n122 -45 0 121 44 0\n123 42 0 121 91 43 0\n124 41 0 122 90 45 0\n125 -40 60 0 116 109 117 111 124 113 119 13 14 39 54 16 7 8 9 68 40 55 15 20 0\n126 -50 0 93 116 109 117 115 114 118 124 123 73 125 38 18 51 97 11 12 3 4 5 6 40 1 2 41 0\n127 -23 0 126 52 0\n128 -39 0 126 53 0\n129 21 0 127 97 0\n130 0 129 128 36 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record017
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f43a83e2e4b50f4ab0ec370bc1f3c2e8ae2e4b52b49d23cb8acaaaa6a8ea668da2e87ac5a561db0e8b86e4785e0fbc1e86e1744f16a4e9364b91e6c5a9665394d52d475334ad1b51d2745d0f783d0ec370f23a8da398ce364d5334cb31cd8b32d2b2ac6b26c5b0ef0791e2745c3743c4fb81989926246a46898661582e078e1644d1624a946499194550b41d18d1314d0b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b69b6db6da6db6db6d36da4d24936924926da49a6924936db6d249349a4924d2492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 90), (facetIndex 100), (facetIndex 101), (facetIndex 115)]))
 (.branch 2
 (.leaf ([(facetIndex 93), (facetIndex 105), (facetIndex 106), (facetIndex 117)]))
 (.leaf ([(facetIndex 57), (facetIndex 59), (facetIndex 121)]))))
 (.branch 4
 (.leaf ([(facetIndex 67), (facetIndex 69), (facetIndex 75)]))
 (.branch 5
 (.leaf ([(facetIndex 94), (facetIndex 112), (facetIndex 113)]))
 (.leaf ([(facetIndex 111), (facetIndex 114), (facetIndex 116)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 45), (facetIndex 48), (facetIndex 119)]))
 (.branch 8
 (.leaf ([(facetIndex 38), (facetIndex 55), (facetIndex 56), (facetIndex 73), (facetIndex 84)]))
 (.leaf ([(facetIndex 58), (facetIndex 74), (facetIndex 83)]))))
 (.branch 10
 (.leaf ([(facetIndex 54), (facetIndex 102), (facetIndex 120)]))
 (.branch 11
 (.leaf ([(facetIndex 60), (facetIndex 95), (facetIndex 96), (facetIndex 99), (facetIndex 104), (facetIndex 107)]))
 (.leaf ([(facetIndex 98), (facetIndex 103), (facetIndex 109), (facetIndex 110)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "29601505445bb0a11ab900ab0aa4100000000780000000387000303000000a2827790000060060000007z26;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [1, 2]
def grouped3_0006 : List Nat := [2]
def grouped3_0007 : List Nat := [3, 4, 5]
def grouped3_0008 : List Nat := [6]
def grouped3_0009 : List Nat := [6, 7, 8]
def grouped3_0010 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0011 : List Nat := [7]
def grouped3_0012 : List Nat := [7, 8]
def grouped3_0013 : List Nat := [8]
def grouped3_0014 : List Nat := [9]
def grouped3_0015 : List Nat := [9, 10, 11]
def grouped3_0016 : List Nat := [10]
def grouped3_0017 : List Nat := [10, 11]
def grouped3_0018 : List Nat := [11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record017" "{\"atoms\":[{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record017" 48

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record017" "{\"ridges\":[[38,773],[56,770],[56,801],[59,833],[60,770],[60,896],[83,801],[83,896],[84,833],[84,896],[90,780],[93,788],[101,808],[102,650],[102,896],[106,848],[107,658],[107,896],[109,896],[110,450],[110,896],[120,808],[120,896],[121,848],[121,896]],\"owners\":[[56,770,[90,93,102,106,107,110],[38,59,60,101,109]],[60,770,[90,93,101,106],[38,56,59,102,107,109,110]],[38,773,[],[]],[56,801,[83],[]],[83,801,[56],[]],[110,450,[57,104],[]],[59,833,[84],[]],[84,833,[59],[]],[60,896,[120,121],[83,84,102,107,109,110]],[83,896,[102,107,110,121],[60,84,109,120]],[84,896,[102,107,109,120],[60,83,110,121]],[102,896,[83,84,121],[60,107,109,110,120]],[107,896,[83,84,120],[60,102,109,110,121]],[109,896,[84,121],[60,83,102,107,110,120]],[110,896,[83,120],[60,84,102,107,109,121]],[120,896,[60,84,107,110,121],[83,102,109]],[121,896,[60,83,102,109,120],[84,107,110]],[90,780,[],[]],[93,788,[],[]],[102,650,[100],[]],[101,808,[120],[]],[120,808,[101],[]],[107,658,[105],[]],[106,848,[121],[]],[121,848,[106],[]]],\"edges\":[[44,[38,56,59,60,83,84,90,93,101,102,106,107,109,110,120,121]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record017" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record017\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-2,8,9,12,15,16,18],[-5,8,9,11,15],[-1],[-2,6],[-6,2],[-18,3,13],[-4,7],[-7,4],[-5,19,20],[-6,12,16,18,20],[-7,12,16,17,19],[-12,6,7,20],[-16,6,7,19],[-17,7,20],[-18,6,19],[-19,5,7,16,18,20],[-20,5,6,12,17,19],[-8],[-9],[-12,10],[-11,19],[-19,11],[-16,14],[-15,20],[-20,15],[-10,21],[-11,21],[-14,22],[-15,22],[-3,23],[-4,23],[-20,23],[-2,24],[-7,24],[-6,25],[-12,26],[-19,26],[-5,27],[-13,27],[-16,27],[-17,28],[-18,28],[-23,29],[-22,29],[-22,-23,30],[-29,31],[-30,32],[-21,31],[-21,-30,33],[-31,34],[-32,35],[-33,36],[-25,37],[-24,37],[-24,-25,38],[-37,39],[-38,40],[-28,41],[-27,41],[-27,-28,42],[-41,43],[-42,44],[-26,43],[-26,-41,44],[-43,45],[-44,46],[-39,-43,46],[-39,-44,47],[-40,46],[-47,48],[-34,-46,48],[-35,-45,48],[-36,48],[-48],[1,2,4,5,6,7,8,9,11,12,15,16,17,18,19,20]],\"atoms\":[{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":770,\"a\":56,\"owners\":[90,93,102,106,107,110]},{\"tag\":\"mate\",\"ridge\":770,\"a\":60,\"owners\":[90,93,101,106]},{\"tag\":\"mate\",\"ridge\":773,\"a\":38,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":801,\"a\":56,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":801,\"a\":83,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":450,\"a\":110,\"owners\":[57,104]},{\"tag\":\"mate\",\"ridge\":833,\"a\":59,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":833,\"a\":84,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":896,\"a\":60,\"owners\":[120,121]},{\"tag\":\"mate\",\"ridge\":896,\"a\":83,\"owners\":[102,107,110,121]},{\"tag\":\"mate\",\"ridge\":896,\"a\":84,\"owners\":[102,107,109,120]},{\"tag\":\"mate\",\"ridge\":896,\"a\":102,\"owners\":[83,84,121]},{\"tag\":\"mate\",\"ridge\":896,\"a\":107,\"owners\":[83,84,120]},{\"tag\":\"mate\",\"ridge\":896,\"a\":109,\"owners\":[84,121]},{\"tag\":\"mate\",\"ridge\":896,\"a\":110,\"owners\":[83,120]},{\"tag\":\"mate\",\"ridge\":896,\"a\":120,\"owners\":[60,84,107,110,121]},{\"tag\":\"mate\",\"ridge\":896,\"a\":121,\"owners\":[60,83,102,109,120]},{\"tag\":\"mate\",\"ridge\":780,\"a\":90,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":788,\"a\":93,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":650,\"a\":102,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":808,\"a\":101,\"owners\":[120]},{\"tag\":\"mate\",\"ridge\":808,\"a\":120,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":658,\"a\":107,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":848,\"a\":106,\"owners\":[121]},{\"tag\":\"mate\",\"ridge\":848,\"a\":121,\"owners\":[106]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":100,\"full_literals\":[-10,21]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":101,\"full_literals\":[-11,21]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":105,\"full_literals\":[-14,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":106,\"full_literals\":[-15,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":57,\"full_literals\":[-3,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":59,\"full_literals\":[-4,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":121,\"full_literals\":[-20,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":56,\"full_literals\":[-2,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-7,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":83,\"full_literals\":[-6,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":102,\"full_literals\":[-12,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":120,\"full_literals\":[-19,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":60,\"full_literals\":[-5,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":104,\"full_literals\":[-13,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":107,\"full_literals\":[-16,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":109,\"full_literals\":[-17,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":110,\"full_literals\":[-18,28]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-23,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-22,false,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-22,-23,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-30,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-21,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-21,-30,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0002\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-25,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-24,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-24,-25,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-38,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-28,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-42,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-26,-41,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-43,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-39,-44,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-34,-46,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-35,-45,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":44,\"owners\":[38,56,59,60,83,84,90,93,101,102,106,107,109,110,120,121]}]}"
  "76 -47 0 74 70 0\n77 -36 0 74 73 0\n78 -33 0 77 52 0\n79 2 4 5 6 7 11 12 15 16 17 18 19 20 0 3 18 19 75 0\n80 37 31 0 18 19 46 44 28 23 43 31 8 32 14 48 27 22 29 2 26 20 53 54 35 33 15 79 0\n81 18 31 0 19 18 46 44 28 23 43 31 8 32 14 48 27 22 29 2 26 20 10 1 79 0\n82 31 0 76 46 43 30 80 56 68 62 81 6 42 39 60 0\n83 34 0 82 50 0\n84 -46 0 83 74 71 0\n85 -44 0 84 66 0\n86 -40 0 84 69 0\n87 -38 0 86 57 0\n88 -6 0 87 5 35 33 55 0\n89 -2 0 88 4 0\n90 19 20 5 7 0 88 89 12 14 24 7 21 13 15 79 0\n91 20 5 7 0 85 90 37 64 58 59 42 40 16 0\n92 5 7 0 88 74 78 91 25 32 29 45 47 49 51 26 27 72 20 22 65 17 61 41 58 0\n93 -5 0 85 74 38 59 61 64 65 37 72 9 51 25 32 47 29 45 0\n94 7 0 93 92 0\n95 24 0 94 34 0\n96 37 0 95 54 0\n97 39 0 96 56 0\n98 -43 0 97 84 67 0\n99 -41 0 98 61 0\n100 -26 0 98 63 0\n101 -28 0 99 58 0\n102 -27 0 99 59 0\n103 -12 0 100 36 0\n104 -19 0 100 37 0\n105 -17 0 101 41 0\n106 -16 0 102 40 0\n107 0 103 106 94 105 104 11 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00005.record017
