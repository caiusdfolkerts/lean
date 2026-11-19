module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00032Data
public import GraphInputsRow29Part00032Frames
public import GraphInputsRow29Part00032Leaves
public import GraphInputsRow29Part00032Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010
def vertexColumn : Fields := ⟨10, hexnat% "3b0da338ae2b4ab29c8f0bce8b62e4b4acaaaa9a96ac6a9a56aa6598e6a5956a3a2e2b86e8789e17ba1e4731ac5b1ca6a95a719a65598e5392e565395554d4b52b49d1743de0f23a8da358ce3c4e9364d53c2e8b52e2b4acab1ae1b46c9b16d4731d2729c6745c5723c2f1b312a4a1a2584e079611a4a5194951342d0754344c9312c1b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6d36db49b6d36da4936db6d36db69369249b6d34926d36d24924d2492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨69, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨85, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400602067c00007bf000000", hexnat% "100000002002000000000", 19825569038336, hexnat% "2082080000000000000000000", 246359324098560]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1a0000082323f3f000000", 2594073387512889344, hexnat% "20c0000000000c00000000000", 234187180623265792, hexnat% "204000000000000000", hexnat% "2040000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20c21e0204002f23f3b000000", 2214592512, 270215977642229760, 2594073385365405696]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20c20e0000002e01e0a000000", 19795571376128, hexnat% "204000002010000000", hexnat% "100000080000001000000", 522417556774977536, 2305843011898048512]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "120000082b23f3f000000", 2594073387512889344, hexnat% "20c2000000000400000000000", 234187180623265792, hexnat% "204000000000000000", hexnat% "c0000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "401600007c010162f000000", 2305843011629613056, hexnat% "2000000000000e00000000000", hexnat% "82080000000000000000000", 4612249110114729984, hexnat% "200000020800000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000027c21032b7000000", 4611686022856572928, hexnat% "e0000000000000000000", hexnat% "80000200000020800000000", hexnat% "2000000000000e00000000000", hexnat% "42000000000000400000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40006740f01fae000000", hexnat% "a0000000000000000000", hexnat% "20c2000000000000000000000", hexnat% "200002022010000000", hexnat% "100000080000001000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2828278236188770304, hexnat% "120000080000001000000", 2205801250816, hexnat% "2000000000000e00000000000", hexnat% "204002002000000000", hexnat% "420c0000000000400000000", hexnat% "80000000000000800000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ec334c715cd8b32acaaa9a8eac9966c59568d9362da2e2b86e8789e17ba1e4731ac5b1aa4e9c6699565554d4b5534ad1b51d2745dc8ea358ce3c4e9354e334ccb3a2ccb8acab1ae1b16d4749ca745c9715c3723c2fa6164a8a92a2a1a268661381e5849951525195151341d28c6324c8b12c1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6d26da6db6da4936db6da6934d249a49a6da49a492492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 73), (facetIndex 74), (facetIndex 75)]))
 (.leaf ([(facetIndex 43), (facetIndex 48), (facetIndex 52), (facetIndex 64)])))
 (.branch 3
 (.leaf ([(facetIndex 33), (facetIndex 35), (facetIndex 36), (facetIndex 51), (facetIndex 84)]))
 (.leaf ([(facetIndex 31), (facetIndex 54), (facetIndex 56), (facetIndex 59), (facetIndex 62)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 30), (facetIndex 44), (facetIndex 61), (facetIndex 89)]))
 (.leaf ([(facetIndex 28), (facetIndex 39), (facetIndex 40), (facetIndex 42), (facetIndex 50)])))
 (.branch 7
 (.leaf ([(facetIndex 29), (facetIndex 32), (facetIndex 34), (facetIndex 55)]))
 (.leaf ([(facetIndex 57), (facetIndex 76), (facetIndex 88)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "270020000070000000010e063bcc1541004345a02596735z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 63), (facetIndex 65), (facetIndex 93)]))
 (.leaf ([(facetIndex 47), (facetIndex 92)])))
 (.branch 3
 (.leaf ([(facetIndex 41), (facetIndex 58), (facetIndex 66), (facetIndex 78), (facetIndex 87)]))
 (.branch 4
 (.leaf ([(facetIndex 67), (facetIndex 77), (facetIndex 86)]))
 (.leaf ([(facetIndex 46), (facetIndex 68), (facetIndex 71)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 69), (facetIndex 72), (facetIndex 95)]))
 (.leaf ([(facetIndex 45), (facetIndex 49), (facetIndex 82), (facetIndex 83), (facetIndex 91)])))
 (.branch 8
 (.leaf ([(facetIndex 60), (facetIndex 70), (facetIndex 80), (facetIndex 81)]))
 (.branch 9
 (.leaf ([(facetIndex 79), (facetIndex 90), (facetIndex 94)]))
 (.leaf ([(facetIndex 53), (facetIndex 85)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5801680023906677823000054754320000070200009000601460002z29;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
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
def grouped2_0010 : List Nat := [6, 7]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3, 4]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [3, 4]
def grouped3_0020 : List Nat := [4]
def grouped3_0021 : List Nat := [5]
def grouped3_0022 : List Nat := [5, 6]
def grouped3_0023 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0024 : List Nat := [6]
def grouped3_0025 : List Nat := [7]
def grouped3_0026 : List Nat := [7, 8, 9]
def grouped3_0027 : List Nat := [8]
def grouped3_0028 : List Nat := [8, 9]
def grouped3_0029 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record008" 56

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record008" "{\"ridges\":[[44,161],[49,771],[52,672],[53,771],[61,273],[65,777],[70,784],[71,897],[72,897],[82,338],[83,784],[85,774],[89,672],[90,784],[90,800],[91,834],[93,780],[94,784],[95,432],[95,784]],\"owners\":[[44,161,[58,66,67,72],[9,34,40,50,52,60,68,69]],[61,273,[47,49,63,65,71],[12,33,45,56,62,68,70]],[52,672,[95],[25,67,69,72,88,89]],[89,672,[67,72],[25,52,69,88,95]],[82,338,[47],[]],[49,771,[53],[]],[53,771,[49],[]],[70,784,[83,93],[49,65,71,90,94,95]],[83,784,[65,70,71,95],[49,90,93,94]],[90,784,[65,71,93],[49,70,83,94,95]],[94,784,[49,65,71],[70,83,90,93,95]],[95,784,[49,65,83,93],[70,71,90,94]],[90,800,[72],[53,70,85,91,94,95]],[65,777,[],[]],[95,432,[68],[]],[71,897,[72],[]],[72,897,[71],[]],[85,774,[83],[]],[91,834,[],[]],[93,780,[],[]]],\"edges\":[[44,[49,53,65,70,71,72,83,85,90,91,93,94,95]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-4,-1],[-7,-2],[-7,-6],[-13,-7],[-18,-1],[-19,-2],[-19,-6],[-19,-13],[-3,10,15,16,20],[-11,5,7,12,14,19],[-8,29],[-24,16,20],[-21,5],[-7,9],[-9,7],[-18,22,27],[-22,14,18,19,29],[-25,14,19,27],[-28,7,14,19],[-29,7,14,22,27],[-25,20],[-14],[-29,17],[-19,20],[-20,19],[-23,22],[-26],[-27],[-30,2,6,8,13],[-31,1,3,11,24],[-32,30],[-33,32],[-34,31],[-35,34],[-36,33],[-36,35],[36],[-12,37],[-5,38],[-10,39],[-15,39],[-16,40],[-17,41],[-19,41],[-20,42],[-29,42],[-43,4,7,21,22,26],[-7,43],[-22,43],[-18,44],[-28,45],[-9,46],[-23,46],[-38,47],[-37,47],[-41,48],[-40,48],[-48,49],[-39,49],[-49,50],[-47,50],[-43,51],[-42,-43,52],[-46,53],[-45,53],[-53,54],[-44,54],[-51,-54,55],[-52,55],[-50,-55,56],[-56],[7,9,14,18,19,20,22,23,25,26,27,28,29]],\"atoms\":[{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":45,\"b\":30},{\"tag\":\"incompatible\",\"a\":49,\"b\":43},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":64,\"b\":49},{\"tag\":\"incompatible\",\"a\":70,\"b\":30},{\"tag\":\"incompatible\",\"a\":71,\"b\":43},{\"tag\":\"incompatible\",\"a\":71,\"b\":48},{\"tag\":\"incompatible\",\"a\":71,\"b\":64},{\"tag\":\"mate\",\"ridge\":161,\"a\":44,\"owners\":[58,66,67,72]},{\"tag\":\"mate\",\"ridge\":273,\"a\":61,\"owners\":[47,49,63,65,71]},{\"tag\":\"mate\",\"ridge\":672,\"a\":52,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":672,\"a\":89,\"owners\":[67,72]},{\"tag\":\"mate\",\"ridge\":338,\"a\":82,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":771,\"a\":49,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":771,\"a\":53,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":784,\"a\":70,\"owners\":[83,93]},{\"tag\":\"mate\",\"ridge\":784,\"a\":83,\"owners\":[65,70,71,95]},{\"tag\":\"mate\",\"ridge\":784,\"a\":90,\"owners\":[65,71,93]},{\"tag\":\"mate\",\"ridge\":784,\"a\":94,\"owners\":[49,65,71]},{\"tag\":\"mate\",\"ridge\":784,\"a\":95,\"owners\":[49,65,83,93]},{\"tag\":\"mate\",\"ridge\":800,\"a\":90,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":777,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":432,\"a\":95,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":897,\"a\":71,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":897,\"a\":72,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":774,\"a\":85,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":834,\"a\":91,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":780,\"a\":93,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[43,48,52,64],\"full_literals\":[-30,2,6,8,13]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[30,44,61,89],\"full_literals\":[-31,1,3,11,24]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-32,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-33,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-34,31,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-35,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-36,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-36,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-12,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":47,\"full_literals\":[-5,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":58,\"full_literals\":[-10,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-15,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-16,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":68,\"full_literals\":[-17,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":71,\"full_literals\":[-19,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":72,\"full_literals\":[-20,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":95,\"full_literals\":[-29,42]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[45,49,82,83,91],\"full_literals\":[-43,4,7,21,22,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":49,\"full_literals\":[-7,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":83,\"full_literals\":[-22,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":70,\"full_literals\":[-18,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":94,\"full_literals\":[-28,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":53,\"full_literals\":[-9,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":85,\"full_literals\":[-23,46]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-43,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-50,-55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":44,\"owners\":[49,53,65,70,71,72,83,85,90,91,93,94,95]}]}"
  "p cnf 56 72\n-4 -1 0\n-7 -2 0\n-7 -6 0\n-13 -7 0\n-18 -1 0\n-19 -2 0\n-19 -6 0\n-19 -13 0\n-3 10 15 16 20 0\n-11 5 7 12 14 19 0\n-8 29 0\n-24 16 20 0\n-21 5 0\n-7 9 0\n-9 7 0\n-18 22 27 0\n-22 14 18 19 29 0\n-25 14 19 27 0\n-28 7 14 19 0\n-29 7 14 22 27 0\n-25 20 0\n-14 0\n-29 17 0\n-19 20 0\n-20 19 0\n-23 22 0\n-26 0\n-27 0\n-30 2 6 8 13 0\n-31 1 3 11 24 0\n-32 30 0\n-33 32 0\n-34 31 0\n-35 34 0\n-36 33 0\n-36 35 0\n36 0\n-12 37 0\n-5 38 0\n-10 39 0\n-15 39 0\n-16 40 0\n-17 41 0\n-19 41 0\n-20 42 0\n-29 42 0\n-43 4 7 21 22 26 0\n-7 43 0\n-22 43 0\n-18 44 0\n-28 45 0\n-9 46 0\n-23 46 0\n-38 47 0\n-37 47 0\n-41 48 0\n-40 48 0\n-48 49 0\n-39 49 0\n-49 50 0\n-47 50 0\n-43 51 0\n-42 -43 52 0\n-46 53 0\n-45 53 0\n-53 54 0\n-44 54 0\n-51 -54 55 0\n-52 55 0\n-50 -55 56 0\n-56 0\n7 9 14 18 19 20 22 23 25 26 27 28 29 0\n"
  "73 33 0 37 35 0\n74 35 0 37 36 0\n75 32 0 73 32 0\n76 34 0 74 34 0\n77 30 0 75 31 0\n78 31 0 76 33 0\n79 -43 4 7 21 22 0 27 47 0\n80 7 9 18 19 20 22 23 25 28 29 0 22 27 28 72 0\n81 43 41 0 22 28 44 25 18 43 23 48 49 15 19 16 26 80 0\n82 7 50 0 78 22 60 58 56 81 59 40 57 42 41 44 25 9 12 43 23 61 54 39 13 55 38 10 30 1 5 79 17 0\n83 50 0 77 60 58 56 43 23 11 82 2 3 4 29 0\n84 -55 0 83 71 70 0\n85 -52 0 84 69 0\n86 -43 0 85 84 22 62 63 68 45 46 66 67 21 24 64 65 50 52 53 51 17 14 80 0\n87 -7 0 86 48 0\n88 -22 0 86 49 0\n89 -9 0 87 15 0\n90 -29 0 87 22 88 28 20 0\n91 -18 0 88 28 16 0\n92 -23 0 88 26 0\n93 -8 0 90 11 0\n94 -19 0 93 77 6 7 8 29 0\n95 -25 0 94 22 28 18 0\n96 -20 0 94 25 0\n97 -28 0 94 22 87 19 0\n98 0 94 96 87 88 91 89 92 95 97 90 80 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3b0cd31c572b2aa8eaa6966559362d8ae1b89e17ba1d8791cc6b16c749aa6693a71956725c55558d5352d70d5362d2b46d8751d2745da8d6338e9354e334ccb3a2ccb8acab1ae1b16d4749ca745c9715c3723c2fa6164268661381ec86a158711a46898649951525195151341d28c6324c8b12c1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6d26db4924926d369a49a6d369249249b692692492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 49), (facetIndex 69)]))
 (.leaf ([(facetIndex 87), (facetIndex 93)])))
 (.branch 3
 (.leaf ([(facetIndex 62), (facetIndex 74)]))
 (.leaf ([(facetIndex 43), (facetIndex 59), (facetIndex 60), (facetIndex 71), (facetIndex 72)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 84), (facetIndex 90), (facetIndex 91)]))
 (.leaf ([(facetIndex 47), (facetIndex 48), (facetIndex 63), (facetIndex 65), (facetIndex 75)])))
 (.branch 7
 (.leaf ([(facetIndex 85), (facetIndex 86), (facetIndex 92), (facetIndex 95), (facetIndex 96)]))
 (.leaf ([(facetIndex 94)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6dce9003b4000000a83600028a83600000005a006z20;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record009" 67

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record009" "{\"ridges\":[[9,162],[12,276],[14,289],[15,261],[20,784],[22,672],[23,289],[23,800],[28,292],[35,276],[36,162],[37,289],[38,261],[42,162],[43,554],[46,162],[48,562],[51,162],[53,162],[53,672],[56,276],[60,556],[61,261],[62,780],[64,276],[65,564],[66,276],[67,276],[67,784],[68,800],[70,784],[72,616],[73,672],[74,840],[75,289],[76,672],[77,800],[78,784],[79,800],[80,672],[80,800],[84,172],[88,292],[90,232],[91,554],[94,780],[95,564],[96,432],[96,800]],\"owners\":[[9,162,[84,85,90,91,92],[36,42,46,51,53]],[36,162,[90,91,92],[9,42,46,51,53,84,85]],[42,162,[85,92],[9,36,46,51,53,84,90,91]],[46,162,[84,90,91],[9,36,42,51,53,85,92]],[51,162,[84,85,91,92],[9,36,42,46,53,90]],[53,162,[84,85,90],[9,36,42,46,51,91,92]],[15,261,[12,14,35,37,56,62,67,68],[38,61]],[38,261,[12,14,56,62,67,68],[15,35,37,61]],[61,261,[12,14,35,37,67,68],[15,38,56,62]],[12,276,[86,87,93,94,95],[35,56,64,66,67]],[35,276,[93,94,95],[12,56,64,66,67,86,87]],[56,276,[86,87,95],[12,35,64,66,67,93,94]],[64,276,[87,93,94],[12,35,56,66,67,86,95]],[66,276,[86,94,95],[12,35,56,64,67,87,93]],[67,276,[86,87,93],[12,35,56,64,66,94,95]],[28,292,[14,37,64,68,86,95],[88]],[88,292,[14,64,68,95],[28,37,86]],[20,784,[94,95,96],[67,70,77,78]],[67,784,[96],[20,70,77,78,94,95]],[70,784,[95,96],[20,67,77,78,94]],[78,784,[94,95],[20,67,70,77,96]],[22,672,[91,92,96],[53,73,76,80]],[53,672,[96],[22,73,76,80,91,92]],[73,672,[92,96],[22,53,76,80,91]],[76,672,[91],[22,53,73,80,92,96]],[80,672,[91,92],[22,53,73,76,96]],[23,800,[95,96],[68,77,79,80]],[68,800,[96],[23,77,79,80,95]],[77,800,[],[23,68,79,80,95,96]],[79,800,[95,96],[23,68,77,80]],[80,800,[95],[23,68,77,79,96]],[96,800,[23,68,79],[77,80,95]],[43,554,[91],[]],[91,554,[43],[]],[48,562,[92],[]],[84,172,[59],[]],[60,556,[],[]],[62,780,[94],[]],[94,780,[62],[]],[65,564,[95],[]],[95,564,[65],[]],[90,232,[71],[]],[72,616,[],[]],[74,840,[],[]],[96,432,[75],[]]],\"edges\":[[22,[12,14,15,28,35,37,38,56,61,62,64,66,67,68,86,87,88,93,94,95]],[36,[9,22,36,42,46,51,53,59,63,71,73,75,76,80,84,85,90,91,92,96]],[38,[22,23,43,48,53,60,65,68,72,73,76,77,79,80,91,92,95,96]],[44,[20,23,62,67,68,70,74,77,78,79,80,94,95,96]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-26,-9],[-35,-29],[-39,-35],[-51,-24],[-51,-35],[-51,-42],[-51,-48],[-52,-43],[-52,-51],[-1,41,42,46,47,48],[-10,46,47,48],[-13,42,48],[-15,41,46,47],[-17,41,42,47,48],[-18,41,42,46],[-4,2,3,9,11,19,23,28,29],[-12,2,3,19,23,28,29],[-22,2,3,9,11,28,29],[-2,43,44,49,50,51],[-9,49,50,51],[-19,43,44,51],[-25,44,49,50],[-27,43,50,51],[-28,43,44,49],[-3,-7,-35],[-7,-11,-35],[-8,3,11,25,29,43,51],[-45,3,25,29,51],[-5,50,51,52],[-28,52],[-30,51,52],[-38,50,51],[-6,47,48,52],[-18,52],[-33,48,52],[-36,47],[-40,47,48],[-7,51,52],[-29,52],[-37],[-39,51,52],[-40,51],[-52,7,29,39],[-14,47],[-47,14],[-16,48],[-41,20],[-21],[-23,50],[-50,23],[-26,51],[-51,26],[-46,31],[-32],[-34],[-52,35],[-44,53],[-49,53],[-23,54],[-14,55],[-20,55],[-31,55],[-47,56],[-26,57],[-35,57],[-48,58],[-51,58],[-52,58],[-50,59],[-53,60],[-55,61],[-54,61],[-61,62],[-60,62],[-57,63],[-56,63],[-59,64],[-58,64],[-58,-59,65],[-65,66],[-63,-64,66],[-62,-66,67],[-67],[2,3,4,8,9,11,12,19,22,23,25,27,28,29,43,44,45,49,50,51],[1,6,10,13,15,17,18,20,24,31,33,35,36,40,41,42,46,47,48,52],[6,7,14,16,18,21,26,29,32,33,36,37,39,40,47,48,51,52],[5,7,23,28,29,30,34,37,38,39,40,50,51,52]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":65,\"b\":35},{\"tag\":\"incompatible\",\"a\":75,\"b\":68},{\"tag\":\"incompatible\",\"a\":79,\"b\":75},{\"tag\":\"incompatible\",\"a\":95,\"b\":63},{\"tag\":\"incompatible\",\"a\":95,\"b\":75},{\"tag\":\"incompatible\",\"a\":95,\"b\":85},{\"tag\":\"incompatible\",\"a\":95,\"b\":92},{\"tag\":\"incompatible\",\"a\":96,\"b\":86},{\"tag\":\"incompatible\",\"a\":96,\"b\":95},{\"tag\":\"mate\",\"ridge\":162,\"a\":9,\"owners\":[84,85,90,91,92]},{\"tag\":\"mate\",\"ridge\":162,\"a\":36,\"owners\":[90,91,92]},{\"tag\":\"mate\",\"ridge\":162,\"a\":42,\"owners\":[85,92]},{\"tag\":\"mate\",\"ridge\":162,\"a\":46,\"owners\":[84,90,91]},{\"tag\":\"mate\",\"ridge\":162,\"a\":51,\"owners\":[84,85,91,92]},{\"tag\":\"mate\",\"ridge\":162,\"a\":53,\"owners\":[84,85,90]},{\"tag\":\"mate\",\"ridge\":261,\"a\":15,\"owners\":[12,14,35,37,56,62,67,68]},{\"tag\":\"mate\",\"ridge\":261,\"a\":38,\"owners\":[12,14,56,62,67,68]},{\"tag\":\"mate\",\"ridge\":261,\"a\":61,\"owners\":[12,14,35,37,67,68]},{\"tag\":\"mate\",\"ridge\":276,\"a\":12,\"owners\":[86,87,93,94,95]},{\"tag\":\"mate\",\"ridge\":276,\"a\":35,\"owners\":[93,94,95]},{\"tag\":\"mate\",\"ridge\":276,\"a\":56,\"owners\":[86,87,95]},{\"tag\":\"mate\",\"ridge\":276,\"a\":64,\"owners\":[87,93,94]},{\"tag\":\"mate\",\"ridge\":276,\"a\":66,\"owners\":[86,94,95]},{\"tag\":\"mate\",\"ridge\":276,\"a\":67,\"owners\":[86,87,93]},{\"tag\":\"three\",\"ridge\":289,\"vertices\":[14,23,75]},{\"tag\":\"three\",\"ridge\":289,\"vertices\":[23,37,75]},{\"tag\":\"mate\",\"ridge\":292,\"a\":28,\"owners\":[14,37,64,68,86,95]},{\"tag\":\"mate\",\"ridge\":292,\"a\":88,\"owners\":[14,64,68,95]},{\"tag\":\"mate\",\"ridge\":784,\"a\":20,\"owners\":[94,95,96]},{\"tag\":\"mate\",\"ridge\":784,\"a\":67,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":784,\"a\":70,\"owners\":[95,96]},{\"tag\":\"mate\",\"ridge\":784,\"a\":78,\"owners\":[94,95]},{\"tag\":\"mate\",\"ridge\":672,\"a\":22,\"owners\":[91,92,96]},{\"tag\":\"mate\",\"ridge\":672,\"a\":53,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":672,\"a\":73,\"owners\":[92,96]},{\"tag\":\"mate\",\"ridge\":672,\"a\":76,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":672,\"a\":80,\"owners\":[91,92]},{\"tag\":\"mate\",\"ridge\":800,\"a\":23,\"owners\":[95,96]},{\"tag\":\"mate\",\"ridge\":800,\"a\":68,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":800,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":800,\"a\":79,\"owners\":[95,96]},{\"tag\":\"mate\",\"ridge\":800,\"a\":80,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":800,\"a\":96,\"owners\":[23,68,79]},{\"tag\":\"mate\",\"ridge\":554,\"a\":43,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":554,\"a\":91,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":562,\"a\":48,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":172,\"a\":84,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":556,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":780,\"a\":62,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":780,\"a\":94,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":564,\"a\":65,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":564,\"a\":95,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":232,\"a\":90,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":616,\"a\":72,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":840,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":432,\"a\":96,\"owners\":[75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-44,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":93,\"full_literals\":[-49,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":62,\"full_literals\":[-23,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":43,\"full_literals\":[-14,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":59,\"full_literals\":[-20,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-31,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":91,\"full_literals\":[-47,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":65,\"full_literals\":[-26,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":75,\"full_literals\":[-35,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":92,\"full_literals\":[-48,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":95,\"full_literals\":[-51,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":96,\"full_literals\":[-52,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":94,\"full_literals\":[-50,59]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-59,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-62,-66,67],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[12,14,15,28,35,37,38,56,61,62,64,66,67,68,86,87,88,93,94,95]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[9,22,36,42,46,51,53,59,63,71,73,75,76,80,84,85,90,91,92,96]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[22,23,43,48,53,60,65,68,72,73,76,77,79,80,91,92,95,96]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[20,23,62,67,68,70,74,77,78,79,80,94,95,96]}]}"
  "p cnf 67 87\n-26 -9 0\n-35 -29 0\n-39 -35 0\n-51 -24 0\n-51 -35 0\n-51 -42 0\n-51 -48 0\n-52 -43 0\n-52 -51 0\n-1 41 42 46 47 48 0\n-10 46 47 48 0\n-13 42 48 0\n-15 41 46 47 0\n-17 41 42 47 48 0\n-18 41 42 46 0\n-4 2 3 9 11 19 23 28 29 0\n-12 2 3 19 23 28 29 0\n-22 2 3 9 11 28 29 0\n-2 43 44 49 50 51 0\n-9 49 50 51 0\n-19 43 44 51 0\n-25 44 49 50 0\n-27 43 50 51 0\n-28 43 44 49 0\n-3 -7 -35 0\n-7 -11 -35 0\n-8 3 11 25 29 43 51 0\n-45 3 25 29 51 0\n-5 50 51 52 0\n-28 52 0\n-30 51 52 0\n-38 50 51 0\n-6 47 48 52 0\n-18 52 0\n-33 48 52 0\n-36 47 0\n-40 47 48 0\n-7 51 52 0\n-29 52 0\n-37 0\n-39 51 52 0\n-40 51 0\n-52 7 29 39 0\n-14 47 0\n-47 14 0\n-16 48 0\n-41 20 0\n-21 0\n-23 50 0\n-50 23 0\n-26 51 0\n-51 26 0\n-46 31 0\n-32 0\n-34 0\n-52 35 0\n-44 53 0\n-49 53 0\n-23 54 0\n-14 55 0\n-20 55 0\n-31 55 0\n-47 56 0\n-26 57 0\n-35 57 0\n-48 58 0\n-51 58 0\n-52 58 0\n-50 59 0\n-53 60 0\n-55 61 0\n-54 61 0\n-61 62 0\n-60 62 0\n-57 63 0\n-56 63 0\n-59 64 0\n-58 64 0\n-58 -59 65 0\n-65 66 0\n-63 -64 66 0\n-62 -66 67 0\n-67 0\n2 3 4 8 9 11 12 19 22 23 25 27 28 29 43 44 45 49 50 51 0\n1 6 10 13 15 17 18 20 24 31 33 35 36 40 41 42 46 47 48 52 0\n6 7 14 16 18 21 26 29 32 33 36 37 39 40 47 48 51 52 0\n5 7 23 28 29 30 34 37 38 39 40 50 51 52 0\n"
  "88 6 7 14 16 18 26 29 33 36 39 40 47 48 51 52 0 48 54 40 86 0\n89 5 7 23 28 29 30 38 39 40 50 51 52 0 55 40 87 0\n90 -9 62 0 73 72 59 50 74 70 58 1 20 52 0\n91 -51 55 0 60 45 62 53 61 47 13 36 4 5 6 7 9 12 10 14 15 37 11 33 35 85 0\n92 52 61 0 72 59 50 71 91 32 42 30 39 31 38 41 29 89 0\n93 62 0 73 74 71 72 70 59 57 58 50 22 90 91 92 8 56 24 23 21 19 2 3 43 25 26 28 16 17 18 27 84 0\n94 -66 0 93 83 82 0\n95 -65 0 94 80 0\n96 -52 0 94 56 68 65 78 75 81 0\n97 -28 0 96 30 0\n98 -18 0 96 34 0\n99 -29 0 96 39 0\n100 50 51 0 96 97 99 41 38 31 42 49 32 29 89 0\n101 51 0 95 94 96 98 99 42 51 38 41 100 69 77 79 81 66 76 46 35 63 36 44 33 88 0\n102 26 0 101 52 0\n103 58 0 101 67 0\n104 57 0 102 64 0\n105 64 0 103 78 0\n106 63 0 104 75 0\n107 0 106 105 94 81 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record009
