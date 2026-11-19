module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00147Data
public import GraphInputsRow24Part00147Frames
public import GraphInputsRow24Part00147Leaves
public import GraphInputsRow24Part00147Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record001
def vertexColumn : Fields := ⟨10, hexnat% "3d0f2c6a3a4e8ba39956359362d876938ce4b8aeb44f1b2719a65998e5392e4e565555355352d4756364d3352d38f1354cd38cd332cc73c2e4b32e2b4acab86d1b26c3b91d4731d2729c6745c9715c3783c8f13cac9490e0ba51344b12a4c52950d2342d90e1344c530ce0b42c2b41c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6d249b6db49b4d34d269249249a4926924924d2491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c04a27f1c7fb6000000", 648518346475569152, hexnat% "20000000000000000000", 213305255788544, hexnat% "80000010000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c00a07f1c5fb2000000", 72705340604416, hexnat% "80000010000000000", hexnat% "30000100000004000000", 140737488355328, hexnat% "40a00000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100c827fdf7f3e000000", 2305843011361177600, 648518346341351424, hexnat% "c000000000000000000", hexnat% "20000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8006fdf6f3a000000", hexnat% "c008010000000000000", hexnat% "30000100000004000000", 70866960384, hexnat% "40a00000000000000", 2305843009213693952]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40a00004014000000", hexnat% "c008010000000000000", hexnat% "82002040200000000", hexnat% "30000100000000000000", 239693669072896, 262563430400, 30681874120572928]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c7 c2
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "b50ec670dc4f0bc3a99a4e8bab18e6c5a9665a364d8b66394e3392e2b86e4789e0f8e9964d94e4b939715954d58d5352d54d3352d2b46d4749d1743d38f138cd332ce4b52ccb4acab1ae1b46c9b0ef0751cc789d2729c6785d1725c3743c8f13c2f07cb82d0ca2aa46318a646439916154543590d0b12c2b81d0711c27"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6936926db69b4d36db6d26934936db4da6db6924934d2492492693499249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 53), (facetIndex 64), (facetIndex 71), (facetIndex 99)]))
 (.leaf ([(facetIndex 24), (facetIndex 27), (facetIndex 51), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 54), (facetIndex 56), (facetIndex 67)]))
 (.leaf ([(facetIndex 57), (facetIndex 72), (facetIndex 76)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 21), (facetIndex 38), (facetIndex 40), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 85), (facetIndex 86)]))
 (.leaf ([(facetIndex 47), (facetIndex 73), (facetIndex 83), (facetIndex 84), (facetIndex 87), (facetIndex 92)])))
 (.branch 7
 (.leaf ([(facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 74), (facetIndex 81), (facetIndex 96), (facetIndex 98)]))
 (.branch 8
 (.leaf ([(facetIndex 75), (facetIndex 78), (facetIndex 80), (facetIndex 97)]))
 (.leaf ([(facetIndex 91), (facetIndex 95)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "676800580005445506707037653010020000006663202001444500000040400000000001001004z15;"⟩
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
def grouped3_0012 : List Nat := [6, 7, 8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record003" 47

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record003" "{\"ridges\":[[10,532],[15,196],[18,200],[29,529],[34,196],[40,538],[44,200],[49,562],[50,786],[59,141],[63,532],[65,532],[66,532],[71,600],[79,196],[84,562],[86,658],[87,786],[88,196],[89,196],[93,200],[96,92],[98,108],[99,720]],\"owners\":[[29,529,[71],[10,40,49,50,63,65,66]],[10,532,[84,86,87,99],[29,63,65,66]],[63,532,[86,87,99],[10,29,65,66,84]],[65,532,[84,86,87],[10,29,63,66,99]],[66,532,[84,86,99],[10,29,63,65,87]],[15,196,[59,64,67,96,98,99],[34,79,88,89]],[34,196,[96,98,99],[15,59,64,67,79,88,89]],[79,196,[64,67,99],[15,34,59,88,89,96,98]],[88,196,[59,64,96,99],[15,34,67,79,89,98]],[89,196,[59,64,67,96,98],[15,34,79,88,99]],[18,200,[59,70,72,96,98],[44,79,93]],[44,200,[96,98],[18,59,70,72,79,93]],[93,200,[59,70,96],[18,44,72,79,98]],[59,141,[24,54,57],[]],[40,538,[],[]],[49,562,[84],[]],[84,562,[49],[]],[50,786,[87],[]],[87,786,[50],[]],[96,92,[53],[]],[98,108,[56,76],[]],[71,600,[],[]],[86,658,[],[]],[99,720,[],[]]],\"edges\":[[34,[10,29,40,49,50,63,65,66,71,84,86,87,99]],[39,[15,18,34,44,51,59,64,67,70,72,79,88,89,93,96,98,99]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-5,23],[-1,27,28,29,35],[-17,28,29,35],[-19,27,28,29],[-20,27,28,35],[-2,16,18,21,33,34,35],[-6,33,34,35],[-26,18,21,35],[-30,16,18,33,35],[-31,16,18,21,33,34],[-3,16,22,24,33,34],[-8,33,34],[-32,16,22,33],[-16,4,13,15],[-7],[-9,27],[-27,9],[-10,29],[-29,10],[-33,12],[-34,14,25],[-23],[-28],[-35],[-12,36],[-18,36],[-4,37],[-11,37],[-22,37],[-13,38],[-14,38],[-21,38],[-15,39],[-24,39],[-25,39],[-9,40],[-10,40],[-27,41],[-29,41],[-37,42],[-36,42],[-39,43],[-38,43],[-43,44],[-42,44],[-40,-41,45],[-45,46],[-44,-46,47],[-47],[1,5,7,9,10,17,19,20,23,27,28,29,35],[2,3,6,8,11,16,18,21,22,24,26,30,31,32,33,34,35]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":529,\"a\":29,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":532,\"a\":10,\"owners\":[84,86,87,99]},{\"tag\":\"mate\",\"ridge\":532,\"a\":63,\"owners\":[86,87,99]},{\"tag\":\"mate\",\"ridge\":532,\"a\":65,\"owners\":[84,86,87]},{\"tag\":\"mate\",\"ridge\":532,\"a\":66,\"owners\":[84,86,99]},{\"tag\":\"mate\",\"ridge\":196,\"a\":15,\"owners\":[59,64,67,96,98,99]},{\"tag\":\"mate\",\"ridge\":196,\"a\":34,\"owners\":[96,98,99]},{\"tag\":\"mate\",\"ridge\":196,\"a\":79,\"owners\":[64,67,99]},{\"tag\":\"mate\",\"ridge\":196,\"a\":88,\"owners\":[59,64,96,99]},{\"tag\":\"mate\",\"ridge\":196,\"a\":89,\"owners\":[59,64,67,96,98]},{\"tag\":\"mate\",\"ridge\":200,\"a\":18,\"owners\":[59,70,72,96,98]},{\"tag\":\"mate\",\"ridge\":200,\"a\":44,\"owners\":[96,98]},{\"tag\":\"mate\",\"ridge\":200,\"a\":93,\"owners\":[59,70,96]},{\"tag\":\"mate\",\"ridge\":141,\"a\":59,\"owners\":[24,54,57]},{\"tag\":\"mate\",\"ridge\":538,\"a\":40,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":562,\"a\":49,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":562,\"a\":84,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":786,\"a\":50,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":786,\"a\":87,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":92,\"a\":96,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":108,\"a\":98,\"owners\":[56,76]},{\"tag\":\"mate\",\"ridge\":600,\"a\":71,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":658,\"a\":86,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":720,\"a\":99,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":53,\"full_literals\":[-12,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":64,\"full_literals\":[-18,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":24,\"full_literals\":[-4,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":51,\"full_literals\":[-11,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":70,\"full_literals\":[-22,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":54,\"full_literals\":[-13,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":56,\"full_literals\":[-14,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-21,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":57,\"full_literals\":[-15,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-24,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-25,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":49,\"full_literals\":[-9,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":50,\"full_literals\":[-10,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-27,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-29,41]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-41,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-44,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[10,29,40,49,50,63,65,66,71,84,86,87,99]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[15,18,34,44,51,59,64,67,70,72,79,88,89,93,96,98,99]}]}"
  "p cnf 47 51\n-5 23 0\n-1 27 28 29 35 0\n-17 28 29 35 0\n-19 27 28 29 0\n-20 27 28 35 0\n-2 16 18 21 33 34 35 0\n-6 33 34 35 0\n-26 18 21 35 0\n-30 16 18 33 35 0\n-31 16 18 21 33 34 0\n-3 16 22 24 33 34 0\n-8 33 34 0\n-32 16 22 33 0\n-16 4 13 15 0\n-7 0\n-9 27 0\n-27 9 0\n-10 29 0\n-29 10 0\n-33 12 0\n-34 14 25 0\n-23 0\n-28 0\n-35 0\n-12 36 0\n-18 36 0\n-4 37 0\n-11 37 0\n-22 37 0\n-13 38 0\n-14 38 0\n-21 38 0\n-15 39 0\n-24 39 0\n-25 39 0\n-9 40 0\n-10 40 0\n-27 41 0\n-29 41 0\n-37 42 0\n-36 42 0\n-39 43 0\n-38 43 0\n-43 44 0\n-42 44 0\n-40 -41 45 0\n-45 46 0\n-44 -46 47 0\n-47 0\n1 5 7 9 10 17 19 20 23 27 28 29 35 0\n2 3 6 8 11 16 18 21 22 24 26 30 31 32 33 34 35 0\n"
  "52 -5 0 22 1 0\n53 1 9 10 17 19 20 27 29 0 52 15 22 23 24 50 0\n54 2 3 6 8 11 16 18 21 22 24 26 30 31 32 33 34 0 24 51 0\n55 44 0 24 44 45 42 43 40 41 33 34 35 30 31 32 27 28 29 25 26 14 21 8 20 6 9 10 11 13 7 12 54 0\n56 -46 0 55 49 48 0\n57 -45 0 56 47 0\n58 27 29 0 23 24 2 4 5 16 18 3 53 0\n59 41 0 38 39 58 0\n60 -40 0 59 57 46 0\n61 -9 0 60 36 0\n62 -10 0 60 37 0\n63 -27 0 61 17 0\n64 -29 0 62 19 0\n65 0 63 64 58 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "b50ec6713c2f2d23a99a4e8bab18e6c5a9665a5635a364d8b663a4e538ce4b8ae1b91e2783e3a5392e4e5c5655356354d4b59354d3352d2b46d4749d0f4e3c4e5334e334ccb392d4b32d2b2ac6b46c9b0ef0791d4731e2749ca719e1745c9715c3783d0f23c4f0bc1f2d0cc2b0b2328aa91615454354344d0b64384d130cd0b12c2b"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "69b4d369b6db6da6da69b6db6d26924924934d26924924934d36db69369a693249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 27), (facetIndex 90), (facetIndex 98)]))
 (.leaf ([(facetIndex 87), (facetIndex 93), (facetIndex 103)])))
 (.branch 3
 (.leaf ([(facetIndex 23), (facetIndex 40), (facetIndex 51), (facetIndex 54)]))
 (.branch 4
 (.leaf ([(facetIndex 28), (facetIndex 56), (facetIndex 67), (facetIndex 70)]))
 (.leaf ([(facetIndex 20), (facetIndex 71), (facetIndex 72), (facetIndex 96)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 73)]))
 (.leaf ([(facetIndex 74), (facetIndex 95), (facetIndex 101)])))
 (.branch 8
 (.leaf ([(facetIndex 33), (facetIndex 75), (facetIndex 100)]))
 (.branch 9
 (.leaf ([(facetIndex 25), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 38), (facetIndex 76), (facetIndex 77), (facetIndex 79), (facetIndex 83), (facetIndex 88)]))
 (.leaf ([(facetIndex 81), (facetIndex 82), (facetIndex 85), (facetIndex 86), (facetIndex 89), (facetIndex 91), (facetIndex 92)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "106700046019909819908990808876544300300000000003020020000000000208088875500300802004z14;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record004" 81

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record004" "{\"ridges\":[[5,530],[6,578],[9,268],[11,276],[12,532],[16,146],[19,148],[24,268],[29,276],[30,530],[30,532],[37,580],[38,774],[47,578],[48,146],[50,530],[52,530],[52,578],[53,530],[57,268],[57,276],[60,268],[62,268],[64,148],[65,276],[66,532],[68,532],[69,276],[69,532],[84,146],[86,550],[88,86],[90,646],[91,774],[94,146],[98,720],[99,148],[101,408],[103,720]],\"owners\":[[5,530,[86,88,90,91,98],[30,50,52,53]],[30,530,[98],[5,50,52,53,86,88,90,91]],[50,530,[88,90,91,98],[5,30,52,53,86]],[52,530,[86,90,91],[5,30,50,53,88,98]],[53,530,[86,88,90,98],[5,30,50,52,91]],[6,578,[82,88,93,98],[37,47,52]],[47,578,[88,93,98],[6,37,52,82]],[52,578,[82,93],[6,37,47,88,98]],[9,268,[76,79,81,83,100,101],[24,57,60,62]],[24,268,[100,101],[9,57,60,62,76,79,81,83]],[57,268,[79,81,83],[9,24,60,62,76,100,101]],[60,268,[76,81,83,101],[9,24,57,62,79,100]],[62,268,[76,79,83,100,101],[9,24,57,60,81]],[11,276,[76,85,89,91,100,101],[29,57,65,69]],[29,276,[100,101],[11,57,65,69,76,85,89,91]],[57,276,[85,89,91],[11,29,65,69,76,100,101]],[65,276,[76,89,91,101],[11,29,57,69,85,100]],[69,276,[76,85,89,100,101],[11,29,57,65,91]],[12,532,[86,88,90,91,103],[30,66,68,69]],[30,532,[103],[12,66,68,69,86,88,90,91]],[66,532,[88,90,91,103],[12,30,68,69,86]],[68,532,[86,90,91],[12,30,66,69,88,103]],[69,532,[86,88,90,103],[12,30,66,68,91]],[37,580,[103],[13,63,68,82,88,93]],[16,146,[28,40,51,75,87,89,90,96,98],[48,84,94]],[48,146,[75,87,89,90,96,98],[16,28,40,51,84,94]],[84,146,[40,51,96,98],[16,28,48,75,87,89,90,94]],[94,146,[28,51,87,89,90,98],[16,40,48,75,84,96]],[19,148,[28,56,67,75,87,89,90,101,103],[64,84,99]],[64,148,[75,87,89,90,101,103],[19,28,56,67,84,99]],[99,148,[28,67,87,89,90,103],[19,56,64,75,84,101]],[88,86,[27,87],[]],[86,550,[34],[]],[38,774,[91],[]],[91,774,[38],[]],[90,646,[93],[]],[101,408,[96],[]],[98,720,[103],[]],[103,720,[98],[]]],\"edges\":[[16,[5,6,25,30,34,37,38,47,50,52,53,82,86,88,90,91,93,98]],[22,[9,11,24,29,33,36,38,57,60,62,65,69,76,79,81,83,85,89,91,100,101]],[32,[16,19,28,40,48,51,56,64,67,71,75,84,87,89,90,94,96,98,99,101,103]],[34,[5,12,30,50,52,53,66,68,69,86,88,90,91,98,103]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-37,-9],[-37,-15],[-37,-18],[-41,-37],[-45,-37],[-47,-8],[-47,-12],[-47,-14],[-47,-16],[-47,-38],[-47,-39],[-47,-40],[-47,-42],[-47,-44],[-48,-9],[-48,-15],[-48,-18],[-48,-41],[-48,-45],[-48,-47],[-50,-37],[-50,-48],[-1,45,47,49,50,54],[-13,54],[-22,47,49,50,54],[-24,45,49,50],[-25,45,47,49,54],[-2,41,47,51,54],[-20,47,51,54],[-24,41,51],[-3,38,39,40,42,56,57],[-8,56,57],[-27,39,40,42],[-28,38,40,42,57],[-29,38,39,42,56,57],[-4,38,44,48,50,56,57],[-12,56,57],[-27,44,48,50],[-31,38,48,50,57],[-35,38,44,48,56,57],[-5,45,47,49,50,58],[-13,58],[-32,47,49,50,58],[-34,45,49,50],[-35,45,47,49,58],[-17,58],[-6,11,19,23,37,46,48,49,53,54],[-21,37,46,48,49,53,54],[-43,19,23,53,54],[-52,11,23,46,48,49,54],[-7,11,26,33,37,46,48,49,57,58],[-30,37,46,48,49,57,58],[-55,11,33,46,48,49,58],[-47,10,46],[-45,15],[-18,50],[-50,18],[-49,51],[-57,53],[-54,58],[-58,54],[-10,59],[-49,59],[-54,59],[-46,60],[-51,60],[-58,60],[-19,61],[-23,61],[-11,62],[-26,62],[-33,62],[-36,63],[-53,63],[-57,64],[-14,65],[-56,65],[-15,66],[-16,66],[-18,66],[-38,66],[-39,66],[-42,66],[-47,66],[-40,67],[-44,67],[-45,67],[-48,67],[-50,67],[-60,68],[-59,68],[-59,-60,69],[-63,70],[-62,70],[-70,71],[-61,71],[-71,72],[-68,72],[-69,73],[-64,74],[-67,75],[-66,75],[-66,-67,76],[-75,77],[-76,78],[-65,77],[-65,-75,78],[-77,79],[-78,80],[-74,79],[-74,-77,80],[-72,-80,81],[-73,-79,81],[-81],[1,2,9,13,15,17,18,20,22,24,25,41,45,47,49,50,51,54],[3,4,8,12,14,16,18,27,28,29,31,35,38,39,40,42,44,48,50,56,57],[6,7,11,19,21,23,26,30,33,36,37,43,46,48,49,52,53,54,55,57,58],[1,5,13,22,24,25,32,34,35,45,47,49,50,54,58]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":75,\"b\":25},{\"tag\":\"incompatible\",\"a\":75,\"b\":34},{\"tag\":\"incompatible\",\"a\":75,\"b\":38},{\"tag\":\"incompatible\",\"a\":82,\"b\":75},{\"tag\":\"incompatible\",\"a\":86,\"b\":75},{\"tag\":\"incompatible\",\"a\":88,\"b\":24},{\"tag\":\"incompatible\",\"a\":88,\"b\":29},{\"tag\":\"incompatible\",\"a\":88,\"b\":33},{\"tag\":\"incompatible\",\"a\":88,\"b\":36},{\"tag\":\"incompatible\",\"a\":88,\"b\":76},{\"tag\":\"incompatible\",\"a\":88,\"b\":79},{\"tag\":\"incompatible\",\"a\":88,\"b\":81},{\"tag\":\"incompatible\",\"a\":88,\"b\":83},{\"tag\":\"incompatible\",\"a\":88,\"b\":85},{\"tag\":\"incompatible\",\"a\":89,\"b\":25},{\"tag\":\"incompatible\",\"a\":89,\"b\":34},{\"tag\":\"incompatible\",\"a\":89,\"b\":38},{\"tag\":\"incompatible\",\"a\":89,\"b\":82},{\"tag\":\"incompatible\",\"a\":89,\"b\":86},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":91,\"b\":75},{\"tag\":\"incompatible\",\"a\":91,\"b\":89},{\"tag\":\"mate\",\"ridge\":530,\"a\":5,\"owners\":[86,88,90,91,98]},{\"tag\":\"mate\",\"ridge\":530,\"a\":30,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":530,\"a\":50,\"owners\":[88,90,91,98]},{\"tag\":\"mate\",\"ridge\":530,\"a\":52,\"owners\":[86,90,91]},{\"tag\":\"mate\",\"ridge\":530,\"a\":53,\"owners\":[86,88,90,98]},{\"tag\":\"mate\",\"ridge\":578,\"a\":6,\"owners\":[82,88,93,98]},{\"tag\":\"mate\",\"ridge\":578,\"a\":47,\"owners\":[88,93,98]},{\"tag\":\"mate\",\"ridge\":578,\"a\":52,\"owners\":[82,93]},{\"tag\":\"mate\",\"ridge\":268,\"a\":9,\"owners\":[76,79,81,83,100,101]},{\"tag\":\"mate\",\"ridge\":268,\"a\":24,\"owners\":[100,101]},{\"tag\":\"mate\",\"ridge\":268,\"a\":57,\"owners\":[79,81,83]},{\"tag\":\"mate\",\"ridge\":268,\"a\":60,\"owners\":[76,81,83,101]},{\"tag\":\"mate\",\"ridge\":268,\"a\":62,\"owners\":[76,79,83,100,101]},{\"tag\":\"mate\",\"ridge\":276,\"a\":11,\"owners\":[76,85,89,91,100,101]},{\"tag\":\"mate\",\"ridge\":276,\"a\":29,\"owners\":[100,101]},{\"tag\":\"mate\",\"ridge\":276,\"a\":57,\"owners\":[85,89,91]},{\"tag\":\"mate\",\"ridge\":276,\"a\":65,\"owners\":[76,89,91,101]},{\"tag\":\"mate\",\"ridge\":276,\"a\":69,\"owners\":[76,85,89,100,101]},{\"tag\":\"mate\",\"ridge\":532,\"a\":12,\"owners\":[86,88,90,91,103]},{\"tag\":\"mate\",\"ridge\":532,\"a\":30,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":532,\"a\":66,\"owners\":[88,90,91,103]},{\"tag\":\"mate\",\"ridge\":532,\"a\":68,\"owners\":[86,90,91]},{\"tag\":\"mate\",\"ridge\":532,\"a\":69,\"owners\":[86,88,90,103]},{\"tag\":\"mate\",\"ridge\":580,\"a\":37,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":146,\"a\":16,\"owners\":[28,40,51,75,87,89,90,96,98]},{\"tag\":\"mate\",\"ridge\":146,\"a\":48,\"owners\":[75,87,89,90,96,98]},{\"tag\":\"mate\",\"ridge\":146,\"a\":84,\"owners\":[40,51,96,98]},{\"tag\":\"mate\",\"ridge\":146,\"a\":94,\"owners\":[28,51,87,89,90,98]},{\"tag\":\"mate\",\"ridge\":148,\"a\":19,\"owners\":[28,56,67,75,87,89,90,101,103]},{\"tag\":\"mate\",\"ridge\":148,\"a\":64,\"owners\":[75,87,89,90,101,103]},{\"tag\":\"mate\",\"ridge\":148,\"a\":99,\"owners\":[28,67,87,89,90,103]},{\"tag\":\"mate\",\"ridge\":86,\"a\":88,\"owners\":[27,87]},{\"tag\":\"mate\",\"ridge\":550,\"a\":86,\"owners\":[34]},{\"tag\":\"mate\",\"ridge\":774,\"a\":38,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":774,\"a\":91,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":646,\"a\":90,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":408,\"a\":101,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":720,\"a\":98,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":720,\"a\":103,\"owners\":[98]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":27,\"full_literals\":[-10,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":90,\"full_literals\":[-49,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":98,\"full_literals\":[-54,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-46,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":93,\"full_literals\":[-51,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":103,\"full_literals\":[-58,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":40,\"full_literals\":[-19,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":51,\"full_literals\":[-23,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":28,\"full_literals\":[-11,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":56,\"full_literals\":[-26,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-33,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":71,\"full_literals\":[-36,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":96,\"full_literals\":[-53,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":101,\"full_literals\":[-57,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":33,\"full_literals\":[-14,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":100,\"full_literals\":[-56,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":34,\"full_literals\":[-15,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":36,\"full_literals\":[-16,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":38,\"full_literals\":[-18,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":76,\"full_literals\":[-38,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":79,\"full_literals\":[-39,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":83,\"full_literals\":[-42,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":88,\"full_literals\":[-47,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":81,\"full_literals\":[-40,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":85,\"full_literals\":[-44,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":86,\"full_literals\":[-45,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":89,\"full_literals\":[-48,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":91,\"full_literals\":[-50,67]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-60,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-67,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-76,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-75,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-78,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-74,-77,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-72,-80,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-73,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":16,\"owners\":[5,6,25,30,34,37,38,47,50,52,53,82,86,88,90,91,93,98]},{\"tag\":\"edge\",\"edge\":22,\"owners\":[9,11,24,29,33,36,38,57,60,62,65,69,76,79,81,83,85,89,91,100,101]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[16,19,28,40,48,51,56,64,67,71,75,84,87,89,90,94,96,98,99,101,103]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[5,12,30,50,52,53,66,68,69,86,88,90,91,98,103]}]}"
  "p cnf 81 118\n-37 -9 0\n-37 -15 0\n-37 -18 0\n-41 -37 0\n-45 -37 0\n-47 -8 0\n-47 -12 0\n-47 -14 0\n-47 -16 0\n-47 -38 0\n-47 -39 0\n-47 -40 0\n-47 -42 0\n-47 -44 0\n-48 -9 0\n-48 -15 0\n-48 -18 0\n-48 -41 0\n-48 -45 0\n-48 -47 0\n-50 -37 0\n-50 -48 0\n-1 45 47 49 50 54 0\n-13 54 0\n-22 47 49 50 54 0\n-24 45 49 50 0\n-25 45 47 49 54 0\n-2 41 47 51 54 0\n-20 47 51 54 0\n-24 41 51 0\n-3 38 39 40 42 56 57 0\n-8 56 57 0\n-27 39 40 42 0\n-28 38 40 42 57 0\n-29 38 39 42 56 57 0\n-4 38 44 48 50 56 57 0\n-12 56 57 0\n-27 44 48 50 0\n-31 38 48 50 57 0\n-35 38 44 48 56 57 0\n-5 45 47 49 50 58 0\n-13 58 0\n-32 47 49 50 58 0\n-34 45 49 50 0\n-35 45 47 49 58 0\n-17 58 0\n-6 11 19 23 37 46 48 49 53 54 0\n-21 37 46 48 49 53 54 0\n-43 19 23 53 54 0\n-52 11 23 46 48 49 54 0\n-7 11 26 33 37 46 48 49 57 58 0\n-30 37 46 48 49 57 58 0\n-55 11 33 46 48 49 58 0\n-47 10 46 0\n-45 15 0\n-18 50 0\n-50 18 0\n-49 51 0\n-57 53 0\n-54 58 0\n-58 54 0\n-10 59 0\n-49 59 0\n-54 59 0\n-46 60 0\n-51 60 0\n-58 60 0\n-19 61 0\n-23 61 0\n-11 62 0\n-26 62 0\n-33 62 0\n-36 63 0\n-53 63 0\n-57 64 0\n-14 65 0\n-56 65 0\n-15 66 0\n-16 66 0\n-18 66 0\n-38 66 0\n-39 66 0\n-42 66 0\n-47 66 0\n-40 67 0\n-44 67 0\n-45 67 0\n-48 67 0\n-50 67 0\n-60 68 0\n-59 68 0\n-59 -60 69 0\n-63 70 0\n-62 70 0\n-70 71 0\n-61 71 0\n-71 72 0\n-68 72 0\n-69 73 0\n-64 74 0\n-67 75 0\n-66 75 0\n-66 -67 76 0\n-75 77 0\n-76 78 0\n-65 77 0\n-65 -75 78 0\n-77 79 0\n-78 80 0\n-74 79 0\n-74 -77 80 0\n-72 -80 81 0\n-73 -79 81 0\n-81 0\n1 2 9 13 15 17 18 20 22 24 25 41 45 47 49 50 51 54 0\n3 4 8 12 14 16 18 27 28 29 31 35 38 39 40 42 44 48 50 56 57 0\n6 7 11 19 21 23 26 30 33 36 37 43 46 48 49 52 53 54 55 57 58 0\n1 5 13 22 24 25 32 34 35 45 47 49 50 54 58 0\n"
  "119 48 37 72 0 97 95 93 74 59 96 69 68 98 91 64 49 94 72 71 70 73 63 90 67 65 50 53 48 52 47 51 117 0\n120 -48 68 0 91 64 90 66 62 65 54 29 67 46 42 63 15 16 17 18 19 22 30 28 27 23 25 115 0\n121 72 0 98 90 91 65 66 67 62 63 64 54 42 46 29 120 119 1 2 3 4 5 21 30 28 27 23 25 115 0\n122 -80 0 121 114 112 0\n123 -78 0 122 109 0\n124 -76 0 123 105 0\n125 45 50 47 54 49 0 61 43 25 24 27 45 26 44 23 41 118 0\n126 -45 0 124 55 87 78 103 0\n127 -50 0 124 57 89 80 103 0\n128 -18 0 127 56 0\n129 -47 0 123 122 127 128 6 7 8 9 10 11 12 13 14 20 84 33 102 104 107 111 77 100 75 34 39 31 35 36 40 116 0\n130 79 0 127 128 108 110 104 106 100 101 102 76 77 75 85 86 88 79 81 82 83 32 37 34 39 31 35 36 40 38 116 0\n131 -73 0 130 114 113 0\n132 -69 0 131 99 0\n133 -54 0 132 60 64 67 92 0\n134 49 0 133 126 127 129 125 0\n135 51 0 134 58 0\n136 59 0 134 63 0\n137 60 0 135 66 0\n138 0 137 136 132 92 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record015
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "cd2746b25c9c8ea96aa699a568d9361da4e4b8ae1ba1e4789e17a715c5a95a4e9565a5996558d5351d58d4b4ad1b49d1766338e538cd331cccb4acab1ad1b26e4789d2719e1745c9715c3743c4f0bd1c98a5216a2629a162381e46459494a54550d2341d28c6314c8b12c1b21c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6d34924db69a4936db49b69a49a4926d26924d2492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 51), (facetIndex 52), (facetIndex 63)]))
 (.leaf ([(facetIndex 31), (facetIndex 48), (facetIndex 69), (facetIndex 80), (facetIndex 83)])))
 (.branch 3
 (.leaf ([(facetIndex 37), (facetIndex 79), (facetIndex 81), (facetIndex 82)]))
 (.branch 4
 (.leaf ([(facetIndex 27), (facetIndex 41), (facetIndex 42), (facetIndex 44), (facetIndex 49)]))
 (.leaf ([(facetIndex 45), (facetIndex 50), (facetIndex 85)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 58), (facetIndex 62)]))
 (.leaf ([(facetIndex 34), (facetIndex 70), (facetIndex 71), (facetIndex 72)])))
 (.branch 8
 (.leaf ([(facetIndex 32), (facetIndex 54), (facetIndex 74)]))
 (.branch 9
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 33), (facetIndex 36)]))
 (.leaf ([(facetIndex 28), (facetIndex 35)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "40122120000706661000000500050557000431004303300028968718893z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 53), (facetIndex 64), (facetIndex 65), (facetIndex 66)]))
 (.branch 2
 (.leaf ([(facetIndex 73), (facetIndex 75), (facetIndex 84), (facetIndex 87)]))
 (.leaf ([(facetIndex 38), (facetIndex 57), (facetIndex 76)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 60), (facetIndex 77), (facetIndex 86)]))
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 67), (facetIndex 88), (facetIndex 89)])))
 (.branch 6
 (.leaf ([(facetIndex 59), (facetIndex 78)]))
 (.leaf ([(facetIndex 61), (facetIndex 68)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "242c100015a208006800033a1000000090000008z1c;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [4]
def grouped2_0008 : List Nat := [5, 6]
def grouped2_0009 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0010 : List Nat := [7]
def grouped2_0011 : List Nat := [7, 8, 9]
def grouped2_0012 : List Nat := [8]
def grouped2_0013 : List Nat := [8, 9]
def grouped2_0014 : List Nat := [9]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1, 2]
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [1, 2]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [3]
def grouped3_0022 : List Nat := [3, 4]
def grouped3_0023 : List Nat := [3, 4, 5, 6]
def grouped3_0024 : List Nat := [4]
def grouped3_0025 : List Nat := [5]
def grouped3_0026 : List Nat := [5, 6]
def grouped3_0027 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record015" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record015" 68

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record015" "{\"ridges\":[[8,97],[15,289],[15,292],[25,608],[35,97],[36,289],[36,292],[37,548],[43,298],[45,97],[46,306],[47,561],[49,97],[50,97],[50,608],[55,289],[55,292],[58,289],[58,292],[62,289],[62,292],[65,360],[66,424],[67,368],[75,298],[77,116],[78,306],[81,548],[81,608],[85,608],[87,424],[88,116],[89,816]],\"owners\":[[8,97,[53,57,61,64,65,67,68],[35,41,45,49,50]],[35,97,[64,65,67,68],[8,41,45,49,50,53,57,61]],[45,97,[53,61,64,65],[8,35,41,49,50,57,67,68]],[49,97,[53,57,61,65,67,68],[8,35,41,45,50,64]],[50,97,[53,57,64,65,67],[8,35,41,45,49,61,68]],[15,289,[43,46,65,66,67],[36,55,58,62]],[36,289,[65,66,67],[15,43,46,55,58,62]],[55,289,[46,67],[15,36,43,58,62,65,66]],[58,289,[43,65,66],[15,36,46,55,62,67]],[62,289,[43,46,65,67],[15,36,55,58,66]],[15,292,[75,78,87,89],[36,55,58,62]],[36,292,[87,89],[15,55,58,62,75,78]],[55,292,[78,89],[15,36,58,62,75,87]],[58,292,[75,87],[15,36,55,62,78,89]],[62,292,[75,78,89],[15,36,55,58,87]],[37,548,[88,89],[22,59,61,79,81,82]],[81,548,[59,89],[22,37,61,79,82,88]],[25,608,[61,68,88],[50,81,85]],[50,608,[88],[25,61,68,81,85]],[81,608,[68],[25,50,61,85,88]],[85,608,[61],[25,50,68,81,88]],[43,298,[75],[]],[75,298,[43],[]],[46,306,[78],[]],[78,306,[46],[]],[47,561,[59,68],[]],[77,116,[57,88],[]],[88,116,[57,77],[]],[65,360,[],[]],[66,424,[87],[]],[87,424,[66],[]],[67,368,[],[]],[89,816,[],[]]],\"edges\":[[35,[8,25,35,41,45,49,50,53,57,61,64,65,67,68,73,77,81,84,85,88]],[37,[15,36,43,46,55,58,62,65,66,67,75,78,87,89]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record015" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record015\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-7],[-13,-4],[-13,-5],[-13,-6],[-13,-12],[-15,-11],[-19,-8],[-21,-13],[-23,-19],[-30,-10],[-30,-17],[-30,-24],[-30,-29],[-33,-13],[-35,-32],[-36,-30],[-37,-13],[-38,-10],[-38,-17],[-38,-24],[-38,-29],[-38,-36],[-39,-13],[-39,-20],[-1,17,19,22,24,25,27,28],[-7,24,25,27,28],[-12,17,22,24,25],[-15,17,19,22,25,27,28],[-16,17,19,24,25,27],[-2,11,13,25,26,27],[-8,25,26,27],[-18,13,27],[-20,11,25,26],[-23,11,13,25,27],[-2,30,32,38,40],[-8,38,40],[-18,32,40],[-20,30,38],[-23,30,32,40],[-9,39,40],[-34,21,40],[-3,22,28,39],[-16,39],[-34,28],[-37,22],[-11,30],[-30,11],[-13,32],[-32,13],[-14,21,28],[-31,19,39],[-39,19,31],[-25],[-26,38],[-38,26],[-27],[-40],[-41,9,33,34,35],[-42,12,16,37],[-43,4,5,6,8],[-44,42],[-45,41,44],[-46,45],[-47,43],[-48,47],[-49,48],[-50,46,49],[50],[-11,51],[-17,51],[-24,51],[-26,51],[-30,52],[-38,52],[-19,53],[-31,54],[-55,13,14,27,39,40],[-13,55],[-39,55],[-21,56],[-32,56],[-22,57],[-28,57],[-53,58],[-52,58],[-52,-53,59],[-58,60],[-59,61],[-51,60],[-51,-58,61],[-51,-59,62],[-55,63],[-54,-55,64],[-57,65],[-56,65],[-65,66],[-63,66],[-63,-65,67],[-64,67],[-60,-67,68],[-61,-66,68],[-62,68],[-68],[1,3,7,10,12,15,16,17,19,22,24,25,27,28,29,31,34,36,37,39],[2,8,11,13,18,20,23,25,26,27,30,32,38,40]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":43,\"b\":35},{\"tag\":\"incompatible\",\"a\":46,\"b\":29},{\"tag\":\"incompatible\",\"a\":46,\"b\":30},{\"tag\":\"incompatible\",\"a\":46,\"b\":33},{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":43},{\"tag\":\"incompatible\",\"a\":57,\"b\":36},{\"tag\":\"incompatible\",\"a\":59,\"b\":46},{\"tag\":\"incompatible\",\"a\":62,\"b\":57},{\"tag\":\"incompatible\",\"a\":75,\"b\":41},{\"tag\":\"incompatible\",\"a\":75,\"b\":53},{\"tag\":\"incompatible\",\"a\":75,\"b\":64},{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":79,\"b\":46},{\"tag\":\"incompatible\",\"a\":82,\"b\":78},{\"tag\":\"incompatible\",\"a\":84,\"b\":75},{\"tag\":\"incompatible\",\"a\":85,\"b\":46},{\"tag\":\"incompatible\",\"a\":87,\"b\":41},{\"tag\":\"incompatible\",\"a\":87,\"b\":53},{\"tag\":\"incompatible\",\"a\":87,\"b\":64},{\"tag\":\"incompatible\",\"a\":87,\"b\":73},{\"tag\":\"incompatible\",\"a\":87,\"b\":84},{\"tag\":\"incompatible\",\"a\":88,\"b\":46},{\"tag\":\"incompatible\",\"a\":88,\"b\":58},{\"tag\":\"mate\",\"ridge\":97,\"a\":8,\"owners\":[53,57,61,64,65,67,68]},{\"tag\":\"mate\",\"ridge\":97,\"a\":35,\"owners\":[64,65,67,68]},{\"tag\":\"mate\",\"ridge\":97,\"a\":45,\"owners\":[53,61,64,65]},{\"tag\":\"mate\",\"ridge\":97,\"a\":49,\"owners\":[53,57,61,65,67,68]},{\"tag\":\"mate\",\"ridge\":97,\"a\":50,\"owners\":[53,57,64,65,67]},{\"tag\":\"mate\",\"ridge\":289,\"a\":15,\"owners\":[43,46,65,66,67]},{\"tag\":\"mate\",\"ridge\":289,\"a\":36,\"owners\":[65,66,67]},{\"tag\":\"mate\",\"ridge\":289,\"a\":55,\"owners\":[46,67]},{\"tag\":\"mate\",\"ridge\":289,\"a\":58,\"owners\":[43,65,66]},{\"tag\":\"mate\",\"ridge\":289,\"a\":62,\"owners\":[43,46,65,67]},{\"tag\":\"mate\",\"ridge\":292,\"a\":15,\"owners\":[75,78,87,89]},{\"tag\":\"mate\",\"ridge\":292,\"a\":36,\"owners\":[87,89]},{\"tag\":\"mate\",\"ridge\":292,\"a\":55,\"owners\":[78,89]},{\"tag\":\"mate\",\"ridge\":292,\"a\":58,\"owners\":[75,87]},{\"tag\":\"mate\",\"ridge\":292,\"a\":62,\"owners\":[75,78,89]},{\"tag\":\"mate\",\"ridge\":548,\"a\":37,\"owners\":[88,89]},{\"tag\":\"mate\",\"ridge\":548,\"a\":81,\"owners\":[59,89]},{\"tag\":\"mate\",\"ridge\":608,\"a\":25,\"owners\":[61,68,88]},{\"tag\":\"mate\",\"ridge\":608,\"a\":50,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":608,\"a\":81,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":608,\"a\":85,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":298,\"a\":43,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":298,\"a\":75,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":306,\"a\":46,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":306,\"a\":78,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":561,\"a\":47,\"owners\":[59,68]},{\"tag\":\"mate\",\"ridge\":116,\"a\":77,\"owners\":[57,88]},{\"tag\":\"mate\",\"ridge\":116,\"a\":88,\"owners\":[57,77]},{\"tag\":\"mate\",\"ridge\":360,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":424,\"a\":66,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":424,\"a\":87,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":368,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":816,\"a\":89,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[37,79,81,82],\"full_literals\":[-41,9,33,34,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[45,50,85],\"full_literals\":[-42,12,16,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[29,30,33,36],\"full_literals\":[-43,4,5,6,8]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,41,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-49,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-50,46,49],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":43,\"full_literals\":[-11,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":53,\"full_literals\":[-17,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":64,\"full_literals\":[-24,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-26,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":75,\"full_literals\":[-30,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-38,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":57,\"full_literals\":[-19,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":77,\"full_literals\":[-31,54]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[46,47,67,88,89],\"full_literals\":[-55,13,14,27,39,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":46,\"full_literals\":[-13,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":88,\"full_literals\":[-39,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":59,\"full_literals\":[-21,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-32,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":61,\"full_literals\":[-22,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":68,\"full_literals\":[-28,57]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-53,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-58,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-51,-59,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-55,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-60,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":35,\"owners\":[8,25,35,41,45,49,50,53,57,61,64,65,67,68,73,77,81,84,85,88]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[15,36,43,46,55,58,62,65,66,67,75,78,87,89]}]}"
  "p cnf 68 105\n-11 -7 0\n-13 -4 0\n-13 -5 0\n-13 -6 0\n-13 -12 0\n-15 -11 0\n-19 -8 0\n-21 -13 0\n-23 -19 0\n-30 -10 0\n-30 -17 0\n-30 -24 0\n-30 -29 0\n-33 -13 0\n-35 -32 0\n-36 -30 0\n-37 -13 0\n-38 -10 0\n-38 -17 0\n-38 -24 0\n-38 -29 0\n-38 -36 0\n-39 -13 0\n-39 -20 0\n-1 17 19 22 24 25 27 28 0\n-7 24 25 27 28 0\n-12 17 22 24 25 0\n-15 17 19 22 25 27 28 0\n-16 17 19 24 25 27 0\n-2 11 13 25 26 27 0\n-8 25 26 27 0\n-18 13 27 0\n-20 11 25 26 0\n-23 11 13 25 27 0\n-2 30 32 38 40 0\n-8 38 40 0\n-18 32 40 0\n-20 30 38 0\n-23 30 32 40 0\n-9 39 40 0\n-34 21 40 0\n-3 22 28 39 0\n-16 39 0\n-34 28 0\n-37 22 0\n-11 30 0\n-30 11 0\n-13 32 0\n-32 13 0\n-14 21 28 0\n-31 19 39 0\n-39 19 31 0\n-25 0\n-26 38 0\n-38 26 0\n-27 0\n-40 0\n-41 9 33 34 35 0\n-42 12 16 37 0\n-43 4 5 6 8 0\n-44 42 0\n-45 41 44 0\n-46 45 0\n-47 43 0\n-48 47 0\n-49 48 0\n-50 46 49 0\n50 0\n-11 51 0\n-17 51 0\n-24 51 0\n-26 51 0\n-30 52 0\n-38 52 0\n-19 53 0\n-31 54 0\n-55 13 14 27 39 40 0\n-13 55 0\n-39 55 0\n-21 56 0\n-32 56 0\n-22 57 0\n-28 57 0\n-53 58 0\n-52 58 0\n-52 -53 59 0\n-58 60 0\n-59 61 0\n-51 60 0\n-51 -58 61 0\n-51 -59 62 0\n-55 63 0\n-54 -55 64 0\n-57 65 0\n-56 65 0\n-65 66 0\n-63 66 0\n-63 -65 67 0\n-64 67 0\n-60 -67 68 0\n-61 -66 68 0\n-62 68 0\n-68 0\n1 3 7 10 12 15 16 17 19 22 24 25 27 28 29 31 34 36 37 39 0\n2 8 11 13 18 20 23 25 26 27 30 32 38 40 0\n"
  "106 -55 13 14 39 0 56 57 77 0\n107 -62 0 103 102 0\n108 1 3 7 10 12 15 16 17 19 22 24 28 29 31 34 36 37 39 0 53 56 104 0\n109 2 8 11 13 18 20 23 26 30 32 38 0 53 56 57 105 0\n110 13 60 0 56 53 89 69 72 33 31 87 85 74 73 32 49 34 30 109 0\n111 60 0 56 53 57 68 87 89 84 70 71 72 75 31 29 110 2 3 4 5 8 14 17 23 48 60 41 59 40 15 64 61 58 65 62 66 63 67 0\n112 -67 0 111 103 100 0\n113 -64 0 112 99 0\n114 -55 0 113 112 103 57 92 93 97 98 76 101 94 95 88 83 80 81 50 37 48 106 24 52 7 9 75 84 86 90 73 74 69 72 35 109 0\n115 -13 0 114 78 0\n116 -39 0 114 79 0\n117 -18 0 115 56 32 0\n118 -32 0 115 49 0\n119 -16 0 116 43 0\n120 30 38 0 57 118 117 115 54 36 46 39 38 35 109 0\n121 -30 0 107 103 56 53 116 119 10 11 12 13 16 47 73 1 6 69 85 91 90 86 101 75 96 51 94 82 83 45 42 27 25 44 108 0\n122 38 0 121 120 0\n123 -10 0 122 18 0\n124 -17 0 122 19 0\n125 -24 0 122 20 0\n126 -29 0 122 21 0\n127 -36 0 122 22 0\n128 26 0 122 55 0\n129 52 0 122 74 0\n130 51 0 128 72 0\n131 58 0 129 85 0\n132 -59 0 130 107 91 0\n133 61 0 131 130 90 0\n134 -53 0 132 129 86 0\n135 -66 0 133 103 101 0\n136 -19 0 134 75 0\n137 -65 0 135 96 0\n138 -31 0 136 116 51 0\n139 -57 0 137 94 0\n140 -22 0 139 82 0\n141 -28 0 139 83 0\n142 -37 0 140 45 0\n143 -3 0 140 141 116 42 0\n144 -12 0 140 124 125 53 27 0\n145 -1 0 140 125 136 124 53 56 141 25 0\n146 -15 0 140 124 136 53 56 141 28 0\n147 -34 0 141 44 0\n148 -7 0 141 53 56 125 26 0\n149 0 143 145 148 123 144 146 119 124 136 140 125 141 126 138 147 127 142 116 108 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record016
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9d25c9c9726a96a3a95a99a568d9361d92e2b86e4789e17b319c5716a5693a659566a5996558d5351d64d4b4ad1b61d4749d175a398d6338e5354e334cc7362d4b32d2b2ac6b26e4789d2719e1745c9715c3743c4f0bd1a168a62381e9865146459894a58548d0752328c6344c5342c8b12c1b21c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6da6db6d34934db6924936da6924924934924924d2492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 27), (facetIndex 32), (facetIndex 41), (facetIndex 60), (facetIndex 81)]))
 (.leaf ([(facetIndex 37), (facetIndex 65), (facetIndex 67), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 39), (facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 88)]))
 (.leaf ([(facetIndex 50), (facetIndex 66), (facetIndex 70), (facetIndex 75)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 40), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 45)]))
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 69)])))
 (.branch 7
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 46), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54)]))
 (.branch 8
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 33), (facetIndex 34), (facetIndex 49)]))
 (.leaf ([(facetIndex 47)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "2000000002220300003511310000005555666637086444404201667707744z1c;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 38), (facetIndex 59), (facetIndex 62), (facetIndex 63)]))
 (.branch 2
 (.leaf ([(facetIndex 61), (facetIndex 71), (facetIndex 72), (facetIndex 73), (facetIndex 80)]))
 (.leaf ([(facetIndex 82), (facetIndex 89), (facetIndex 90), (facetIndex 91)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 83), (facetIndex 86), (facetIndex 94)]))
 (.leaf ([(facetIndex 48), (facetIndex 64), (facetIndex 74), (facetIndex 76), (facetIndex 95)])))
 (.branch 6
 (.leaf ([(facetIndex 84), (facetIndex 85), (facetIndex 92)]))
 (.leaf ([(facetIndex 87), (facetIndex 93)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "8f5490ced681004109200004008000000004z24;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
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
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8]
def grouped2_0014 : List Nat := [8]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1, 2]
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [1, 2]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [3]
def grouped3_0022 : List Nat := [3, 4]
def grouped3_0023 : List Nat := [3, 4, 5, 6]
def grouped3_0024 : List Nat := [4]
def grouped3_0025 : List Nat := [5]
def grouped3_0026 : List Nat := [5, 6]
def grouped3_0027 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record016" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record016" 66

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record016" "{\"ridges\":[[12,289],[12,290],[17,548],[21,545],[36,289],[36,290],[37,548],[42,289],[42,290],[47,290],[50,592],[52,289],[52,290],[53,608],[54,289],[54,290],[64,308],[65,548],[66,532],[67,548],[68,548],[74,368],[75,608],[76,816],[84,308],[85,562],[87,582],[92,368],[94,588],[95,116]],\"owners\":[[12,289,[61,64,72,73,74,76],[36,42,47,52,54]],[36,289,[72,73,74,76],[12,42,47,52,54,61,64]],[42,289,[64,74,76],[12,36,47,52,54,61,72,73]],[52,289,[61,64,73,76],[12,36,42,47,54,72,74]],[54,289,[61,64,72,74,76],[12,36,42,47,52,73]],[12,290,[82,84,90,91,92],[36,42,47,52,54]],[36,290,[90,91,92],[12,42,47,52,54,82,84]],[42,290,[84,92],[12,36,47,52,54,82,90,91]],[47,290,[82,90,91],[12,36,42,52,54,84,92]],[52,290,[82,84,91],[12,36,42,47,54,90,92]],[54,290,[82,84,90,92],[12,36,42,47,52,91]],[66,532,[85],[15,34,58,65,86,94,95]],[21,545,[17,37,48,65,68,76],[53,75]],[17,548,[85,87,95],[37,65,67,68]],[37,548,[95],[17,65,67,68,85,87]],[65,548,[87],[17,37,67,68,85,95]],[67,548,[85],[17,37,65,68,87,95]],[68,548,[85,87,95],[17,37,65,67]],[50,592,[94,95],[20,66,70,75,86,93]],[53,608,[95],[21,67,75,87,93]],[75,608,[87],[21,53,67,93,95]],[87,582,[38,86],[]],[85,562,[48,93],[]],[94,588,[62],[]],[95,116,[63,83],[]],[64,308,[84],[]],[84,308,[64],[]],[74,368,[92],[]],[92,368,[74],[]],[76,816,[],[]]],\"edges\":[[37,[12,36,42,47,52,54,61,64,72,73,74,76,82,84,90,91,92]],[38,[17,21,37,48,53,65,67,68,75,76,85,87,93,95]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record016" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record016\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-8],[-21,-17],[-25,-22],[-30,-18],[-31,-30],[-36,-26],[-36,-31],[-37,-8],[-39,-30],[-39,-36],[-1,14,17,23,24,25,27],[-4,23,24,25,27],[-7,17,25,27],[-11,14,17,24,27],[-13,14,17,23,25,27],[-1,28,30,34,35,36],[-4,34,35,36],[-7,30,36],[-8,28,34,35],[-11,28,30,35],[-13,28,30,34,36],[-19,31],[-3,2,5,9,18,21,27],[-2,31,33,39],[-5,39],[-18,33],[-20,31],[-21,31,33,39],[-10,38,39],[-12,39],[-26,33],[-33,6,32],[-31,9,37],[-38,15],[-39,16,29],[-17,30],[-30,17],[-25,36],[-36,25],[-27],[-40,5,18,20,21],[-41,10,19,22,26],[-42,8],[-43,40],[-44,41],[-45,43],[-45,44],[-46,42],[-47,46],[-48,47],[-49,45,48],[49],[-6,50],[-15,50],[-16,50],[-14,51],[-23,51],[-24,51],[-28,52],[-34,52],[-35,52],[-29,53],[-32,53],[-9,54],[-17,54],[-25,54],[-39,54],[-30,55],[-31,55],[-36,55],[-33,56],[-37,56],[-52,57],[-51,57],[-57,58],[-50,58],[-50,-57,59],[-54,60],[-53,60],[-53,-54,61],[-56,62],[-55,62],[-55,-56,63],[-62,64],[-63,65],[-60,64],[-60,-62,65],[-61,65],[-58,-65,66],[-59,-64,66],[-66],[1,4,7,8,11,13,14,17,23,24,25,27,28,30,34,35,36],[2,3,5,9,12,18,20,21,26,27,31,33,37,39]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":84,\"b\":65},{\"tag\":\"incompatible\",\"a\":85,\"b\":84},{\"tag\":\"incompatible\",\"a\":92,\"b\":75},{\"tag\":\"incompatible\",\"a\":92,\"b\":85},{\"tag\":\"incompatible\",\"a\":93,\"b\":47},{\"tag\":\"incompatible\",\"a\":95,\"b\":84},{\"tag\":\"incompatible\",\"a\":95,\"b\":92},{\"tag\":\"mate\",\"ridge\":289,\"a\":12,\"owners\":[61,64,72,73,74,76]},{\"tag\":\"mate\",\"ridge\":289,\"a\":36,\"owners\":[72,73,74,76]},{\"tag\":\"mate\",\"ridge\":289,\"a\":42,\"owners\":[64,74,76]},{\"tag\":\"mate\",\"ridge\":289,\"a\":52,\"owners\":[61,64,73,76]},{\"tag\":\"mate\",\"ridge\":289,\"a\":54,\"owners\":[61,64,72,74,76]},{\"tag\":\"mate\",\"ridge\":290,\"a\":12,\"owners\":[82,84,90,91,92]},{\"tag\":\"mate\",\"ridge\":290,\"a\":36,\"owners\":[90,91,92]},{\"tag\":\"mate\",\"ridge\":290,\"a\":42,\"owners\":[84,92]},{\"tag\":\"mate\",\"ridge\":290,\"a\":47,\"owners\":[82,90,91]},{\"tag\":\"mate\",\"ridge\":290,\"a\":52,\"owners\":[82,84,91]},{\"tag\":\"mate\",\"ridge\":290,\"a\":54,\"owners\":[82,84,90,92]},{\"tag\":\"mate\",\"ridge\":532,\"a\":66,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":545,\"a\":21,\"owners\":[17,37,48,65,68,76]},{\"tag\":\"mate\",\"ridge\":548,\"a\":17,\"owners\":[85,87,95]},{\"tag\":\"mate\",\"ridge\":548,\"a\":37,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":548,\"a\":65,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":548,\"a\":67,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":548,\"a\":68,\"owners\":[85,87,95]},{\"tag\":\"mate\",\"ridge\":592,\"a\":50,\"owners\":[94,95]},{\"tag\":\"mate\",\"ridge\":608,\"a\":53,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":608,\"a\":75,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":582,\"a\":87,\"owners\":[38,86]},{\"tag\":\"mate\",\"ridge\":562,\"a\":85,\"owners\":[48,93]},{\"tag\":\"mate\",\"ridge\":588,\"a\":94,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":116,\"a\":95,\"owners\":[63,83]},{\"tag\":\"mate\",\"ridge\":308,\"a\":64,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":308,\"a\":84,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":368,\"a\":74,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":368,\"a\":92,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":816,\"a\":76,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[37,65,67,68],\"full_literals\":[-40,5,18,20,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[50,66,70,75],\"full_literals\":[-41,10,19,22,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[47],\"full_literals\":[-42,8]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-45,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-48,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-49,45,48],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":38,\"full_literals\":[-6,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":62,\"full_literals\":[-15,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-16,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":61,\"full_literals\":[-14,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":72,\"full_literals\":[-23,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-24,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":82,\"full_literals\":[-28,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":90,\"full_literals\":[-34,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":91,\"full_literals\":[-35,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-29,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":86,\"full_literals\":[-32,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":48,\"full_literals\":[-9,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":64,\"full_literals\":[-17,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-25,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":95,\"full_literals\":[-39,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-30,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-31,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":92,\"full_literals\":[-36,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-33,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":93,\"full_literals\":[-37,56]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-54,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-56,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-62,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-58,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[12,36,42,47,52,54,61,64,72,73,74,76,82,84,90,91,92]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[17,21,37,48,53,65,67,68,75,76,85,87,93,95]}]}"
  "p cnf 66 93\n-9 -8 0\n-21 -17 0\n-25 -22 0\n-30 -18 0\n-31 -30 0\n-36 -26 0\n-36 -31 0\n-37 -8 0\n-39 -30 0\n-39 -36 0\n-1 14 17 23 24 25 27 0\n-4 23 24 25 27 0\n-7 17 25 27 0\n-11 14 17 24 27 0\n-13 14 17 23 25 27 0\n-1 28 30 34 35 36 0\n-4 34 35 36 0\n-7 30 36 0\n-8 28 34 35 0\n-11 28 30 35 0\n-13 28 30 34 36 0\n-19 31 0\n-3 2 5 9 18 21 27 0\n-2 31 33 39 0\n-5 39 0\n-18 33 0\n-20 31 0\n-21 31 33 39 0\n-10 38 39 0\n-12 39 0\n-26 33 0\n-33 6 32 0\n-31 9 37 0\n-38 15 0\n-39 16 29 0\n-17 30 0\n-30 17 0\n-25 36 0\n-36 25 0\n-27 0\n-40 5 18 20 21 0\n-41 10 19 22 26 0\n-42 8 0\n-43 40 0\n-44 41 0\n-45 43 0\n-45 44 0\n-46 42 0\n-47 46 0\n-48 47 0\n-49 45 48 0\n49 0\n-6 50 0\n-15 50 0\n-16 50 0\n-14 51 0\n-23 51 0\n-24 51 0\n-28 52 0\n-34 52 0\n-35 52 0\n-29 53 0\n-32 53 0\n-9 54 0\n-17 54 0\n-25 54 0\n-39 54 0\n-30 55 0\n-31 55 0\n-36 55 0\n-33 56 0\n-37 56 0\n-52 57 0\n-51 57 0\n-57 58 0\n-50 58 0\n-50 -57 59 0\n-54 60 0\n-53 60 0\n-53 -54 61 0\n-56 62 0\n-55 62 0\n-55 -56 63 0\n-62 64 0\n-63 65 0\n-60 64 0\n-60 -62 65 0\n-61 65 0\n-58 -65 66 0\n-59 -64 66 0\n-66 0\n1 4 7 8 11 13 14 17 23 24 25 27 28 30 34 35 36 0\n2 3 5 9 12 18 20 21 26 27 31 33 37 39 0\n"
  "94 1 4 7 8 11 13 14 17 23 24 25 28 30 34 35 36 0 40 92 0\n95 2 3 5 9 12 18 20 21 26 31 33 37 39 0 40 93 0\n96 54 57 0 40 73 61 59 60 19 74 58 57 56 65 66 13 37 14 15 11 39 12 94 0\n97 30 36 57 0 73 60 61 17 38 59 19 74 58 57 56 18 36 20 21 16 94 0\n98 -30 -40 0 4 5 9 37 27 25 2 41 0\n99 58 0 52 75 76 73 54 59 60 61 34 19 43 48 49 50 51 46 47 44 45 98 97 6 7 10 39 22 29 3 42 0\n100 -65 0 99 91 89 0\n101 -63 0 100 85 0\n102 -61 0 100 88 0\n103 57 0 100 96 78 87 82 68 70 97 0\n104 -33 0 100 91 103 71 81 84 87 90 79 77 63 53 32 0\n105 -18 0 104 26 0\n106 -26 0 104 31 0\n107 31 39 -40 0 104 105 25 27 28 41 0\n108 -31 0 101 100 69 82 83 87 72 78 33 64 0\n109 -20 0 108 27 0\n110 -39 0 102 91 103 67 78 80 86 62 90 35 77 55 0\n111 -5 0 110 25 0\n112 -12 0 110 30 0\n113 -40 0 110 108 107 0\n114 -2 0 110 108 104 24 0\n115 -21 0 110 108 104 28 0\n116 -43 0 113 44 0\n117 -45 0 116 46 0\n118 48 0 117 52 51 0\n119 47 0 118 50 0\n120 46 0 119 49 0\n121 42 0 120 48 0\n122 8 0 121 43 0\n123 -9 0 122 1 0\n124 -37 0 122 8 0\n125 3 0 123 104 111 114 105 109 115 106 108 112 124 110 95 0\n126 0 125 123 111 114 105 115 40 23 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record016
