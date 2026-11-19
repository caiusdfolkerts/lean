module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00059Data
public import GraphInputsRow26Part00059Frames
public import GraphInputsRow26Part00059Leaves
public import GraphInputsRow26Part00059Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00059.record035
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨51, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨65, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [146402815757516800, (certNat% 2), 43092279296, 10995118374912, (certNat% 3)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [46745668550656, (certNat% 3), 103230210048, 146367005069410304, (certNat% 2)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2263350523723776, (certNat% 3), 113816633344, 144150389627813888, (certNat% 2)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2289754774700032, (certNat% 4), (certNat% 5), 78517370880, 36507222016]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [146404429599866880, (certNat% 2), 78517370880, 9345850933248, (certNat% 3)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 2203318222848, (certNat% 4), 549755813888]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [144115303435468800, (certNat% 2), (certNat% 4), 2251821288521728, 37933151158272]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2289826690236416, 34519121920, 8589934592, (certNat% 4), (certNat% 5)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 34519121920, 11811160064, 72061992084439040, 11544874188800, 146402189441499136]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨19, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨20, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00059.record035

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00059.record036
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "7a338752b47323c789d26c96a8e93a71996558d68d8b653a2e8791e0f9e1746b16c5c96a5693a6394e6a5a54d58d4b5934cd8b4ad8743d70da358ce364d5334e334ccb352e2b4ac6b86d1b0ecc789ca785c9715c3783c2f07db04c94a4a84e8c4b18a4c5854958344d0cc4b0ac4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6d269b6db4db6da4db69b4924934db6db6924926d26d2492449249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 35), (facetIndex 71), (facetIndex 80)]))
 (.leaf ([(facetIndex 23), (facetIndex 28), (facetIndex 50), (facetIndex 54)])))
 (.branch 3
 (.leaf ([(facetIndex 37), (facetIndex 78), (facetIndex 81)]))
 (.leaf ([(facetIndex 33), (facetIndex 63)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 20), (facetIndex 21), (facetIndex 49), (facetIndex 51)]))
 (.leaf ([(facetIndex 19), (facetIndex 24), (facetIndex 25), (facetIndex 47), (facetIndex 55)])))
 (.branch 7
 (.leaf ([(facetIndex 29), (facetIndex 34), (facetIndex 38), (facetIndex 58)]))
 (.leaf ([(facetIndex 22), (facetIndex 36), (facetIndex 52), (facetIndex 53), (facetIndex 64)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "10080000000007600180a7f860a0000019719803102d3e4a00000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 26), (facetIndex 27), (facetIndex 46), (facetIndex 48), (facetIndex 56)]))
 (.branch 2
 (.leaf ([(facetIndex 59), (facetIndex 61), (facetIndex 85)]))
 (.leaf ([(facetIndex 39), (facetIndex 75), (facetIndex 76)]))))
 (.branch 4
 (.leaf ([(facetIndex 67), (facetIndex 70), (facetIndex 72), (facetIndex 86)]))
 (.branch 5
 (.leaf ([(facetIndex 74), (facetIndex 77), (facetIndex 87)]))
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 68), (facetIndex 84), (facetIndex 88)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 89)]))
 (.branch 8
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 57), (facetIndex 60), (facetIndex 62)]))
 (.leaf ([(facetIndex 44), (facetIndex 65), (facetIndex 66)]))))
 (.branch 10
 (.leaf ([(facetIndex 45), (facetIndex 82), (facetIndex 83)]))
 (.branch 11
 (.leaf ([(facetIndex 69), (facetIndex 73)]))
 (.leaf ([(facetIndex 79)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "6543159900b04224a303a538800717107000000000009866772000000055z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
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
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00059.record036" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":10}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00059.record036" 71

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00059.record036" "{\"ridges\":[[7,521],[9,532],[11,545],[11,552],[13,49],[13,560],[15,42],[21,524],[25,532],[29,49],[31,538],[34,42],[34,552],[35,266],[38,50],[38,560],[47,524],[47,532],[49,552],[51,521],[51,524],[53,560],[55,532],[56,676],[58,529],[58,552],[58,560],[63,49],[64,560],[67,42],[67,50],[68,284],[71,266],[73,560],[80,42],[81,50],[81,176],[84,60],[84,532],[84,560],[86,560],[88,792]],\"owners\":[[7,521,[11,31,34,58],[21,47,51]],[51,521,[11,31,34,58],[7,21,47]],[21,524,[84],[7,47,49,51,69,70]],[47,524,[70],[7,21,49,51,69,84]],[51,524,[69,70,84],[7,21,47,49]],[58,529,[9,25,55],[13,31,38,47,64]],[9,532,[69,73,84,86],[25,47,53,55]],[25,532,[84,86],[9,47,53,55,69,73]],[47,532,[73,86],[9,25,53,55,69,84]],[55,532,[69,73,84],[9,25,47,53,86]],[84,532,[9,25,55],[47,53,69,73,86]],[11,545,[13,27,38,53,56,64],[34,49]],[11,552,[70,79,84,88],[34,49,58]],[34,552,[84,88],[11,49,58,70,79]],[49,552,[79,88],[11,34,58,70,84]],[58,552,[70],[11,34,49,79,84,88]],[81,176,[12,52,64,86],[18,36,72]],[13,560,[73,79,84,86,88],[38,53,58,64]],[38,560,[84,86,88],[13,53,58,64,73,79]],[53,560,[79,88],[13,38,58,64,73,84,86]],[58,560,[73,86],[13,38,53,64,79,84,88]],[64,560,[73,79,84,88],[13,38,53,58,86]],[73,560,[13,58,64,88],[38,53,79,84,86]],[84,560,[13,38,64],[53,58,73,79,86,88]],[86,560,[13,38,58,79,88],[53,64,73,84]],[35,266,[15,68,78],[16,30,33,71]],[71,266,[15,30,33,78],[16,35,68]],[31,538,[69,79],[]],[84,60,[46,67],[]],[56,676,[86],[]],[68,284,[],[]],[88,792,[],[]]],\"edges\":[[29,[7,11,21,31,34,47,49,51,58,69,70,79,84,88]],[34,[9,13,25,31,38,47,53,55,58,64,69,73,79,84,86,88]],[38,[11,13,27,34,38,49,53,56,58,64,70,73,79,84,86,88]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00059.record036" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00059.record036\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-12,-2],[-18,-16],[-20,-16],[-21,-13],[-21,-19],[-23,-5],[-25,-4],[-25,-18],[-25,-24],[-26,-25],[-30,-15],[-30,-29],[-34,-10],[-34,-11],[-34,-26],[-34,-31],[-34,-33],[-36,-7],[-36,-23],[-36,-27],[-37,-25],[-38,-16],[-38,-24],[-38,-25],[-38,-26],[-38,-34],[-38,-36],[-38,-37],[-39,-20],[-39,-24],[-41,-14],[-41,-25],[-42,-20],[-42,-41],[-44,-8],[-44,-10],[-44,-31],[-44,-41],[-46,-16],[-46,-20],[-46,-21],[-46,-24],[-46,-25],[-46,-36],[-46,-45],[-48,-12],[-48,-37],[-49,-7],[-49,-10],[-49,-16],[-49,-17],[-49,-31],[-49,-36],[-49,-41],[-49,-44],[-49,-45],[-50,-8],[-50,-10],[-50,-31],[-50,-38],[-50,-42],[-50,-49],[-6,-21,-39],[-21,-39,-47],[-5,-16,-37],[-25,-39,-48],[-1,3,18,21,36],[-30,3,18,21,36],[-9,49],[-27,42],[-30,41,42,49],[-36,2,13,34],[-2,41,44,49,50],[-13,49,50],[-27,44,50],[-34,41,44,49],[-49,2,13,34],[-3,5,14,25,32,35,38],[-3,42,46,49,51],[-21,49,51],[-28,46,51],[-36,42],[-48,4,31,38,50],[-5,44,46,49,50,51],[-25,49,50,51],[-32,46,51],[-36,44,50],[-38,44,46,49,51],[-44,5,36,38,51],[-49,5,25,38],[-50,5,25,36,46,51],[-22,6,40,45],[-43,6,17,20,45],[-18,41,46],[-49,26,39],[-35,50],[-40],[-51],[-52,19,22,43,47],[-53,11,15,29,33],[-54,24,45,48],[-55,20,37],[-56,8,9,28,30],[-57,7,12,13,27,34],[-58,16,21,25,36],[-59,10,23,31,32,38],[-60,52],[-60,53],[-61,54,55],[-62,54],[-62,55],[-64,60],[-63,61],[-64,62],[-65,56],[-65,57],[-66,58,59],[-67,58],[-67,59],[-68,65,67],[-69,65],[-68,66],[-69,67],[-70,63],[-70,64,69],[-70,68],[70],[-71,41,44],[-41,71],[-44,71],[1,3,9,18,21,27,28,30,36,41,42,46,49,51],[2,5,13,18,25,27,32,34,36,38,41,44,46,49,50,51],[3,5,14,21,25,28,32,35,36,38,42,44,46,49,50,51]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":24,\"b\":9},{\"tag\":\"incompatible\",\"a\":31,\"b\":29},{\"tag\":\"incompatible\",\"a\":33,\"b\":29},{\"tag\":\"incompatible\",\"a\":34,\"b\":25},{\"tag\":\"incompatible\",\"a\":34,\"b\":32},{\"tag\":\"incompatible\",\"a\":36,\"b\":13},{\"tag\":\"incompatible\",\"a\":38,\"b\":12},{\"tag\":\"incompatible\",\"a\":38,\"b\":31},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":46,\"b\":38},{\"tag\":\"incompatible\",\"a\":51,\"b\":28},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":55,\"b\":22},{\"tag\":\"incompatible\",\"a\":55,\"b\":23},{\"tag\":\"incompatible\",\"a\":55,\"b\":46},{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":58,\"b\":19},{\"tag\":\"incompatible\",\"a\":58,\"b\":36},{\"tag\":\"incompatible\",\"a\":58,\"b\":47},{\"tag\":\"incompatible\",\"a\":63,\"b\":38},{\"tag\":\"incompatible\",\"a\":64,\"b\":29},{\"tag\":\"incompatible\",\"a\":64,\"b\":37},{\"tag\":\"incompatible\",\"a\":64,\"b\":38},{\"tag\":\"incompatible\",\"a\":64,\"b\":46},{\"tag\":\"incompatible\",\"a\":64,\"b\":55},{\"tag\":\"incompatible\",\"a\":64,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":67,\"b\":33},{\"tag\":\"incompatible\",\"a\":67,\"b\":37},{\"tag\":\"incompatible\",\"a\":69,\"b\":27},{\"tag\":\"incompatible\",\"a\":69,\"b\":38},{\"tag\":\"incompatible\",\"a\":70,\"b\":33},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":20},{\"tag\":\"incompatible\",\"a\":73,\"b\":22},{\"tag\":\"incompatible\",\"a\":73,\"b\":52},{\"tag\":\"incompatible\",\"a\":73,\"b\":69},{\"tag\":\"incompatible\",\"a\":79,\"b\":29},{\"tag\":\"incompatible\",\"a\":79,\"b\":33},{\"tag\":\"incompatible\",\"a\":79,\"b\":34},{\"tag\":\"incompatible\",\"a\":79,\"b\":37},{\"tag\":\"incompatible\",\"a\":79,\"b\":38},{\"tag\":\"incompatible\",\"a\":79,\"b\":58},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":81,\"b\":24},{\"tag\":\"incompatible\",\"a\":81,\"b\":63},{\"tag\":\"incompatible\",\"a\":84,\"b\":19},{\"tag\":\"incompatible\",\"a\":84,\"b\":22},{\"tag\":\"incompatible\",\"a\":84,\"b\":29},{\"tag\":\"incompatible\",\"a\":84,\"b\":30},{\"tag\":\"incompatible\",\"a\":84,\"b\":52},{\"tag\":\"incompatible\",\"a\":84,\"b\":58},{\"tag\":\"incompatible\",\"a\":84,\"b\":69},{\"tag\":\"incompatible\",\"a\":84,\"b\":73},{\"tag\":\"incompatible\",\"a\":84,\"b\":78},{\"tag\":\"incompatible\",\"a\":86,\"b\":20},{\"tag\":\"incompatible\",\"a\":86,\"b\":22},{\"tag\":\"incompatible\",\"a\":86,\"b\":52},{\"tag\":\"incompatible\",\"a\":86,\"b\":64},{\"tag\":\"incompatible\",\"a\":86,\"b\":70},{\"tag\":\"incompatible\",\"a\":86,\"b\":84},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[15,34,67]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[34,67,80]},{\"tag\":\"three\",\"ridge\":49,\"vertices\":[13,29,63]},{\"tag\":\"three\",\"ridge\":50,\"vertices\":[38,67,81]},{\"tag\":\"mate\",\"ridge\":521,\"a\":7,\"owners\":[11,31,34,58]},{\"tag\":\"mate\",\"ridge\":521,\"a\":51,\"owners\":[11,31,34,58]},{\"tag\":\"mate\",\"ridge\":524,\"a\":21,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":524,\"a\":47,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":524,\"a\":51,\"owners\":[69,70,84]},{\"tag\":\"mate\",\"ridge\":529,\"a\":58,\"owners\":[9,25,55]},{\"tag\":\"mate\",\"ridge\":532,\"a\":9,\"owners\":[69,73,84,86]},{\"tag\":\"mate\",\"ridge\":532,\"a\":25,\"owners\":[84,86]},{\"tag\":\"mate\",\"ridge\":532,\"a\":47,\"owners\":[73,86]},{\"tag\":\"mate\",\"ridge\":532,\"a\":55,\"owners\":[69,73,84]},{\"tag\":\"mate\",\"ridge\":532,\"a\":84,\"owners\":[9,25,55]},{\"tag\":\"mate\",\"ridge\":545,\"a\":11,\"owners\":[13,27,38,53,56,64]},{\"tag\":\"mate\",\"ridge\":552,\"a\":11,\"owners\":[70,79,84,88]},{\"tag\":\"mate\",\"ridge\":552,\"a\":34,\"owners\":[84,88]},{\"tag\":\"mate\",\"ridge\":552,\"a\":49,\"owners\":[79,88]},{\"tag\":\"mate\",\"ridge\":552,\"a\":58,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":176,\"a\":81,\"owners\":[12,52,64,86]},{\"tag\":\"mate\",\"ridge\":560,\"a\":13,\"owners\":[73,79,84,86,88]},{\"tag\":\"mate\",\"ridge\":560,\"a\":38,\"owners\":[84,86,88]},{\"tag\":\"mate\",\"ridge\":560,\"a\":53,\"owners\":[79,88]},{\"tag\":\"mate\",\"ridge\":560,\"a\":58,\"owners\":[73,86]},{\"tag\":\"mate\",\"ridge\":560,\"a\":64,\"owners\":[73,79,84,88]},{\"tag\":\"mate\",\"ridge\":560,\"a\":73,\"owners\":[13,58,64,88]},{\"tag\":\"mate\",\"ridge\":560,\"a\":84,\"owners\":[13,38,64]},{\"tag\":\"mate\",\"ridge\":560,\"a\":86,\"owners\":[13,38,58,79,88]},{\"tag\":\"mate\",\"ridge\":266,\"a\":35,\"owners\":[15,68,78]},{\"tag\":\"mate\",\"ridge\":266,\"a\":71,\"owners\":[15,30,33,78]},{\"tag\":\"mate\",\"ridge\":538,\"a\":31,\"owners\":[69,79]},{\"tag\":\"mate\",\"ridge\":60,\"a\":84,\"owners\":[46,67]},{\"tag\":\"mate\",\"ridge\":676,\"a\":56,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":284,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":792,\"a\":88,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[32,35,71,80],\"full_literals\":[-52,19,22,43,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[23,28,50,54],\"full_literals\":[-53,11,15,29,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[37,78,81],\"full_literals\":[-54,24,45,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[33,63],\"full_literals\":[-55,20,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[20,21,49,51],\"full_literals\":[-56,8,9,28,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[19,24,25,47,55],\"full_literals\":[-57,7,12,13,27,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[29,34,38,58],\"full_literals\":[-58,16,21,25,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[22,36,52,53,64],\"full_literals\":[-59,10,23,31,32,38]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,54,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-64,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-66,58,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,65,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-69,65,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-70,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-70,64,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-70,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":10,\"members\":[69,73],\"full_literals\":[-71,41,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":69,\"full_literals\":[-41,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":73,\"full_literals\":[-44,71]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[7,11,21,31,34,47,49,51,58,69,70,79,84,88]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[9,13,25,31,38,47,53,55,58,64,69,73,79,84,86,88]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[11,13,27,34,38,49,53,56,58,64,70,73,79,84,86,88]}]}"
  "134 63 0 127 124 0\n135 68 0 127 126 0\n136 61 0 134 113 0\n137 66 0 135 122 0\n138 1 3 9 18 21 27 28 30 36 41 42 46 49 0 98 131 0\n139 2 5 13 18 25 27 32 34 36 38 41 44 46 49 50 0 98 132 0\n140 3 5 14 21 25 28 32 35 36 38 42 44 46 49 50 0 98 133 0\n141 -46 0 127 39 40 41 42 43 44 45 105 118 123 125 114 110 111 101 102 47 0\n142 -28 0 141 98 81 0\n143 -32 0 141 98 86 0\n144 44 49 -71 50 0 98 141 143 142 85 80 96 87 128 84 88 31 34 78 140 0\n145 36 38 -44 25 21 0 98 143 137 127 37 36 89 6 106 119 117 123 105 125 3 65 114 102 111 0\n146 38 -44 25 21 13 34 0 143 135 37 36 145 18 19 20 72 106 1 119 104 120 116 0\n147 49 -71 34 50 0 98 135 127 142 69 74 80 85 144 35 38 146 22 27 28 105 118 123 120 125 115 114 103 111 71 102 33 0\n148 -71 34 50 0 147 54 55 128 0\n149 -38 -49 36 27 34 0 136 127 56 50 48 23 24 25 28 95 29 102 111 109 114 101 125 46 121 123 116 118 104 105 4 0\n150 25 -49 36 27 34 0 143 137 135 149 52 50 49 48 90 6 106 119 117 120 105 116 4 77 104 1 0\n151 -49 34 50 0 136 148 130 87 75 52 56 149 150 7 9 10 21 83 95 101 29 109 102 0\n152 34 50 0 143 141 98 148 129 130 94 75 87 151 74 85 73 84 88 139 0\n153 44 49 50 0 152 144 76 129 0\n154 49 50 0 98 143 135 127 142 152 26 17 16 14 13 69 80 85 153 35 145 19 106 119 123 120 125 115 112 103 108 11 12 100 0\n155 25 50 0 143 137 127 97 152 15 154 95 29 56 53 51 50 26 16 13 90 6 106 119 117 123 105 125 5 63 64 112 93 92 107 99 0\n156 50 0 136 152 15 154 56 95 29 30 155 21 66 102 101 109 0\n157 -8 0 156 57 0\n158 -10 0 156 58 0\n159 -31 0 156 59 0\n160 -38 0 156 60 0\n161 -42 0 156 61 0\n162 -49 0 156 62 0\n163 -27 0 161 70 0\n164 -36 0 161 82 0\n165 -3 0 161 141 162 98 79 0\n166 -9 0 162 69 0\n167 -21 0 162 98 80 0\n168 -25 0 162 141 161 164 142 163 165 167 166 8 32 67 68 138 0\n169 5 0 168 156 164 141 98 91 0\n170 -23 0 169 6 0\n171 -59 0 170 158 159 143 160 106 0\n172 -67 0 171 119 0\n173 58 0 171 137 117 0\n174 65 0 172 135 120 0\n175 16 0 173 167 164 168 105 0\n176 56 0 174 115 0\n177 -18 0 175 2 0\n178 30 0 176 166 157 142 103 0\n179 0 178 177 165 167 164 68 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00059.record036
