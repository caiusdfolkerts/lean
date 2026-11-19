module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00005Data
public import GraphInputsRow29Part00005Frames
public import GraphInputsRow29Part00005Leaves
public import GraphInputsRow29Part00005Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record001
def vertexColumn : Fields := ⟨10, hexnat% "2741f07ae1b46b1b26a9a661d98e538ce4b8ae1b91e2785e0fa71e2749b2729aa6691e745b1725a9665956351d58d534cd4b4ad1b51d2745d0f783d0ec3c8ea398c7352ccb4acab1ad1b26f07a1e4751cc789d2729c6745c9743c8f13c2f07f846285a0e98615836e058916439c168561645894550d58314c3342c8b12c2b06d0721c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "da4db6d26db6da4d36db49249249b6db6926db692492492492492492449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000401000000000000000", hexnat% "81000000000000000000000000", hexnat% "7f000000000000000000", hexnat% "102000080800042004080000000", 17310775492214784, hexnat% "18000006000000000000000", 140393890971648]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record002
def vertexColumn : Fields := ⟨10, hexnat% "7c9cb8ad2acacaaaa9a87ae1b46b1b26a9a661d98e538ce4b8ae1b91e2785e0fa71e2749b2729aa6691e785d16c5c96a5994756354d3352d2b46d4749d1743dd0ec3c8ea398e538cc73c2e8b92d4b32e2b4acab1ad1b26f07a1e4751cc789d2729c6745c9743c8f13c2f07f826285a0e98615836e058916439614550d703a0d8390e2314c3342c8b12c2b06d0721c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "369b6da4db6d26db6da4d36db49b6da4db6db492492492492492492492492492449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨89, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨114, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20408000000000000000000", hexnat% "40810000000000000000000000000", hexnat% "1020000810002402004000000000", hexnat% "1800000c0000000f80000000", hexnat% "3d800000000000000", 140393890971648, 287526688709935104]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "a725ce4b1aa6a5a4e9a6659362785e0fb61ca669c669996539b15a5a559595535a364d8749d1743de0f43b0da358f13a4e534cf0ba2e4b4ae1b46c9b16c3b61cc749ca745c570dc8fe406c6486a198961382e07b81c4691646491a619194951342d0758348c6344c9312c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6d36db4d24da4936d26da4924da4934da492492492489249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 66), (facetIndex 70)]))
 (.leaf ([(facetIndex 77), (facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 82), (facetIndex 84)]))
 (.leaf ([(facetIndex 65), (facetIndex 67), (facetIndex 71)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 50), (facetIndex 72)]))
 (.leaf ([(facetIndex 85), (facetIndex 88)])))
 (.branch 7
 (.leaf ([(facetIndex 90), (facetIndex 91)]))
 (.branch 8
 (.leaf ([(facetIndex 49), (facetIndex 52), (facetIndex 57), (facetIndex 58)]))
 (.leaf ([(facetIndex 86), (facetIndex 87)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "6605885202000110000430003030000007700007047z31;"⟩
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
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8]
def grouped3_0016 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record009" 60

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record009" "{\"ridges\":[[11,289],[11,290],[18,536],[20,577],[20,584],[39,289],[39,290],[46,536],[47,290],[48,577],[48,584],[49,650],[50,778],[51,290],[55,289],[55,290],[56,289],[56,290],[57,706],[58,834],[63,536],[64,577],[64,584],[65,652],[66,308],[67,596],[70,420],[71,708],[72,312],[73,584],[74,536],[75,536],[76,577],[76,584],[77,808],[78,864],[85,312],[86,594],[90,596]],\"owners\":[[11,289,[66,70,72,77,78],[39,47,51,55,56]],[39,289,[72,77,78],[11,47,51,55,56,66,70]],[55,289,[66,70,72,77],[11,39,47,51,56,78]],[56,289,[66,72,77,78],[11,39,47,51,55,70]],[11,290,[82,84,85],[39,47,51,55,56]],[39,290,[85],[11,47,51,55,56,82,84]],[47,290,[82,84],[11,39,51,55,56,85]],[51,290,[84],[11,39,47,55,56,82,85]],[55,290,[82,84,85],[11,39,47,51,56]],[56,290,[82,85],[11,39,47,51,55,84]],[18,536,[86,87,88,90,91],[46,63,73,74,75]],[46,536,[90,91],[18,63,73,74,75,86,87,88]],[63,536,[86,87,88],[18,46,73,74,75,90,91]],[74,536,[86,88,90],[18,46,63,73,75,87,91]],[75,536,[86,87,90,91],[18,46,63,73,74,88]],[20,577,[52,57,58,67,71,78],[48,64,73,76]],[48,577,[67,71,78],[20,52,57,58,64,73,76]],[64,577,[52,57,58,78],[20,48,67,71,73,76]],[76,577,[52,57,58,67,71],[20,48,64,73,78]],[20,584,[86,90],[48,64,73,76]],[48,584,[90],[20,64,73,76,86]],[64,584,[86],[20,48,73,76,90]],[73,584,[],[20,48,64,76,86,90]],[76,584,[86,90],[20,48,64,73]],[49,650,[87],[]],[50,778,[88],[]],[86,594,[52],[]],[57,706,[],[]],[58,834,[],[]],[65,652,[91],[]],[66,308,[82],[]],[67,596,[90],[]],[90,596,[67],[]],[70,420,[84],[]],[71,708,[],[]],[72,312,[85],[]],[85,312,[72],[]],[77,808,[],[]],[78,864,[],[]]],\"edges\":[[29,[18,20,46,48,49,50,63,64,65,73,74,75,76,77,86,87,88,90,91]],[37,[11,39,47,51,55,56,66,70,72,77,78,82,84,85]],[41,[20,48,52,57,58,64,67,71,73,76,78,86,90]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,19,21,23,28,29],[-4,23,28,29],[-12,19,21,23,28],[-13,19,23,28,29],[-1,30,31,32],[-4,32],[-6,30,31],[-10,31],[-12,30,31,32],[-13,30,32],[-2,33,34,35,36,37],[-5,36,37],[-16,33,34,35],[-25,33,35,36],[-26,33,34,36,37],[-3,11,14,15,20,22,29],[-7,20,22,29],[-17,11,14,15,29],[-27,11,14,15,20,22],[-3,33,36],[-7,36],[-17,33],[-24],[-27,33,36],[-8,34],[-9,35],[-33,11],[-14],[-15],[-18,37],[-19,30],[-20,36],[-36,20],[-21,31],[-22],[-23,32],[-32,23],[-28],[-29],[-19,38],[-21,38],[-30,39],[-31,39],[-20,40],[-41,9,23],[-9,41],[-23,41],[-32,42],[-35,42],[-36,43],[-37,43],[-11,44],[-33,45],[-34,45],[-38,46],[-40,47],[-39,47],[-39,-40,48],[-47,49],[-48,50],[-46,49],[-51,41,42],[-42,51],[-41,51],[-41,-42,52],[-45,53],[-44,53],[-44,-45,54],[-53,55],[-54,56],[-43,55],[-43,-53,56],[-55,57],[-56,58],[-51,-55,58],[-52,-55,59],[-59,60],[-49,-58,60],[-50,-57,60],[-60],[2,3,5,7,8,9,16,17,18,24,25,26,27,28,33,34,35,36,37],[1,4,6,10,12,13,19,21,23,28,29,30,31,32],[3,7,11,14,15,17,20,22,24,27,29,33,36]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":289,\"a\":11,\"owners\":[66,70,72,77,78]},{\"tag\":\"mate\",\"ridge\":289,\"a\":39,\"owners\":[72,77,78]},{\"tag\":\"mate\",\"ridge\":289,\"a\":55,\"owners\":[66,70,72,77]},{\"tag\":\"mate\",\"ridge\":289,\"a\":56,\"owners\":[66,72,77,78]},{\"tag\":\"mate\",\"ridge\":290,\"a\":11,\"owners\":[82,84,85]},{\"tag\":\"mate\",\"ridge\":290,\"a\":39,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":290,\"a\":47,\"owners\":[82,84]},{\"tag\":\"mate\",\"ridge\":290,\"a\":51,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":290,\"a\":55,\"owners\":[82,84,85]},{\"tag\":\"mate\",\"ridge\":290,\"a\":56,\"owners\":[82,85]},{\"tag\":\"mate\",\"ridge\":536,\"a\":18,\"owners\":[86,87,88,90,91]},{\"tag\":\"mate\",\"ridge\":536,\"a\":46,\"owners\":[90,91]},{\"tag\":\"mate\",\"ridge\":536,\"a\":63,\"owners\":[86,87,88]},{\"tag\":\"mate\",\"ridge\":536,\"a\":74,\"owners\":[86,88,90]},{\"tag\":\"mate\",\"ridge\":536,\"a\":75,\"owners\":[86,87,90,91]},{\"tag\":\"mate\",\"ridge\":577,\"a\":20,\"owners\":[52,57,58,67,71,78]},{\"tag\":\"mate\",\"ridge\":577,\"a\":48,\"owners\":[67,71,78]},{\"tag\":\"mate\",\"ridge\":577,\"a\":64,\"owners\":[52,57,58,78]},{\"tag\":\"mate\",\"ridge\":577,\"a\":76,\"owners\":[52,57,58,67,71]},{\"tag\":\"mate\",\"ridge\":584,\"a\":20,\"owners\":[86,90]},{\"tag\":\"mate\",\"ridge\":584,\"a\":48,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":584,\"a\":64,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":584,\"a\":73,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":584,\"a\":76,\"owners\":[86,90]},{\"tag\":\"mate\",\"ridge\":650,\"a\":49,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":778,\"a\":50,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":594,\"a\":86,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":706,\"a\":57,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":834,\"a\":58,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":652,\"a\":65,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":308,\"a\":66,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":596,\"a\":67,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":596,\"a\":90,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":420,\"a\":70,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":708,\"a\":71,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":312,\"a\":72,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":312,\"a\":85,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":808,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":864,\"a\":78,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-19,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-21,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":82,\"full_literals\":[-30,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":84,\"full_literals\":[-31,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-20,40]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[50,72],\"full_literals\":[-41,9,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":50,\"full_literals\":[-9,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":72,\"full_literals\":[-23,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-32,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":88,\"full_literals\":[-35,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":90,\"full_literals\":[-36,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":91,\"full_literals\":[-37,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":52,\"full_literals\":[-11,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":86,\"full_literals\":[-33,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":87,\"full_literals\":[-34,45]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-40,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-42,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-45,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-53,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-56,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-55,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-55,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-49,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-57,60],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[18,20,46,48,49,50,63,64,65,73,74,75,76,77,86,87,88,90,91]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[11,39,47,51,55,56,66,70,72,77,78,82,84,85]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[20,48,52,57,58,64,67,71,73,76,78,86,90]}]}"
  "p cnf 60 83\n-1 19 21 23 28 29 0\n-4 23 28 29 0\n-12 19 21 23 28 0\n-13 19 23 28 29 0\n-1 30 31 32 0\n-4 32 0\n-6 30 31 0\n-10 31 0\n-12 30 31 32 0\n-13 30 32 0\n-2 33 34 35 36 37 0\n-5 36 37 0\n-16 33 34 35 0\n-25 33 35 36 0\n-26 33 34 36 37 0\n-3 11 14 15 20 22 29 0\n-7 20 22 29 0\n-17 11 14 15 29 0\n-27 11 14 15 20 22 0\n-3 33 36 0\n-7 36 0\n-17 33 0\n-24 0\n-27 33 36 0\n-8 34 0\n-9 35 0\n-33 11 0\n-14 0\n-15 0\n-18 37 0\n-19 30 0\n-20 36 0\n-36 20 0\n-21 31 0\n-22 0\n-23 32 0\n-32 23 0\n-28 0\n-29 0\n-19 38 0\n-21 38 0\n-30 39 0\n-31 39 0\n-20 40 0\n-41 9 23 0\n-9 41 0\n-23 41 0\n-32 42 0\n-35 42 0\n-36 43 0\n-37 43 0\n-11 44 0\n-33 45 0\n-34 45 0\n-38 46 0\n-40 47 0\n-39 47 0\n-39 -40 48 0\n-47 49 0\n-48 50 0\n-46 49 0\n-51 41 42 0\n-42 51 0\n-41 51 0\n-41 -42 52 0\n-45 53 0\n-44 53 0\n-44 -45 54 0\n-53 55 0\n-54 56 0\n-43 55 0\n-43 -53 56 0\n-55 57 0\n-56 58 0\n-51 -55 58 0\n-52 -55 59 0\n-59 60 0\n-49 -58 60 0\n-50 -57 60 0\n-60 0\n2 3 5 7 8 9 16 17 18 24 25 26 27 28 33 34 35 36 37 0\n1 4 6 10 12 13 19 21 23 28 29 30 31 32 0\n3 7 11 14 15 17 20 22 24 27 29 33 36 0\n"
  "84 -59 0 80 77 0\n85 2 3 5 7 8 9 16 17 18 25 26 27 33 34 35 36 37 0 23 38 81 0\n86 1 4 6 10 12 13 19 21 23 30 31 32 0 38 39 82 0\n87 3 7 11 17 20 27 33 36 0 28 29 35 23 39 83 0\n88 51 49 0 59 57 43 8 42 7 61 55 41 40 63 64 48 47 6 5 9 10 86 0\n89 42 -51 0 48 49 62 36 26 45 0\n90 53 20 0 35 39 33 17 66 67 53 52 20 22 24 87 0\n91 49 0 84 39 38 59 61 56 57 55 44 42 43 40 41 7 8 88 89 90 69 76 65 47 2 37 1 3 4 86 0\n92 -58 0 91 80 78 0\n93 -56 0 92 74 0\n94 -54 0 93 70 0\n95 45 43 51 0 51 30 50 21 12 64 46 63 49 53 54 15 20 22 24 11 13 14 25 85 0\n96 43 51 0 94 39 35 29 28 50 21 32 95 68 52 18 27 16 19 87 0\n97 -55 0 92 80 93 73 75 79 63 64 60 48 47 6 96 72 90 44 58 42 43 7 31 5 9 10 8 34 86 0\n98 -53 0 97 69 0\n99 -43 0 97 71 0\n100 20 0 98 90 0\n101 -36 0 99 50 0\n102 0 100 101 32 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record012
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "398a725c1f392d4972e29aac6a9a66a5a4e87a699964d8762b86e2785e0fb61e47515c789ca5a99a719a6599965391e6c569695656554d475a364d2b46d8749d1743de0f43b0da358f13a4d9394d534cc73c2e8b62e4b4acab1ae1b46c9b16c3b61cc749ca745c970dc4f198562382e07b81c4651a2619194552342d0758348c6344c5322c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db6db6db69249349a6da4d36db69a4d24924da49a492693492492492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 66), (facetIndex 72), (facetIndex 74)]))
 (.branch 2
 (.leaf ([(facetIndex 73), (facetIndex 82)]))
 (.leaf ([(facetIndex 81), (facetIndex 83), (facetIndex 88)]))))
 (.branch 4
 (.leaf ([(facetIndex 97), (facetIndex 104)]))
 (.branch 5
 (.leaf ([(facetIndex 69), (facetIndex 75), (facetIndex 76), (facetIndex 85)]))
 (.leaf ([(facetIndex 95), (facetIndex 98), (facetIndex 99), (facetIndex 106)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 44), (facetIndex 109), (facetIndex 110)]))
 (.branch 8
 (.leaf ([(facetIndex 47), (facetIndex 53), (facetIndex 57), (facetIndex 58), (facetIndex 100)]))
 (.leaf ([(facetIndex 71), (facetIndex 78), (facetIndex 102), (facetIndex 111)]))))
 (.branch 10
 (.leaf ([(facetIndex 96), (facetIndex 101), (facetIndex 108)]))
 (.branch 11
 (.leaf ([(facetIndex 103), (facetIndex 107)]))
 (.leaf ([(facetIndex 105), (facetIndex 112)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "b8669a5b3a89755395000000200402120080440108040000000000770007000007006z2c;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record012" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record012" 69

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record012" "{\"ridges\":[[11,290],[20,577],[21,784],[22,896],[33,290],[43,290],[47,778],[49,290],[51,577],[54,784],[55,290],[56,290],[57,706],[58,834],[59,386],[66,588],[70,577],[73,420],[74,708],[77,577],[80,784],[81,616],[82,424],[83,808],[84,896],[86,577],[86,784],[87,896],[88,864],[97,420],[104,424],[107,834],[110,588]],\"owners\":[[11,290,[95,97,99,104,106],[33,43,49,55,56]],[33,290,[99,104,106],[11,43,49,55,56,95,97]],[43,290,[95,97,106],[11,33,49,55,56,99,104]],[49,290,[97,104],[11,33,43,55,56,95,99,106]],[55,290,[95,97,99,104],[11,33,43,49,56,106]],[56,290,[95,99,106],[11,33,43,49,55,97,104]],[59,386,[96,97,101,104],[12,35,45,52,56,105,108]],[20,577,[44,57,58,66,74,81,88],[51,70,77,86]],[51,577,[66,74,81,88],[20,44,57,58,70,77,86]],[70,577,[44,57,58,81,88],[20,51,66,74,77,86]],[77,577,[57,58,74,88],[20,44,51,66,70,81,86]],[86,577,[44,57,66,74,81],[20,51,58,70,77,88]],[21,784,[103,107,108,112],[54,80,86,87]],[54,784,[112],[21,80,86,87,103,107,108]],[80,784,[107,108],[21,54,86,87,103,112]],[86,784,[103,108,112],[21,54,80,87,107]],[22,896,[105,108,112],[59,84,87]],[84,896,[108],[22,59,87,105,112]],[87,896,[105],[22,59,84,108,112]],[47,778,[103,105],[]],[57,706,[],[]],[58,834,[107],[]],[107,834,[58],[]],[66,588,[110],[]],[110,588,[66],[]],[73,420,[97],[]],[97,420,[73],[]],[74,708,[],[]],[81,616,[],[]],[82,424,[104],[]],[104,424,[82],[]],[83,808,[],[]],[88,864,[],[]]],\"edges\":[[37,[11,33,43,49,55,56,69,73,76,82,83,85,88,95,97,99,104,106]],[41,[20,44,51,57,58,66,70,74,77,81,86,88,100,107,110]],[44,[21,22,47,54,58,59,80,83,84,86,87,88,103,105,107,108,112]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record012" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record012\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,33,35,36,40,42],[-5,36,40,42],[-6,33,35,42],[-9,35,40],[-12,33,35,36,40],[-13,33,36,42],[-16,34,35,38,40],[-2,7,14,15,17,21,25,32],[-10,17,21,25,32],[-19,7,14,15,25,32],[-23,14,15,21,32],[-30,7,14,17,21,25],[-3,39,43,44,46],[-11,46],[-24,43,44],[-30,39,44,46],[-4,41,44,46],[-28,44],[-31,41],[-8,39,41],[-14],[-15,43],[-43,15],[-17,45],[-45,17],[-20,35],[-35,20],[-21],[-25],[-26,40],[-40,26],[-27],[-32],[-17,47],[-20,48],[-26,48],[-35,49],[-40,49],[-18,50],[-22,50],[-29,50],[-33,51],[-36,51],[-42,51],[-7,52],[-45,52],[-15,53],[-37,53],[-34,54],[-38,54],[-44,54],[-39,55],[-43,55],[-41,56],[-46,56],[-48,57],[-57,58],[-47,58],[-51,59],[-50,59],[-59,60],[-49,60],[-60,61],[-58,-60,62],[-53,63],[-63,64],[-52,64],[-56,65],[-55,65],[-65,66],[-54,66],[-64,67],[-64,-66,68],[-61,-68,69],[-62,-67,69],[-69],[1,5,6,9,12,13,18,20,22,26,27,29,32,33,35,36,40,42],[2,7,10,14,15,17,19,21,23,25,30,32,37,43,45],[3,4,8,11,15,16,24,27,28,30,31,32,39,41,43,44,46]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":290,\"a\":11,\"owners\":[95,97,99,104,106]},{\"tag\":\"mate\",\"ridge\":290,\"a\":33,\"owners\":[99,104,106]},{\"tag\":\"mate\",\"ridge\":290,\"a\":43,\"owners\":[95,97,106]},{\"tag\":\"mate\",\"ridge\":290,\"a\":49,\"owners\":[97,104]},{\"tag\":\"mate\",\"ridge\":290,\"a\":55,\"owners\":[95,97,99,104]},{\"tag\":\"mate\",\"ridge\":290,\"a\":56,\"owners\":[95,99,106]},{\"tag\":\"mate\",\"ridge\":386,\"a\":59,\"owners\":[96,97,101,104]},{\"tag\":\"mate\",\"ridge\":577,\"a\":20,\"owners\":[44,57,58,66,74,81,88]},{\"tag\":\"mate\",\"ridge\":577,\"a\":51,\"owners\":[66,74,81,88]},{\"tag\":\"mate\",\"ridge\":577,\"a\":70,\"owners\":[44,57,58,81,88]},{\"tag\":\"mate\",\"ridge\":577,\"a\":77,\"owners\":[57,58,74,88]},{\"tag\":\"mate\",\"ridge\":577,\"a\":86,\"owners\":[44,57,66,74,81]},{\"tag\":\"mate\",\"ridge\":784,\"a\":21,\"owners\":[103,107,108,112]},{\"tag\":\"mate\",\"ridge\":784,\"a\":54,\"owners\":[112]},{\"tag\":\"mate\",\"ridge\":784,\"a\":80,\"owners\":[107,108]},{\"tag\":\"mate\",\"ridge\":784,\"a\":86,\"owners\":[103,108,112]},{\"tag\":\"mate\",\"ridge\":896,\"a\":22,\"owners\":[105,108,112]},{\"tag\":\"mate\",\"ridge\":896,\"a\":84,\"owners\":[108]},{\"tag\":\"mate\",\"ridge\":896,\"a\":87,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":778,\"a\":47,\"owners\":[103,105]},{\"tag\":\"mate\",\"ridge\":706,\"a\":57,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":834,\"a\":58,\"owners\":[107]},{\"tag\":\"mate\",\"ridge\":834,\"a\":107,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":588,\"a\":66,\"owners\":[110]},{\"tag\":\"mate\",\"ridge\":588,\"a\":110,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":420,\"a\":73,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":420,\"a\":97,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":708,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":616,\"a\":81,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":424,\"a\":82,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":424,\"a\":104,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":808,\"a\":83,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":864,\"a\":88,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-17,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-20,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-26,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":97,\"full_literals\":[-35,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":104,\"full_literals\":[-40,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":69,\"full_literals\":[-18,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-22,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":85,\"full_literals\":[-29,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":95,\"full_literals\":[-33,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":99,\"full_literals\":[-36,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":106,\"full_literals\":[-42,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":44,\"full_literals\":[-7,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":110,\"full_literals\":[-45,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":58,\"full_literals\":[-15,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":100,\"full_literals\":[-37,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":96,\"full_literals\":[-34,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":101,\"full_literals\":[-38,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":108,\"full_literals\":[-44,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":103,\"full_literals\":[-39,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":107,\"full_literals\":[-43,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":105,\"full_literals\":[-41,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":112,\"full_literals\":[-46,56]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-61,-68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-62,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[11,33,43,49,55,56,69,73,76,82,83,85,88,95,97,99,104,106]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[20,44,51,57,58,66,70,74,77,81,86,88,100,107,110]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[21,22,47,54,58,59,80,83,84,86,87,88,103,105,107,108,112]}]}"
  "p cnf 69 79\n-1 33 35 36 40 42 0\n-5 36 40 42 0\n-6 33 35 42 0\n-9 35 40 0\n-12 33 35 36 40 0\n-13 33 36 42 0\n-16 34 35 38 40 0\n-2 7 14 15 17 21 25 32 0\n-10 17 21 25 32 0\n-19 7 14 15 25 32 0\n-23 14 15 21 32 0\n-30 7 14 17 21 25 0\n-3 39 43 44 46 0\n-11 46 0\n-24 43 44 0\n-30 39 44 46 0\n-4 41 44 46 0\n-28 44 0\n-31 41 0\n-8 39 41 0\n-14 0\n-15 43 0\n-43 15 0\n-17 45 0\n-45 17 0\n-20 35 0\n-35 20 0\n-21 0\n-25 0\n-26 40 0\n-40 26 0\n-27 0\n-32 0\n-17 47 0\n-20 48 0\n-26 48 0\n-35 49 0\n-40 49 0\n-18 50 0\n-22 50 0\n-29 50 0\n-33 51 0\n-36 51 0\n-42 51 0\n-7 52 0\n-45 52 0\n-15 53 0\n-37 53 0\n-34 54 0\n-38 54 0\n-44 54 0\n-39 55 0\n-43 55 0\n-41 56 0\n-46 56 0\n-48 57 0\n-57 58 0\n-47 58 0\n-51 59 0\n-50 59 0\n-59 60 0\n-49 60 0\n-60 61 0\n-58 -60 62 0\n-53 63 0\n-63 64 0\n-52 64 0\n-56 65 0\n-55 65 0\n-65 66 0\n-54 66 0\n-64 67 0\n-64 -66 68 0\n-61 -68 69 0\n-62 -67 69 0\n-69 0\n1 5 6 9 12 13 18 20 22 26 27 29 32 33 35 36 40 42 0\n2 7 10 14 15 17 19 21 23 25 30 32 37 43 45 0\n3 4 8 11 15 16 24 27 28 30 31 32 39 41 43 44 46 0\n"
  "80 1 5 6 9 12 13 18 20 22 26 29 33 35 36 40 42 0 32 33 77 0\n81 2 7 10 15 17 19 23 30 37 43 45 0 21 28 29 33 78 0\n82 3 4 8 11 15 16 24 28 30 31 39 41 43 44 46 0 32 33 79 0\n83 60 0 61 62 59 60 37 38 42 43 44 39 40 41 4 26 30 1 3 5 6 2 80 0\n84 61 0 83 63 0\n85 -68 0 84 76 74 0\n86 64 17 0 28 33 29 21 25 9 66 67 65 45 47 48 12 11 23 8 10 81 0\n87 58 0 85 57 58 56 34 35 36 27 31 86 73 70 71 68 69 49 50 51 54 55 52 53 7 18 19 14 13 17 16 20 15 22 82 0\n88 62 0 87 83 64 0\n89 -67 0 88 76 75 0\n90 -64 0 89 72 0\n91 -52 0 90 67 0\n92 17 0 90 86 0\n93 -45 0 91 46 0\n94 0 92 93 24 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record012_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record014
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "398b329c9707ce4b8ab2b1aa699a9687a699964d8763386e2785e0fb61e47319c789b2719a659996479b15a5a5595955351d68d934cd1b61d2745d0f783d0ec368d63c4e9364e531cf0ba2d8b92ccb1ae1b46c9b16c3b61cc749ca745c9715c2f4c8660d88e1381ee07114c68992619194352344d0758348c6344c3322c4b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6db6db49249349a4934db6da49249249b4934d3492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 70), (facetIndex 72)]))
 (.branch 2
 (.leaf ([(facetIndex 57), (facetIndex 84)]))
 (.leaf ([(facetIndex 92), (facetIndex 93)]))))
 (.branch 4
 (.leaf ([(facetIndex 50), (facetIndex 69), (facetIndex 74), (facetIndex 81)]))
 (.branch 5
 (.leaf ([(facetIndex 94), (facetIndex 95), (facetIndex 103)]))
 (.leaf ([(facetIndex 102)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 56), (facetIndex 73)]))
 (.branch 8
 (.leaf ([(facetIndex 99), (facetIndex 105)]))
 (.leaf ([(facetIndex 48), (facetIndex 52), (facetIndex 76)]))))
 (.branch 11
 (.branch 10
 (.leaf ([(facetIndex 96), (facetIndex 97), (facetIndex 98)]))
 (.leaf ([(facetIndex 100), (facetIndex 101), (facetIndex 106)])))
 (.branch 12
 (.leaf ([(facetIndex 71)]))
 (.leaf ([(facetIndex 104)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "a7c45aa7999442200000001003000080360b03000000000001600080308z30;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 13
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
def grouped3_0014 : List Nat := [6, 7, 8, 9, 10, 11, 12]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [7, 8]
def grouped3_0017 : List Nat := [8]
def grouped3_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [9, 10]
def grouped3_0020 : List Nat := [9, 10, 11, 12]
def grouped3_0021 : List Nat := [10]
def grouped3_0022 : List Nat := [11, 12]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record014" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record014" 68

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record014" "{\"ridges\":[[12,386],[19,584],[22,784],[23,896],[37,386],[45,584],[46,386],[48,778],[51,386],[52,658],[53,784],[55,386],[56,706],[57,834],[58,896],[65,584],[73,708],[75,584],[76,408],[78,784],[79,577],[80,896],[81,624],[82,784],[83,784],[83,896],[84,864],[96,408],[97,658],[98,778],[99,706],[100,778],[101,658],[105,708],[106,408]],\"owners\":[[12,386,[92,93,96,100,101],[37,46,51,55,58]],[37,386,[96,100,101],[12,46,51,55,58,92,93]],[46,386,[92,93,101],[12,37,51,55,58,96,100]],[51,386,[93,100],[12,37,46,55,58,92,96,101]],[55,386,[92,96,100,101],[12,37,46,51,58,93]],[79,577,[50,57,69,81,84],[19,45,56,65,73,75]],[19,584,[95,99,103,105],[45,65,75,79]],[45,584,[103,105],[19,65,75,79,95,99]],[65,584,[95,99],[19,45,75,79,103,105]],[75,584,[99,105],[19,45,65,79,95,103]],[22,784,[98,101,106],[53,78,82,83]],[53,784,[106],[22,78,82,83,98,101]],[78,784,[101],[22,53,82,83,98,106]],[82,784,[98,101,106],[22,53,78,83]],[83,784,[98],[22,53,78,82,101,106]],[23,896,[100,101,106],[58,80,83]],[58,896,[106],[23,80,83,100,101]],[80,896,[101],[23,58,83,100,106]],[83,896,[100],[23,58,80,101,106]],[48,778,[98,100],[]],[98,778,[48,100],[]],[100,778,[48,98],[]],[52,658,[97,101],[]],[97,658,[52,101],[]],[101,658,[52,97],[]],[56,706,[99],[]],[99,706,[56],[]],[57,834,[],[]],[73,708,[105],[]],[105,708,[73],[]],[76,408,[96,106],[]],[96,408,[76,106],[]],[106,408,[76,96],[]],[81,624,[],[]],[84,864,[],[]]],\"edges\":[[41,[19,45,50,56,57,65,69,73,75,79,81,84,95,99,103,105]],[42,[12,23,37,46,51,55,58,70,72,76,80,83,92,93,96,100,101,106]],[44,[22,23,48,53,57,58,78,80,82,83,84,98,100,101,106]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record014" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record014\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-5],[-26,-21],[-37,-16],[-37,-36],[-38,-37],[-39,-37],[-1,31,32,34,38,39],[-5,34,38,39],[-7,31,32,39],[-10,32,38],[-13,31,34,38,39],[-25,9,15,18,27,30],[-2,33,37,40,41],[-6,40,41],[-17,33,37],[-22,37,41],[-3,36,39,42],[-12,42],[-24,39],[-28,36,39,42],[-29,36],[-4,38,39,42],[-16,42],[-26,39],[-29,38],[-8,36,38],[-36,8,38],[-38,8,36],[-11,35,39],[-35,11,39],[-39,11,35],[-14,37],[-37,14],[-15],[-21,41],[-41,21],[-23,34,42],[-34,23,42],[-42,23,34],[-27],[-30],[-19,43],[-20,43],[-31,44],[-32,44],[-9,45],[-18,45],[-33,46],[-40,46],[-14,47],[-21,47],[-48,37,41],[-37,48],[-41,48],[-49,8,11,23],[-8,49],[-11,49],[-23,49],[-50,34,35,36],[-34,50],[-35,50],[-36,50],[-51,38,39,42],[-38,51],[-39,51],[-42,51],[-44,52],[-52,53],[-43,53],[-46,54],[-54,55],[-45,55],[-55,56],[-53,56],[-57,48,49],[-49,57],[-48,57],[-48,-49,58],[-57,59],[-47,-57,60],[-47,-58,61],[-62,50,51],[-51,62],[-50,62],[-50,-51,63],[-62,64],[-63,65],[-65,66],[-59,-64,66],[-60,66],[-60,-64,67],[-61,67],[-67,68],[-56,-66,68],[-68],[2,6,9,14,15,17,18,21,22,25,27,30,33,37,40,41],[1,4,5,7,10,13,16,19,20,23,26,29,31,32,34,38,39,42],[3,4,8,12,15,16,24,26,28,29,30,36,38,39,42]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":56,\"b\":37},{\"tag\":\"incompatible\",\"a\":80,\"b\":73},{\"tag\":\"incompatible\",\"a\":99,\"b\":58},{\"tag\":\"incompatible\",\"a\":99,\"b\":98},{\"tag\":\"incompatible\",\"a\":100,\"b\":99},{\"tag\":\"incompatible\",\"a\":101,\"b\":99},{\"tag\":\"mate\",\"ridge\":386,\"a\":12,\"owners\":[92,93,96,100,101]},{\"tag\":\"mate\",\"ridge\":386,\"a\":37,\"owners\":[96,100,101]},{\"tag\":\"mate\",\"ridge\":386,\"a\":46,\"owners\":[92,93,101]},{\"tag\":\"mate\",\"ridge\":386,\"a\":51,\"owners\":[93,100]},{\"tag\":\"mate\",\"ridge\":386,\"a\":55,\"owners\":[92,96,100,101]},{\"tag\":\"mate\",\"ridge\":577,\"a\":79,\"owners\":[50,57,69,81,84]},{\"tag\":\"mate\",\"ridge\":584,\"a\":19,\"owners\":[95,99,103,105]},{\"tag\":\"mate\",\"ridge\":584,\"a\":45,\"owners\":[103,105]},{\"tag\":\"mate\",\"ridge\":584,\"a\":65,\"owners\":[95,99]},{\"tag\":\"mate\",\"ridge\":584,\"a\":75,\"owners\":[99,105]},{\"tag\":\"mate\",\"ridge\":784,\"a\":22,\"owners\":[98,101,106]},{\"tag\":\"mate\",\"ridge\":784,\"a\":53,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":784,\"a\":78,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":784,\"a\":82,\"owners\":[98,101,106]},{\"tag\":\"mate\",\"ridge\":784,\"a\":83,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":896,\"a\":23,\"owners\":[100,101,106]},{\"tag\":\"mate\",\"ridge\":896,\"a\":58,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":896,\"a\":80,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":896,\"a\":83,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":778,\"a\":48,\"owners\":[98,100]},{\"tag\":\"mate\",\"ridge\":778,\"a\":98,\"owners\":[48,100]},{\"tag\":\"mate\",\"ridge\":778,\"a\":100,\"owners\":[48,98]},{\"tag\":\"mate\",\"ridge\":658,\"a\":52,\"owners\":[97,101]},{\"tag\":\"mate\",\"ridge\":658,\"a\":97,\"owners\":[52,101]},{\"tag\":\"mate\",\"ridge\":658,\"a\":101,\"owners\":[52,97]},{\"tag\":\"mate\",\"ridge\":706,\"a\":56,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":706,\"a\":99,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":834,\"a\":57,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":708,\"a\":73,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":708,\"a\":105,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":408,\"a\":76,\"owners\":[96,106]},{\"tag\":\"mate\",\"ridge\":408,\"a\":96,\"owners\":[76,106]},{\"tag\":\"mate\",\"ridge\":408,\"a\":106,\"owners\":[76,96]},{\"tag\":\"mate\",\"ridge\":624,\"a\":81,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":864,\"a\":84,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-19,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":72,\"full_literals\":[-20,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":92,\"full_literals\":[-31,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":93,\"full_literals\":[-32,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":50,\"full_literals\":[-9,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":69,\"full_literals\":[-18,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":95,\"full_literals\":[-33,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":103,\"full_literals\":[-40,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":56,\"full_literals\":[-14,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":73,\"full_literals\":[-21,47]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[99,105],\"full_literals\":[-48,37,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":99,\"full_literals\":[-37,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":105,\"full_literals\":[-41,48]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[48,52,76],\"full_literals\":[-49,8,11,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":48,\"full_literals\":[-8,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":52,\"full_literals\":[-11,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":76,\"full_literals\":[-23,49]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[96,97,98],\"full_literals\":[-50,34,35,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":96,\"full_literals\":[-34,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":97,\"full_literals\":[-35,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":98,\"full_literals\":[-36,50]},{\"tag\":\"group_or\",\"kind\":3,\"index\":10,\"members\":[100,101,106],\"full_literals\":[-51,38,39,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":100,\"full_literals\":[-38,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":101,\"full_literals\":[-39,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":106,\"full_literals\":[-42,51]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-48,-49,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-57,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-47,-58,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-51,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0014\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0014\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-64,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0014\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-56,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[19,45,50,56,57,65,69,73,75,79,81,84,95,99,103,105]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[12,23,37,46,51,55,58,70,72,76,80,83,92,93,96,100,101,106]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[22,23,48,53,57,58,78,80,82,83,84,98,100,101,106]}]}"
  "p cnf 68 98\n-14 -5 0\n-26 -21 0\n-37 -16 0\n-37 -36 0\n-38 -37 0\n-39 -37 0\n-1 31 32 34 38 39 0\n-5 34 38 39 0\n-7 31 32 39 0\n-10 32 38 0\n-13 31 34 38 39 0\n-25 9 15 18 27 30 0\n-2 33 37 40 41 0\n-6 40 41 0\n-17 33 37 0\n-22 37 41 0\n-3 36 39 42 0\n-12 42 0\n-24 39 0\n-28 36 39 42 0\n-29 36 0\n-4 38 39 42 0\n-16 42 0\n-26 39 0\n-29 38 0\n-8 36 38 0\n-36 8 38 0\n-38 8 36 0\n-11 35 39 0\n-35 11 39 0\n-39 11 35 0\n-14 37 0\n-37 14 0\n-15 0\n-21 41 0\n-41 21 0\n-23 34 42 0\n-34 23 42 0\n-42 23 34 0\n-27 0\n-30 0\n-19 43 0\n-20 43 0\n-31 44 0\n-32 44 0\n-9 45 0\n-18 45 0\n-33 46 0\n-40 46 0\n-14 47 0\n-21 47 0\n-48 37 41 0\n-37 48 0\n-41 48 0\n-49 8 11 23 0\n-8 49 0\n-11 49 0\n-23 49 0\n-50 34 35 36 0\n-34 50 0\n-35 50 0\n-36 50 0\n-51 38 39 42 0\n-38 51 0\n-39 51 0\n-42 51 0\n-44 52 0\n-52 53 0\n-43 53 0\n-46 54 0\n-54 55 0\n-45 55 0\n-55 56 0\n-53 56 0\n-57 48 49 0\n-49 57 0\n-48 57 0\n-48 -49 58 0\n-57 59 0\n-47 -57 60 0\n-47 -58 61 0\n-62 50 51 0\n-51 62 0\n-50 62 0\n-50 -51 63 0\n-62 64 0\n-63 65 0\n-65 66 0\n-59 -64 66 0\n-60 66 0\n-60 -64 67 0\n-61 67 0\n-67 68 0\n-56 -66 68 0\n-68 0\n2 6 9 14 15 17 18 21 22 25 27 30 33 37 40 41 0\n1 4 5 7 10 13 16 19 20 23 26 29 31 32 34 38 39 42 0\n3 4 8 12 15 16 24 26 28 29 30 36 38 39 42 0\n"
  "99 -67 0 95 93 0\n100 -61 0 99 92 0\n101 2 6 9 14 17 18 21 22 25 33 37 40 41 0 34 40 41 96 0\n102 3 4 8 12 16 24 26 28 29 36 38 39 42 0 34 41 98 0\n103 48 55 0 34 40 41 72 46 47 12 71 70 49 48 53 54 32 15 13 35 14 16 101 0\n104 -37 56 0 100 99 73 103 77 74 68 67 45 44 69 43 42 3 4 5 6 33 21 10 24 9 1 50 81 80 78 91 58 86 83 84 66 60 22 7 11 97 0\n105 56 0 100 99 73 74 68 69 67 42 43 44 45 103 77 104 52 36 2 51 81 80 78 91 58 86 83 84 64 65 66 60 25 10 9 23 22 8 7 11 97 0\n106 -66 0 105 95 94 0\n107 -65 0 106 88 0\n108 -60 0 106 90 0\n109 -63 0 107 87 0\n110 -57 0 108 106 79 80 89 50 51 86 33 36 83 84 52 64 65 66 60 61 62 75 37 29 26 55 0\n111 -49 0 110 76 0\n112 -8 0 111 56 0\n113 -11 0 111 57 0\n114 -23 0 111 58 0\n115 62 0 112 83 84 64 65 66 62 25 19 24 18 23 17 20 22 102 0\n116 51 0 115 112 113 114 64 65 66 82 27 30 38 59 0\n117 -50 0 116 109 85 0\n118 -34 0 117 60 0\n119 -35 0 117 61 0\n120 -36 0 117 62 0\n121 -42 0 118 114 39 0\n122 -39 0 119 113 31 0\n123 -38 0 120 112 28 0\n124 0 121 123 122 116 63 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record014_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record017
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e6364e538cc729c6707cb4b8a6aa9a1eb86c9a66a5876c3a8e6392e1ba1e2785e0fb91b45a966479e174559715a5595954756346d4749d1743de0ec368e9394cd31cd8b4acab1ac5b0ef07a1d8791d2785c970dd0f23c4f9512ca4a5226a4619a161582e079894a499494651550d0b41d18c9314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db4da6da49b6924936936d36d249249b6924924936d2492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 68)]))
 (.leaf ([(facetIndex 87)])))
 (.branch 3
 (.leaf ([(facetIndex 92)]))
 (.branch 4
 (.leaf ([(facetIndex 66), (facetIndex 98)]))
 (.leaf ([(facetIndex 38), (facetIndex 40), (facetIndex 51), (facetIndex 81), (facetIndex 85)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 39), (facetIndex 52), (facetIndex 53), (facetIndex 64)]))
 (.branch 7
 (.leaf ([(facetIndex 63), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 79), (facetIndex 89), (facetIndex 90)]))))
 (.branch 9
 (.leaf ([(facetIndex 62), (facetIndex 80), (facetIndex 95)]))
 (.branch 10
 (.leaf ([(facetIndex 93), (facetIndex 94), (facetIndex 99)]))
 (.leaf ([(facetIndex 67), (facetIndex 86), (facetIndex 96), (facetIndex 97)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "93aa899207701a400048700000066000a30568000000005540000000000454z26;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0, 1]
def grouped3_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0003 : List Nat := [2]
def grouped3_0004 : List Nat := [2, 3, 4]
def grouped3_0005 : List Nat := [3]
def grouped3_0006 : List Nat := [3, 4]
def grouped3_0007 : List Nat := [4]
def grouped3_0008 : List Nat := [5]
def grouped3_0009 : List Nat := [5, 6, 7]
def grouped3_0010 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0011 : List Nat := [6]
def grouped3_0012 : List Nat := [6, 7]
def grouped3_0013 : List Nat := [7]
def grouped3_0014 : List Nat := [8]
def grouped3_0015 : List Nat := [8, 9, 10]
def grouped3_0016 : List Nat := [9]
def grouped3_0017 : List Nat := [9, 10]
def grouped3_0018 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record017" "{\"atoms\":[{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record017" 58

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record017" "{\"ridges\":[[18,392],[27,656],[38,390],[46,392],[50,656],[51,418],[53,771],[53,896],[59,392],[62,404],[64,772],[66,833],[67,645],[67,896],[69,392],[70,392],[72,896],[80,652],[83,656],[85,802],[86,390],[86,772],[86,896],[88,656],[90,778],[90,896],[91,656],[93,404],[94,652],[95,772],[95,792],[96,652],[96,772],[97,404],[97,772],[98,864],[99,792],[99,896]],\"owners\":[[18,392,[79,89,90,93,96,99],[46,59,69,70]],[46,392,[93,96,99],[18,59,69,70,79,89,90]],[59,392,[89,90,99],[18,46,69,70,79,93,96]],[69,392,[79,89,90,96],[18,46,59,70,93,99]],[70,392,[79,90,93,96,99],[18,46,59,69,89]],[27,656,[63,71,72,94,97,99],[50,83,88,91]],[50,656,[94,97,99],[27,63,71,72,83,88,91]],[83,656,[71,72,99],[27,50,63,88,91,94,97]],[88,656,[63,71,72,97],[27,50,83,91,94,99]],[91,656,[63,72,94,97,99],[27,50,71,83,88]],[38,390,[79,86],[]],[86,390,[38,79],[]],[67,645,[39,63],[]],[53,771,[40],[]],[64,772,[81,85,86,96,98],[40,66,67,95,97]],[86,772,[64,66,95,98],[40,67,81,85,96,97]],[95,772,[40,66,67,85,86,98],[64,81,96,97]],[96,772,[40,64,66,85,98],[67,81,86,95,97]],[97,772,[40,66,81,85,98],[64,67,86,95,96]],[51,418,[89],[]],[53,896,[96,97,99],[67,72,86,90]],[67,896,[90,99],[53,72,86,96,97]],[72,896,[86,90,96],[53,67,97,99]],[86,896,[72,99],[53,67,90,96,97]],[90,896,[67,72,97],[53,86,96,99]],[99,896,[53,67,86],[72,90,96,97]],[62,404,[93,97],[]],[93,404,[62,97],[]],[97,404,[62,93],[]],[66,833,[],[]],[80,652,[94,96],[]],[94,652,[80,96],[]],[96,652,[80,94],[]],[90,778,[81],[]],[85,802,[],[]],[95,792,[99],[]],[99,792,[95],[]],[98,864,[],[]]],\"edges\":[[42,[18,38,46,51,53,59,62,67,69,70,72,79,86,89,90,93,96,97,99]],[43,[27,39,50,52,53,63,67,71,72,80,83,86,88,90,91,94,96,97,99]],[44,[40,53,64,66,67,72,81,85,86,90,95,96,97,98,99]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record017" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record017\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,21,28,29,31,34,37],[-6,31,34,37],[-11,28,29,37],[-17,21,28,29,34],[-18,21,29,31,34,37],[-2,13,19,20,32,35,37],[-7,32,35,37],[-24,19,20,37],[-27,13,19,20,35],[-30,13,20,32,35,37],[-3,21,26],[-26,3,21],[-16,4,13],[-10,5],[-14,23,25,26,34,36],[-26,14,15,33,36],[-33,5,15,16,25,26,36],[-34,5,14,15,25,36],[-35,5,15,23,25,36],[-8,28],[-10,34,35,37],[-16,29,37],[-20,26,29,34],[-26,20,37],[-29,16,20,35],[-37,10,16,26],[-12,31,35],[-31,12,35],[-35,12,31],[-15],[-22,32,34],[-32,22,34],[-34,22,32],[-29,23],[-25],[-33,37],[-37,33],[-36],[-3,38],[-5,38],[-23,38],[-4,39],[-9,39],[-14,39],[-13,40],[-19,40],[-20,40],[-21,41],[-28,41],[-29,41],[-12,42],[-22,42],[-33,42],[-43,31,32,37],[-31,43],[-32,43],[-37,43],[-44,16,26,34,35],[-16,44],[-26,44],[-34,44],[-35,44],[-38,45],[-45,46],[-46,47],[-41,48],[-40,48],[-40,-41,49],[-48,50],[-49,51],[-39,50],[-39,-48,51],[-44,52],[-43,52],[-43,-44,53],[-52,54],[-53,55],[-42,-52,55],[-55,56],[-50,-54,56],[-50,-55,57],[-51,56],[-51,-54,57],[-57,58],[-47,-56,58],[-58],[1,3,6,8,10,11,12,16,17,18,20,21,26,28,29,31,34,35,37],[2,4,7,9,10,13,16,19,20,22,24,26,27,29,30,32,34,35,37],[5,10,14,15,16,20,23,25,26,29,33,34,35,36,37]],\"atoms\":[{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":392,\"a\":18,\"owners\":[79,89,90,93,96,99]},{\"tag\":\"mate\",\"ridge\":392,\"a\":46,\"owners\":[93,96,99]},{\"tag\":\"mate\",\"ridge\":392,\"a\":59,\"owners\":[89,90,99]},{\"tag\":\"mate\",\"ridge\":392,\"a\":69,\"owners\":[79,89,90,96]},{\"tag\":\"mate\",\"ridge\":392,\"a\":70,\"owners\":[79,90,93,96,99]},{\"tag\":\"mate\",\"ridge\":656,\"a\":27,\"owners\":[63,71,72,94,97,99]},{\"tag\":\"mate\",\"ridge\":656,\"a\":50,\"owners\":[94,97,99]},{\"tag\":\"mate\",\"ridge\":656,\"a\":83,\"owners\":[71,72,99]},{\"tag\":\"mate\",\"ridge\":656,\"a\":88,\"owners\":[63,71,72,97]},{\"tag\":\"mate\",\"ridge\":656,\"a\":91,\"owners\":[63,72,94,97,99]},{\"tag\":\"mate\",\"ridge\":390,\"a\":38,\"owners\":[79,86]},{\"tag\":\"mate\",\"ridge\":390,\"a\":86,\"owners\":[38,79]},{\"tag\":\"mate\",\"ridge\":645,\"a\":67,\"owners\":[39,63]},{\"tag\":\"mate\",\"ridge\":771,\"a\":53,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":772,\"a\":64,\"owners\":[81,85,86,96,98]},{\"tag\":\"mate\",\"ridge\":772,\"a\":86,\"owners\":[64,66,95,98]},{\"tag\":\"mate\",\"ridge\":772,\"a\":95,\"owners\":[40,66,67,85,86,98]},{\"tag\":\"mate\",\"ridge\":772,\"a\":96,\"owners\":[40,64,66,85,98]},{\"tag\":\"mate\",\"ridge\":772,\"a\":97,\"owners\":[40,66,81,85,98]},{\"tag\":\"mate\",\"ridge\":418,\"a\":51,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":896,\"a\":53,\"owners\":[96,97,99]},{\"tag\":\"mate\",\"ridge\":896,\"a\":67,\"owners\":[90,99]},{\"tag\":\"mate\",\"ridge\":896,\"a\":72,\"owners\":[86,90,96]},{\"tag\":\"mate\",\"ridge\":896,\"a\":86,\"owners\":[72,99]},{\"tag\":\"mate\",\"ridge\":896,\"a\":90,\"owners\":[67,72,97]},{\"tag\":\"mate\",\"ridge\":896,\"a\":99,\"owners\":[53,67,86]},{\"tag\":\"mate\",\"ridge\":404,\"a\":62,\"owners\":[93,97]},{\"tag\":\"mate\",\"ridge\":404,\"a\":93,\"owners\":[62,97]},{\"tag\":\"mate\",\"ridge\":404,\"a\":97,\"owners\":[62,93]},{\"tag\":\"mate\",\"ridge\":833,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":652,\"a\":80,\"owners\":[94,96]},{\"tag\":\"mate\",\"ridge\":652,\"a\":94,\"owners\":[80,96]},{\"tag\":\"mate\",\"ridge\":652,\"a\":96,\"owners\":[80,94]},{\"tag\":\"mate\",\"ridge\":778,\"a\":90,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":802,\"a\":85,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":792,\"a\":95,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":792,\"a\":99,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":864,\"a\":98,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":38,\"full_literals\":[-3,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":40,\"full_literals\":[-5,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":81,\"full_literals\":[-23,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":39,\"full_literals\":[-4,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":52,\"full_literals\":[-9,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":64,\"full_literals\":[-14,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":63,\"full_literals\":[-13,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":71,\"full_literals\":[-19,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":72,\"full_literals\":[-20,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":79,\"full_literals\":[-21,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":89,\"full_literals\":[-28,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":90,\"full_literals\":[-29,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":62,\"full_literals\":[-12,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":80,\"full_literals\":[-22,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":95,\"full_literals\":[-33,42]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[93,94,99],\"full_literals\":[-43,31,32,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":93,\"full_literals\":[-31,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":94,\"full_literals\":[-32,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":99,\"full_literals\":[-37,43]},{\"tag\":\"group_or\",\"kind\":3,\"index\":10,\"members\":[67,86,96,97],\"full_literals\":[-44,16,26,34,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":67,\"full_literals\":[-16,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":86,\"full_literals\":[-26,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":96,\"full_literals\":[-34,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":97,\"full_literals\":[-35,44]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-41,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-48,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-44,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-53,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-52,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-50,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-54,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-47,-56,58],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[18,38,46,51,53,59,62,67,69,70,72,79,86,89,90,93,96,97,99]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[27,39,50,52,53,63,67,71,72,80,83,86,88,90,91,94,96,97,99]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[40,53,64,66,67,72,81,85,86,90,95,96,97,98,99]}]}"
  "p cnf 58 89\n-1 21 28 29 31 34 37 0\n-6 31 34 37 0\n-11 28 29 37 0\n-17 21 28 29 34 0\n-18 21 29 31 34 37 0\n-2 13 19 20 32 35 37 0\n-7 32 35 37 0\n-24 19 20 37 0\n-27 13 19 20 35 0\n-30 13 20 32 35 37 0\n-3 21 26 0\n-26 3 21 0\n-16 4 13 0\n-10 5 0\n-14 23 25 26 34 36 0\n-26 14 15 33 36 0\n-33 5 15 16 25 26 36 0\n-34 5 14 15 25 36 0\n-35 5 15 23 25 36 0\n-8 28 0\n-10 34 35 37 0\n-16 29 37 0\n-20 26 29 34 0\n-26 20 37 0\n-29 16 20 35 0\n-37 10 16 26 0\n-12 31 35 0\n-31 12 35 0\n-35 12 31 0\n-15 0\n-22 32 34 0\n-32 22 34 0\n-34 22 32 0\n-29 23 0\n-25 0\n-33 37 0\n-37 33 0\n-36 0\n-3 38 0\n-5 38 0\n-23 38 0\n-4 39 0\n-9 39 0\n-14 39 0\n-13 40 0\n-19 40 0\n-20 40 0\n-21 41 0\n-28 41 0\n-29 41 0\n-12 42 0\n-22 42 0\n-33 42 0\n-43 31 32 37 0\n-31 43 0\n-32 43 0\n-37 43 0\n-44 16 26 34 35 0\n-16 44 0\n-26 44 0\n-34 44 0\n-35 44 0\n-38 45 0\n-45 46 0\n-46 47 0\n-41 48 0\n-40 48 0\n-40 -41 49 0\n-48 50 0\n-49 51 0\n-39 50 0\n-39 -48 51 0\n-44 52 0\n-43 52 0\n-43 -44 53 0\n-52 54 0\n-53 55 0\n-42 -52 55 0\n-55 56 0\n-50 -54 56 0\n-50 -55 57 0\n-51 56 0\n-51 -54 57 0\n-57 58 0\n-47 -56 58 0\n-58 0\n1 3 6 8 10 11 12 16 17 18 20 21 26 28 29 31 34 35 37 0\n2 4 7 9 10 13 16 19 20 22 24 26 27 29 30 32 34 35 37 0\n5 10 14 15 16 20 23 25 26 29 33 34 35 36 37 0\n"
  "90 -57 0 86 84 0\n91 5 10 14 16 20 23 26 29 33 34 35 37 0 30 35 38 89 0\n92 50 38 0 38 35 30 40 41 19 34 14 39 69 71 66 67 42 44 48 45 47 18 12 13 17 26 91 0\n93 -16 38 0 90 92 81 77 41 34 22 59 57 75 0\n94 -37 38 0 90 93 92 81 77 40 14 26 57 60 75 0\n95 -44 38 0 30 35 38 90 94 93 92 81 77 40 41 19 39 73 75 76 78 56 83 52 70 33 58 12 24 48 47 68 0\n96 38 0 30 38 35 40 41 14 34 19 93 94 36 95 60 61 23 15 91 0\n97 45 0 96 63 0\n98 46 0 97 64 0\n99 47 0 98 65 0\n100 -56 0 99 86 85 0\n101 -55 0 100 79 0\n102 -51 0 100 82 0\n103 -53 0 101 77 0\n104 -49 0 102 70 0\n105 -41 32 44 16 37 0 104 102 61 31 62 7 21 60 66 68 72 45 46 47 42 43 6 9 8 10 25 88 0\n106 43 44 16 37 0 62 61 21 60 55 56 27 2 105 48 49 50 1 5 11 4 20 3 23 87 0\n107 44 16 37 0 101 61 62 106 74 78 51 52 28 32 54 0\n108 16 37 0 103 101 100 38 30 36 107 73 75 76 78 55 56 80 51 52 29 71 33 44 58 16 0\n109 -16 37 0 100 22 59 50 73 66 76 69 80 0\n110 37 0 108 109 0\n111 33 0 110 37 0\n112 43 0 110 57 0\n113 42 0 111 53 0\n114 52 0 112 74 0\n115 0 113 114 101 78 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00005.record017_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00005.record017
