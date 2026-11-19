module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00038Data
public import GraphInputsRow24Part00038Frames
public import GraphInputsRow24Part00038Leaves
public import GraphInputsRow24Part00038Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record006
def vertexColumn : Fields := ⟨10, hexnat% "bcaaa3a2eb262d876c398e538ce8b8ae4789e0faa98e4b9c94b51d70d6354d3362d2b51d2743dc8ea38ccb31ce8b62e4b52ccb8acab86d1b26c3bc1d8751cc789d2719d1725e0f0bc5cc285a298560d90e2384e07b09164a5154354348d1341dc0e2328c530ce0b42c8b12c1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db49249a4936da4924d2492492492492492492492449249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fbffe56602c7f3800000000", hexnat% "400080020000c000000000", 2017612633061982208, hexnat% "298000000000000000", hexnat% "1000000800000000000", 131448814123876352]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffe46600c7ff800000000", 2161727821137838080, hexnat% "1808000000000000000", hexnat% "390000000000000000", 140596750866972672]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c1 c3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fab3f7fe02c7f3800000000", hexnat% "400080020000c000000000", 2017612633061982208, hexnat% "14c0000000000000000000", 131589551612231680]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c1 c5
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fe3ffffe00c637800000000", 31336081391616, 2161727821137838080, hexnat% "1c00000000000000000000", 140596750866972672]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c1 c7
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f433e86420000e000000000", hexnat% "798000001000000000", hexnat% "3cc0000000000000000000", 4323458940810559488, hexnat% "8001000000800800000000", 65970697666560, 143904081843322880]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c10 c6
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c12 c2
  c13
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f31a2eb2665956358b6c3a2e2b86e4789e0fb192e72565555354b5c362d2b46d4749d0f723a8f1364d5334cb3c2e4b2ac6b86d1b26c3bc1d8751cc789d2719c3783d0f23c5c8a85a29916258561382e07a29164a5454951544d0b41dc0e2328d1324c5382c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6d249a4924db492692492492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 38), (facetIndex 41), (facetIndex 46), (facetIndex 51), (facetIndex 54), (facetIndex 59)]))
 (.leaf ([(facetIndex 61), (facetIndex 64), (facetIndex 65), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 62), (facetIndex 63), (facetIndex 68), (facetIndex 69), (facetIndex 70), (facetIndex 71)]))
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 84), (facetIndex 85)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 37), (facetIndex 49), (facetIndex 52), (facetIndex 53), (facetIndex 60)]))
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 80)])))
 (.branch 7
 (.leaf ([(facetIndex 47), (facetIndex 48), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58)]))
 (.branch 8
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 39), (facetIndex 40), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 45)]))
 (.leaf ([(facetIndex 50)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "333305553330002222011122140666604408466077770770477z23;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 73)]))
 (.branch 2
 (.leaf ([(facetIndex 87)]))
 (.leaf ([(facetIndex 89)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 67), (facetIndex 72)]))
 (.leaf ([(facetIndex 74), (facetIndex 81)])))
 (.branch 6
 (.leaf ([(facetIndex 86)]))
 (.leaf ([(facetIndex 88)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "163400200001030006z32;"⟩
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
def grouped2_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0009 : List Nat := [5]
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record000" 88

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record000" "{\"ridges\":[[2,38],[9,521],[14,545],[17,41],[22,37],[22,161],[24,41],[24,521],[24,545],[24,552],[31,38],[31,162],[33,42],[33,522],[33,546],[33,552],[38,37],[38,38],[41,545],[49,521],[50,41],[50,42],[51,41],[52,521],[52,522],[53,770],[54,35],[54,161],[54,162],[59,545],[59,546],[60,545],[61,41],[64,37],[64,41],[64,44],[65,41],[66,44],[66,521],[67,521],[68,161],[72,37],[72,545],[72,804],[73,41],[74,521],[74,792],[78,38],[78,44],[79,42],[79,44],[80,44],[80,522],[80,552],[82,162],[86,38],[86,546],[86,804],[87,184],[88,522],[88,792],[89,44]],\"owners\":[[54,35,[2,7,14,39,40,50,60],[13,38,46]],[9,521,[24,66,67,74],[37,49,52,53]],[24,521,[9,37,49,52,53,67,74],[66]],[49,521,[24,66,67],[9,37,52,53,74]],[52,521,[24,66,67,74],[9,37,49,53]],[74,521,[9,24,37,52,66],[49,53,67]],[33,522,[9,37,49,52,53,81,88],[80]],[88,522,[9,33,37,52,80],[49,53,81]],[22,161,[13,51,54,59,73],[65,68]],[54,161,[22,65],[13,51,59,68,73]],[68,161,[13,51,59],[22,54,65,73]],[31,162,[13,51,54,59,87],[79,82]],[54,162,[31,79],[13,51,59,82,87]],[82,162,[13,51,59],[31,54,79,87]],[14,545,[24,66,72],[41,59,60]],[41,545,[24],[14,59,60,66,72]],[59,545,[24,66,72],[14,41,60]],[60,545,[24,66],[14,41,59,72]],[72,545,[14,24,59],[41,60,66]],[53,770,[86],[15,45,58,60,81,88]],[79,44,[17,61,64,66],[26,65,75,78,80,89]],[24,552,[33,80],[66]],[33,552,[24,66],[80]],[80,552,[24],[33,66]],[72,804,[86],[]],[86,804,[72],[]],[87,184,[73,89],[]],[74,792,[88],[]],[88,792,[74],[]]],\"edges\":[[29,[9,24,33,37,49,52,53,66,67,74,80,81,88]],[36,[13,22,31,51,54,59,65,68,73,79,82,87,89]],[38,[14,24,33,41,59,60,66,72,80,86]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-11],[-14,-11],[-14,-13],[-15,-14],[-17,-4],[-18,-13],[-18,-14],[-19,-13],[-19,-14],[-20,-13],[-20,-14],[-21,-13],[-22,-3],[-23,-22],[-25,-22],[-26,-3],[-26,-13],[-27,-5],[-27,-13],[-28,-2],[-28,-22],[-28,-26],[-28,-27],[-29,-22],[-30,-23],[-31,-22],[-31,-30],[-32,-22],[-32,-30],[-33,-22],[-33,-30],[-35,-15],[-35,-16],[-35,-26],[-35,-29],[-36,-16],[-36,-21],[-36,-27],[-36,-28],[-36,-35],[-37,-14],[-37,-30],[-38,-26],[-39,-17],[-40,-26],[-41,-13],[-41,-17],[-41,-37],[-41,-38],[-41,-40],[-43,-39],[-44,-37],[-44,-39],[-44,-40],[-46,-15],[-46,-26],[-46,-38],[-47,-17],[-47,-39],[-48,-26],[-48,-40],[-48,-41],[-49,-46],[-51,-13],[-51,-16],[-51,-17],[-51,-36],[-51,-40],[-51,-41],[-51,-47],[-51,-48],[-51,-49],[-52,-37],[-52,-39],[-52,-47],[-52,-48],[-53,-12],[-53,-24],[-53,-25],[-53,-29],[-53,-34],[-54,-37],[-54,-39],[-54,-47],[-30,1,2,5,15,16,26,36],[-7,-38,-43],[-14,-38,-43],[-1,-46,-51],[-9,-46,-51],[-14,-46,-51],[-6,-8,-26],[-8,-26,-37],[-8,-26,-39],[-8,-27,-37],[-8,-27,-38],[-8,-38,-44],[-10,-26,-47],[-3,8,40,41,45],[-8,3,13,25,28,29,41,45],[-25,8,40,41],[-28,8,40,41,45],[-45,3,8,13,28,40],[-8,-25,-41],[-8,-28,-41],[-8,-28,-45],[-28,-40,-45],[-10,3,13,25,28,29,49,53],[-53,3,10,13,28,48],[-10,-28,-53],[-28,-48,-53],[-7,4,27,30,35,44],[-30,7,39],[-42,4,27,35],[-9,4,27,30,35,52],[-30,9,47],[-50,4,27,35],[-5,8,40,43],[-17,8],[-35,8,40,43],[-36,8,40],[-43,5,8,35],[-5,-8,-43],[-8,-35,-43],[-10,-35,-51],[-29,51],[-47,6,37,38,40],[-38,-48,-54],[-40,-46,-54],[-8,10,48],[-10,8,40],[-48,8],[-43,51],[-51,43],[-52,44,54],[-45,53],[-53,45],[-55,14,17,22,27,30,35],[-56,37,38,39,40],[-57,13,25,28,29,36],[-58,46,47,48],[-59,23,24,31,32,33,34],[-60,11,12,15,16,18,19,20,21],[-61,26],[-62,55],[-62,56],[-63,62],[-64,57],[-64,58],[-65,60,61],[-66,61],[-67,59,66],[-67,65],[-68,66],[-69,64,68],[-70,64],[-69,67],[-70,68],[-71,63,70],[-71,69],[71],[-72,44],[-44,72],[-73,52],[-52,73],[-74,54],[-54,74],[-75,41,43],[-76,45,49],[-45,76],[-77,51],[-51,77],[-78,53],[-53,78],[-79,73,74],[-74,79],[-73,79],[-80,72,79],[-79,80],[-72,80],[-76,81],[-82,75],[-82,76],[-83,77,78],[-84,78],[-77,-78,84],[-85,82,83],[-81,-84,86],[-87,80,85],[-86,88],[-80,-85,88],[87],[-88],[3,8,10,13,25,28,29,40,41,45,48,49,53],[4,7,9,27,30,35,39,42,44,47,50,52,54],[5,8,10,17,35,36,40,43,48,51]],\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":13},{\"tag\":\"incompatible\",\"a\":42,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":38},{\"tag\":\"incompatible\",\"a\":43,\"b\":37},{\"tag\":\"incompatible\",\"a\":43,\"b\":38},{\"tag\":\"incompatible\",\"a\":44,\"b\":37},{\"tag\":\"incompatible\",\"a\":44,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":37},{\"tag\":\"incompatible\",\"a\":46,\"b\":9},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":46},{\"tag\":\"incompatible\",\"a\":50,\"b\":9},{\"tag\":\"incompatible\",\"a\":50,\"b\":37},{\"tag\":\"incompatible\",\"a\":51,\"b\":14},{\"tag\":\"incompatible\",\"a\":51,\"b\":37},{\"tag\":\"incompatible\",\"a\":52,\"b\":7},{\"tag\":\"incompatible\",\"a\":52,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":46},{\"tag\":\"incompatible\",\"a\":54,\"b\":47},{\"tag\":\"incompatible\",\"a\":55,\"b\":46},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":46},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":57,\"b\":46},{\"tag\":\"incompatible\",\"a\":57,\"b\":54},{\"tag\":\"incompatible\",\"a\":59,\"b\":39},{\"tag\":\"incompatible\",\"a\":59,\"b\":40},{\"tag\":\"incompatible\",\"a\":59,\"b\":50},{\"tag\":\"incompatible\",\"a\":59,\"b\":53},{\"tag\":\"incompatible\",\"a\":60,\"b\":40},{\"tag\":\"incompatible\",\"a\":60,\"b\":45},{\"tag\":\"incompatible\",\"a\":60,\"b\":51},{\"tag\":\"incompatible\",\"a\":60,\"b\":52},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":38},{\"tag\":\"incompatible\",\"a\":61,\"b\":54},{\"tag\":\"incompatible\",\"a\":64,\"b\":50},{\"tag\":\"incompatible\",\"a\":65,\"b\":41},{\"tag\":\"incompatible\",\"a\":66,\"b\":50},{\"tag\":\"incompatible\",\"a\":67,\"b\":37},{\"tag\":\"incompatible\",\"a\":67,\"b\":41},{\"tag\":\"incompatible\",\"a\":67,\"b\":61},{\"tag\":\"incompatible\",\"a\":67,\"b\":64},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":72,\"b\":65},{\"tag\":\"incompatible\",\"a\":73,\"b\":61},{\"tag\":\"incompatible\",\"a\":73,\"b\":65},{\"tag\":\"incompatible\",\"a\":73,\"b\":66},{\"tag\":\"incompatible\",\"a\":78,\"b\":39},{\"tag\":\"incompatible\",\"a\":78,\"b\":50},{\"tag\":\"incompatible\",\"a\":78,\"b\":64},{\"tag\":\"incompatible\",\"a\":79,\"b\":41},{\"tag\":\"incompatible\",\"a\":79,\"b\":65},{\"tag\":\"incompatible\",\"a\":80,\"b\":50},{\"tag\":\"incompatible\",\"a\":80,\"b\":66},{\"tag\":\"incompatible\",\"a\":80,\"b\":67},{\"tag\":\"incompatible\",\"a\":81,\"b\":78},{\"tag\":\"incompatible\",\"a\":86,\"b\":37},{\"tag\":\"incompatible\",\"a\":86,\"b\":40},{\"tag\":\"incompatible\",\"a\":86,\"b\":41},{\"tag\":\"incompatible\",\"a\":86,\"b\":60},{\"tag\":\"incompatible\",\"a\":86,\"b\":66},{\"tag\":\"incompatible\",\"a\":86,\"b\":67},{\"tag\":\"incompatible\",\"a\":86,\"b\":79},{\"tag\":\"incompatible\",\"a\":86,\"b\":80},{\"tag\":\"incompatible\",\"a\":86,\"b\":81},{\"tag\":\"incompatible\",\"a\":87,\"b\":61},{\"tag\":\"incompatible\",\"a\":87,\"b\":65},{\"tag\":\"incompatible\",\"a\":87,\"b\":79},{\"tag\":\"incompatible\",\"a\":87,\"b\":80},{\"tag\":\"incompatible\",\"a\":88,\"b\":36},{\"tag\":\"incompatible\",\"a\":88,\"b\":48},{\"tag\":\"incompatible\",\"a\":88,\"b\":49},{\"tag\":\"incompatible\",\"a\":88,\"b\":53},{\"tag\":\"incompatible\",\"a\":88,\"b\":58},{\"tag\":\"incompatible\",\"a\":89,\"b\":61},{\"tag\":\"incompatible\",\"a\":89,\"b\":65},{\"tag\":\"incompatible\",\"a\":89,\"b\":79},{\"tag\":\"mate\",\"ridge\":35,\"a\":54,\"owners\":[2,7,14,39,40,50,60]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[22,64,72]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[38,64,72]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[2,78,86]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[31,78,86]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[38,78,86]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[17,24,50]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[24,50,61]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[24,50,65]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[24,51,61]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[24,51,64]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[24,64,73]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[33,50,79]},{\"tag\":\"mate\",\"ridge\":521,\"a\":9,\"owners\":[24,66,67,74]},{\"tag\":\"mate\",\"ridge\":521,\"a\":24,\"owners\":[9,37,49,52,53,67,74]},{\"tag\":\"mate\",\"ridge\":521,\"a\":49,\"owners\":[24,66,67]},{\"tag\":\"mate\",\"ridge\":521,\"a\":52,\"owners\":[24,66,67,74]},{\"tag\":\"mate\",\"ridge\":521,\"a\":74,\"owners\":[9,24,37,52,66]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[24,49,67]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[24,52,67]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[24,52,74]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[52,66,74]},{\"tag\":\"mate\",\"ridge\":522,\"a\":33,\"owners\":[9,37,49,52,53,81,88]},{\"tag\":\"mate\",\"ridge\":522,\"a\":88,\"owners\":[9,33,37,52,80]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[33,52,88]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[52,80,88]},{\"tag\":\"mate\",\"ridge\":161,\"a\":22,\"owners\":[13,51,54,59,73]},{\"tag\":\"mate\",\"ridge\":161,\"a\":54,\"owners\":[22,65]},{\"tag\":\"mate\",\"ridge\":161,\"a\":68,\"owners\":[13,51,59]},{\"tag\":\"mate\",\"ridge\":162,\"a\":31,\"owners\":[13,51,54,59,87]},{\"tag\":\"mate\",\"ridge\":162,\"a\":54,\"owners\":[31,79]},{\"tag\":\"mate\",\"ridge\":162,\"a\":82,\"owners\":[13,51,59]},{\"tag\":\"mate\",\"ridge\":545,\"a\":14,\"owners\":[24,66,72]},{\"tag\":\"mate\",\"ridge\":545,\"a\":41,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":545,\"a\":59,\"owners\":[24,66,72]},{\"tag\":\"mate\",\"ridge\":545,\"a\":60,\"owners\":[24,66]},{\"tag\":\"mate\",\"ridge\":545,\"a\":72,\"owners\":[14,24,59]},{\"tag\":\"three\",\"ridge\":545,\"vertices\":[14,24,72]},{\"tag\":\"three\",\"ridge\":545,\"vertices\":[24,59,72]},{\"tag\":\"three\",\"ridge\":546,\"vertices\":[33,59,86]},{\"tag\":\"mate\",\"ridge\":770,\"a\":53,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":44,\"a\":79,\"owners\":[17,61,64,66]},{\"tag\":\"three\",\"ridge\":44,\"vertices\":[64,80,89]},{\"tag\":\"three\",\"ridge\":44,\"vertices\":[66,78,89]},{\"tag\":\"mate\",\"ridge\":552,\"a\":24,\"owners\":[33,80]},{\"tag\":\"mate\",\"ridge\":552,\"a\":33,\"owners\":[24,66]},{\"tag\":\"mate\",\"ridge\":552,\"a\":80,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":804,\"a\":72,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":804,\"a\":86,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":184,\"a\":87,\"owners\":[73,89]},{\"tag\":\"mate\",\"ridge\":792,\"a\":74,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":792,\"a\":88,\"owners\":[74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[38,41,46,51,54,59],\"full_literals\":[-55,14,17,22,27,30,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[61,64,65,66],\"full_literals\":[-56,37,38,39,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[37,49,52,53,60],\"full_literals\":[-57,13,25,28,29,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[78,79,80],\"full_literals\":[-58,46,47,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[47,48,55,56,57,58],\"full_literals\":[-59,23,24,31,32,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[35,36,39,40,42,43,44,45],\"full_literals\":[-60,11,12,15,16,18,19,20,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[50],\"full_literals\":[-61,26]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-63,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,60,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-66,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,59,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-69,64,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-70,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-70,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-71,63,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-71,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[73],\"full_literals\":[-72,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":73,\"full_literals\":[-44,72]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[87],\"full_literals\":[-73,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-52,73]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[89],\"full_literals\":[-74,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":89,\"full_literals\":[-54,74]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[67,72],\"full_literals\":[-75,41,43]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[74,81],\"full_literals\":[-76,45,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-45,76]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[86],\"full_literals\":[-77,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":86,\"full_literals\":[-51,77]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[88],\"full_literals\":[-78,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-53,78]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,73,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,72,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-79,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-76,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-82,75,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-82,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-83,77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-84,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-77,-78,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,82,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-81,-84,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-87,80,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-86,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-80,-85,88],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[9,24,33,37,49,52,53,66,67,74,80,81,88]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[13,22,31,51,54,59,65,68,73,79,82,87,89]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[14,24,33,41,59,60,66,72,80,86]}]}"
  "p cnf 88 195\n-13 -11 0\n-14 -11 0\n-14 -13 0\n-15 -14 0\n-17 -4 0\n-18 -13 0\n-18 -14 0\n-19 -13 0\n-19 -14 0\n-20 -13 0\n-20 -14 0\n-21 -13 0\n-22 -3 0\n-23 -22 0\n-25 -22 0\n-26 -3 0\n-26 -13 0\n-27 -5 0\n-27 -13 0\n-28 -2 0\n-28 -22 0\n-28 -26 0\n-28 -27 0\n-29 -22 0\n-30 -23 0\n-31 -22 0\n-31 -30 0\n-32 -22 0\n-32 -30 0\n-33 -22 0\n-33 -30 0\n-35 -15 0\n-35 -16 0\n-35 -26 0\n-35 -29 0\n-36 -16 0\n-36 -21 0\n-36 -27 0\n-36 -28 0\n-36 -35 0\n-37 -14 0\n-37 -30 0\n-38 -26 0\n-39 -17 0\n-40 -26 0\n-41 -13 0\n-41 -17 0\n-41 -37 0\n-41 -38 0\n-41 -40 0\n-43 -39 0\n-44 -37 0\n-44 -39 0\n-44 -40 0\n-46 -15 0\n-46 -26 0\n-46 -38 0\n-47 -17 0\n-47 -39 0\n-48 -26 0\n-48 -40 0\n-48 -41 0\n-49 -46 0\n-51 -13 0\n-51 -16 0\n-51 -17 0\n-51 -36 0\n-51 -40 0\n-51 -41 0\n-51 -47 0\n-51 -48 0\n-51 -49 0\n-52 -37 0\n-52 -39 0\n-52 -47 0\n-52 -48 0\n-53 -12 0\n-53 -24 0\n-53 -25 0\n-53 -29 0\n-53 -34 0\n-54 -37 0\n-54 -39 0\n-54 -47 0\n-30 1 2 5 15 16 26 36 0\n-7 -38 -43 0\n-14 -38 -43 0\n-1 -46 -51 0\n-9 -46 -51 0\n-14 -46 -51 0\n-6 -8 -26 0\n-8 -26 -37 0\n-8 -26 -39 0\n-8 -27 -37 0\n-8 -27 -38 0\n-8 -38 -44 0\n-10 -26 -47 0\n-3 8 40 41 45 0\n-8 3 13 25 28 29 41 45 0\n-25 8 40 41 0\n-28 8 40 41 45 0\n-45 3 8 13 28 40 0\n-8 -25 -41 0\n-8 -28 -41 0\n-8 -28 -45 0\n-28 -40 -45 0\n-10 3 13 25 28 29 49 53 0\n-53 3 10 13 28 48 0\n-10 -28 -53 0\n-28 -48 -53 0\n-7 4 27 30 35 44 0\n-30 7 39 0\n-42 4 27 35 0\n-9 4 27 30 35 52 0\n-30 9 47 0\n-50 4 27 35 0\n-5 8 40 43 0\n-17 8 0\n-35 8 40 43 0\n-36 8 40 0\n-43 5 8 35 0\n-5 -8 -43 0\n-8 -35 -43 0\n-10 -35 -51 0\n-29 51 0\n-47 6 37 38 40 0\n-38 -48 -54 0\n-40 -46 -54 0\n-8 10 48 0\n-10 8 40 0\n-48 8 0\n-43 51 0\n-51 43 0\n-52 44 54 0\n-45 53 0\n-53 45 0\n-55 14 17 22 27 30 35 0\n-56 37 38 39 40 0\n-57 13 25 28 29 36 0\n-58 46 47 48 0\n-59 23 24 31 32 33 34 0\n-60 11 12 15 16 18 19 20 21 0\n-61 26 0\n-62 55 0\n-62 56 0\n-63 62 0\n-64 57 0\n-64 58 0\n-65 60 61 0\n-66 61 0\n-67 59 66 0\n-67 65 0\n-68 66 0\n-69 64 68 0\n-70 64 0\n-69 67 0\n-70 68 0\n-71 63 70 0\n-71 69 0\n71 0\n-72 44 0\n-44 72 0\n-73 52 0\n-52 73 0\n-74 54 0\n-54 74 0\n-75 41 43 0\n-76 45 49 0\n-45 76 0\n-77 51 0\n-51 77 0\n-78 53 0\n-53 78 0\n-79 73 74 0\n-74 79 0\n-73 79 0\n-80 72 79 0\n-79 80 0\n-72 80 0\n-76 81 0\n-82 75 0\n-82 76 0\n-83 77 78 0\n-84 78 0\n-77 -78 84 0\n-85 82 83 0\n-81 -84 86 0\n-87 80 85 0\n-86 88 0\n-80 -85 88 0\n87 0\n-88 0\n3 8 10 13 25 28 29 40 41 45 48 49 53 0\n4 7 9 27 30 35 39 42 44 47 50 52 54 0\n5 8 10 17 35 36 40 43 48 51 0\n"
  "196 69 0 160 159 0\n197 67 0 196 156 0\n198 65 0 197 152 0\n199 -86 0 192 189 0\n200 -84 0 199 184 187 172 180 136 169 0\n201 -70 -53 0 155 157 148 153 150 143 16 17 22 56 60 108 140 97 0\n202 -26 -53 0 160 201 158 146 145 136 16 17 22 43 45 102 92 93 138 0\n203 -30 -53 0 197 202 143 150 151 81 78 25 27 29 31 141 0\n204 -14 -36 -53 0 198 37 36 202 143 149 77 2 4 7 9 11 142 0\n205 -22 -53 0 197 202 143 150 151 81 78 14 26 28 30 141 0\n206 -14 28 -53 0 196 202 143 150 153 154 147 80 79 3 204 139 0\n207 27 35 14 -53 80 0 160 205 203 201 158 146 144 178 176 164 175 166 179 162 137 5 44 58 111 113 116 114 194 0\n208 -27 28 -53 0 196 202 143 150 153 154 147 80 79 19 38 139 0\n209 28 -53 80 0 198 196 202 143 150 153 154 147 149 80 79 77 206 208 207 32 33 40 139 1 6 8 10 12 142 0\n210 -78 80 0 200 172 185 136 171 132 209 39 105 106 109 110 117 118 119 195 0\n211 -28 35 -51 45 0 196 160 133 71 70 69 68 67 66 65 20 21 22 23 101 143 122 150 153 157 154 158 148 146 140 144 55 88 90 85 137 0\n212 -22 -8 28 -51 45 0 69 64 13 15 24 99 0\n213 -30 -51 0 160 133 51 71 70 68 42 112 115 86 89 138 140 145 148 146 155 158 0\n214 -22 28 -51 53 0 72 71 69 68 64 135 13 15 24 212 107 193 0\n215 -70 -51 0 71 70 155 157 148 153 140 150 56 143 0\n216 -14 -51 0 160 215 158 146 145 133 51 68 41 87 138 0\n217 35 -51 53 0 160 216 215 158 146 145 144 213 133 51 68 66 135 211 214 137 18 121 94 95 138 0\n218 -51 53 0 135 64 68 69 71 72 133 217 35 123 124 98 101 100 193 0\n219 -35 -85 0 192 196 190 210 173 218 132 170 183 186 181 167 50 46 125 34 40 119 143 103 104 150 139 153 147 154 0\n220 64 -8 -41 0 196 160 50 49 48 154 155 153 158 150 146 143 145 93 138 0\n221 -8 -85 0 192 160 190 210 173 135 218 170 183 186 182 168 63 132 181 167 62 50 49 48 129 220 148 140 59 97 138 143 145 150 146 153 158 157 0\n222 -85 0 192 190 210 173 218 132 170 183 186 181 167 47 50 62 219 221 117 120 130 195 0\n223 80 0 222 191 188 0\n224 43 8 40 0 130 120 131 118 133 117 119 195 0\n225 -51 0 200 171 218 185 173 0\n226 -43 0 225 132 0\n227 -38 -58 48 -8 0 223 57 96 140 161 75 84 177 163 165 174 0\n228 -39 0 223 53 74 83 161 163 165 177 174 0\n229 -37 0 223 52 73 82 161 163 165 177 174 0\n230 -38 -8 0 223 196 43 96 143 161 150 177 153 154 148 227 76 127 163 165 174 0\n231 40 0 226 228 160 229 224 230 138 145 146 158 155 157 148 153 150 143 56 60 91 140 126 0\n232 -26 0 231 45 0\n233 -44 0 231 54 0\n234 -48 0 231 61 0\n235 -61 0 232 143 0\n236 -72 0 233 161 0\n237 -66 0 235 150 0\n238 79 0 236 223 177 0\n239 -68 0 237 153 0\n240 64 0 239 196 154 0\n241 58 0 240 148 0\n242 54 0 233 238 165 134 174 163 0\n243 -47 0 242 84 0\n244 -46 0 242 231 128 0\n245 0 243 244 241 234 140 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "aab1ac9956c38ce8b86e4789e0faa9c67255570d3362d1b51d2743dc8ea3c4d53c2e8b92ccb1ae1b46c9b0ef0761d4731e2749c6725c3783d0f2b05c8a8aa168a6458562384e0b81e8a4a9164a5454552344d0b41dc0e2328d1314e0b22c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4da6924926d3492492492492492492492489249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 46), (facetIndex 58), (facetIndex 69), (facetIndex 80)]))
 (.leaf ([(facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 60), (facetIndex 72), (facetIndex 83)])))
 (.branch 3
 (.leaf ([(facetIndex 43), (facetIndex 48), (facetIndex 59), (facetIndex 61)]))
 (.leaf ([(facetIndex 39), (facetIndex 62), (facetIndex 63), (facetIndex 65), (facetIndex 66), (facetIndex 67)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 38), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 54), (facetIndex 55), (facetIndex 57)]))
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 76), (facetIndex 77), (facetIndex 78)])))
 (.branch 7
 (.leaf ([(facetIndex 42), (facetIndex 44), (facetIndex 45), (facetIndex 47)]))
 (.leaf ([(facetIndex 64), (facetIndex 75)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "20016df690006df6d142190c90ac365807z1d;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 68), (facetIndex 70)]))
 (.leaf ([(facetIndex 71), (facetIndex 79)])))
 (.branch 3
 (.leaf ([(facetIndex 81)]))
 (.leaf ([(facetIndex 82)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "3840004z23;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7]
def grouped2_0010 : List Nat := [7]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0014 : List Nat := [1]
def grouped3_0015 : List Nat := [2]
def grouped3_0016 : List Nat := [2, 3]
def grouped3_0017 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record005" 47

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record005" "{\"ridges\":[[19,133],[22,37],[22,133],[29,134],[32,38],[37,164],[42,37],[42,38],[45,133],[48,770],[62,37],[63,133],[65,37],[67,133],[70,37],[70,804],[74,134],[78,134],[81,38],[81,804]],\"owners\":[[70,37,[2,17,22,40,42,62,65],[43,44,66]],[19,133,[4,22,41,45,47],[63,67]],[45,133,[19,22,63],[4,41,47,67]],[63,133,[4,22,45,47],[19,41,67]],[67,133,[4,22,41,47],[19,45,63]],[29,134,[4,32,41,45,47],[74,78]],[74,134,[4,32,45,47],[29,41,78]],[78,134,[4,32,41,47],[29,45,74]],[48,770,[82],[15,57,59,61,79,81]],[37,164,[22,32],[]],[70,804,[81],[]],[81,804,[70],[]]],\"edges\":[[21,[4,19,22,29,32,37,41,45,47,63,67,74,78]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-12,-2],[-12,-11],[-15,-1],[-15,-10],[-15,-12],[-18,-16],[-20,-4],[-21,-3],[-21,-20],[-23,-4],[-23,-21],[-25,-15],[-26,-9],[-26,-20],[-26,-21],[-26,-23],[-26,-24],[-26,-25],[-31,-9],[-31,-13],[-31,-14],[-31,-19],[-31,-24],[-32,-22],[-32,-29],[-27,1,3,5,10,12,20,23],[-5,-12,-27],[-5,-20,-27],[-5,-23,-27],[-7,-12,-31],[-4,2,5,11,15,16],[-15,4,5,21],[-21,2,5,15,16],[-25,2,5,11,16],[-5,-15,-21],[-6,2,7,11,15,16],[-28,2,7,15,16],[-30,2,7,11,16],[-17,32],[-8,5,7],[-27,31],[-31,27],[-33,13,17,18,19],[-34,9,20,21,23,24,25],[-35,12,14,15,16],[-36,22,29],[-37,33],[-37,34],[-38,37],[-39,35],[-39,36],[-40,39],[-41,38],[-41,40],[41],[-42,26,27],[-43,31],[-44,32],[-45,42],[-46,43,44],[-47,45,46],[47],[2,4,5,6,7,8,11,15,16,21,25,28,30]],\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":42,\"b\":4},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":45,\"b\":2},{\"tag\":\"incompatible\",\"a\":45,\"b\":40},{\"tag\":\"incompatible\",\"a\":45,\"b\":42},{\"tag\":\"incompatible\",\"a\":59,\"b\":47},{\"tag\":\"incompatible\",\"a\":62,\"b\":19},{\"tag\":\"incompatible\",\"a\":63,\"b\":17},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":19},{\"tag\":\"incompatible\",\"a\":65,\"b\":63},{\"tag\":\"incompatible\",\"a\":67,\"b\":45},{\"tag\":\"incompatible\",\"a\":68,\"b\":39},{\"tag\":\"incompatible\",\"a\":68,\"b\":62},{\"tag\":\"incompatible\",\"a\":68,\"b\":63},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":81,\"b\":39},{\"tag\":\"incompatible\",\"a\":81,\"b\":43},{\"tag\":\"incompatible\",\"a\":81,\"b\":44},{\"tag\":\"incompatible\",\"a\":81,\"b\":61},{\"tag\":\"incompatible\",\"a\":81,\"b\":66},{\"tag\":\"incompatible\",\"a\":82,\"b\":64},{\"tag\":\"incompatible\",\"a\":82,\"b\":75},{\"tag\":\"mate\",\"ridge\":37,\"a\":70,\"owners\":[2,17,22,40,42,62,65]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[22,42,70]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[22,62,70]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[22,65,70]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[32,42,81]},{\"tag\":\"mate\",\"ridge\":133,\"a\":19,\"owners\":[4,22,41,45,47]},{\"tag\":\"mate\",\"ridge\":133,\"a\":45,\"owners\":[19,22,63]},{\"tag\":\"mate\",\"ridge\":133,\"a\":63,\"owners\":[4,22,45,47]},{\"tag\":\"mate\",\"ridge\":133,\"a\":67,\"owners\":[4,22,41,47]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[22,45,63]},{\"tag\":\"mate\",\"ridge\":134,\"a\":29,\"owners\":[4,32,41,45,47]},{\"tag\":\"mate\",\"ridge\":134,\"a\":74,\"owners\":[4,32,45,47]},{\"tag\":\"mate\",\"ridge\":134,\"a\":78,\"owners\":[4,32,41,47]},{\"tag\":\"mate\",\"ridge\":770,\"a\":48,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":164,\"a\":37,\"owners\":[22,32]},{\"tag\":\"mate\",\"ridge\":804,\"a\":70,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":804,\"a\":81,\"owners\":[70]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[43,48,59,61],\"full_literals\":[-33,13,17,18,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[39,62,63,65,66,67],\"full_literals\":[-34,9,20,21,23,24,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[42,44,45,47],\"full_literals\":[-35,12,14,15,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[64,75],\"full_literals\":[-36,22,29]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-37,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,35,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-39,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-41,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-41,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[68,70],\"full_literals\":[-42,26,27]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[81],\"full_literals\":[-43,31]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[82],\"full_literals\":[-44,32]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,42,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,43,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":21,\"owners\":[4,19,22,29,32,37,41,45,47,63,67,74,78]}]}"
  "p cnf 47 63\n-12 -2 0\n-12 -11 0\n-15 -1 0\n-15 -10 0\n-15 -12 0\n-18 -16 0\n-20 -4 0\n-21 -3 0\n-21 -20 0\n-23 -4 0\n-23 -21 0\n-25 -15 0\n-26 -9 0\n-26 -20 0\n-26 -21 0\n-26 -23 0\n-26 -24 0\n-26 -25 0\n-31 -9 0\n-31 -13 0\n-31 -14 0\n-31 -19 0\n-31 -24 0\n-32 -22 0\n-32 -29 0\n-27 1 3 5 10 12 20 23 0\n-5 -12 -27 0\n-5 -20 -27 0\n-5 -23 -27 0\n-7 -12 -31 0\n-4 2 5 11 15 16 0\n-15 4 5 21 0\n-21 2 5 15 16 0\n-25 2 5 11 16 0\n-5 -15 -21 0\n-6 2 7 11 15 16 0\n-28 2 7 15 16 0\n-30 2 7 11 16 0\n-17 32 0\n-8 5 7 0\n-27 31 0\n-31 27 0\n-33 13 17 18 19 0\n-34 9 20 21 23 24 25 0\n-35 12 14 15 16 0\n-36 22 29 0\n-37 33 0\n-37 34 0\n-38 37 0\n-39 35 0\n-39 36 0\n-40 39 0\n-41 38 0\n-41 40 0\n41 0\n-42 26 27 0\n-43 31 0\n-44 32 0\n-45 42 0\n-46 43 44 0\n-47 45 46 0\n47 0\n2 4 5 6 7 8 11 15 16 21 25 28 30 0\n"
  "64 38 0 55 53 0\n65 40 0 55 54 0\n66 37 0 64 49 0\n67 39 0 65 52 0\n68 33 0 66 47 0\n69 34 0 66 48 0\n70 35 0 67 50 0\n71 36 0 67 51 0\n72 -32 0 71 24 25 46 0\n73 -17 0 72 39 0\n74 -44 0 72 58 0\n75 -5 -31 0 68 73 70 69 20 22 43 6 42 23 21 19 27 28 29 45 12 35 44 0\n76 15 -31 0 68 73 70 75 20 22 43 6 21 45 1 2 30 33 34 31 36 37 38 40 63 0\n77 21 -31 0 69 76 12 75 23 19 32 7 10 44 0\n78 -31 0 42 75 76 3 4 5 77 8 9 11 26 0\n79 -27 0 78 41 0\n80 -43 0 78 57 0\n81 -46 0 80 74 60 0\n82 45 0 81 62 61 0\n83 42 0 82 59 0\n84 26 0 83 79 56 0\n85 -9 0 84 13 0\n86 -20 0 84 14 0\n87 -21 0 84 15 0\n88 -23 0 84 16 0\n89 -24 0 84 17 0\n90 -25 0 84 18 0\n91 0 86 88 69 90 87 85 89 44 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record005
