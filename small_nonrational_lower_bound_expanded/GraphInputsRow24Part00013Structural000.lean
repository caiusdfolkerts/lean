module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00013Data
public import GraphInputsRow24Part00013Frames
public import GraphInputsRow24Part00013Leaves
public import GraphInputsRow24Part00013Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record070
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record070
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨91, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 8651417083201978368, (certNat% 4), 138194867716096, 283023089082564608]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record070_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record070_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record070_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record070_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record070_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record070_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record070_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record070_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record070_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record070

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "dc1f38a3a8da1eac6c9a9635876c3a8e3392e1b89e1783ee24e936479b1725a54d51d70da34cd4b46d2745d0f783b0f2358ce3a4c73c2e8b62ccb2ac6b46c5b0ef07a1e4731e2749e1725c3783d0f23c4f3492a268661582e078d14a499194550b41dc0e8330d2318c9314d0b22c2b06e0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db69b6d26da4926d36da4db492492492492492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 37), (facetIndex 42), (facetIndex 63), (facetIndex 80)]))
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 54), (facetIndex 55)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 34), (facetIndex 43), (facetIndex 52), (facetIndex 59), (facetIndex 67), (facetIndex 76), (facetIndex 84)]))
 (.leaf ([(facetIndex 31), (facetIndex 35), (facetIndex 39), (facetIndex 41), (facetIndex 61), (facetIndex 68), (facetIndex 78), (facetIndex 85)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 53), (facetIndex 57), (facetIndex 58)]))
 (.leaf ([(facetIndex 44), (facetIndex 60), (facetIndex 62), (facetIndex 73), (facetIndex 77), (facetIndex 79), (facetIndex 90)])))
 (.branch 7
 (.leaf ([(facetIndex 45), (facetIndex 51), (facetIndex 56)]))
 (.leaf ([(facetIndex 33), (facetIndex 36), (facetIndex 38), (facetIndex 40)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "14001a000aea02800340015d526262d2427541f7c76b868z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 66), (facetIndex 70)]))
 (.leaf ([(facetIndex 83), (facetIndex 87)])))
 (.branch 3
 (.leaf ([(facetIndex 65), (facetIndex 75)]))
 (.leaf ([(facetIndex 82), (facetIndex 92)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 64), (facetIndex 72), (facetIndex 74)]))
 (.leaf ([(facetIndex 81), (facetIndex 89), (facetIndex 91)])))
 (.branch 7
 (.leaf ([(facetIndex 93), (facetIndex 94)]))
 (.branch 8
 (.leaf ([(facetIndex 69), (facetIndex 71)]))
 (.leaf ([(facetIndex 86), (facetIndex 88)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "6635058180013500000240470700024z40;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
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
def grouped3_0015 : List Nat := [0, 1, 2, 3]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [2, 3]
def grouped3_0020 : List Nat := [3]
def grouped3_0021 : List Nat := [4]
def grouped3_0022 : List Nat := [4, 5]
def grouped3_0023 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0024 : List Nat := [5]
def grouped3_0025 : List Nat := [6]
def grouped3_0026 : List Nat := [6, 7, 8]
def grouped3_0027 : List Nat := [7]
def grouped3_0028 : List Nat := [7, 8]
def grouped3_0029 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record000" 82

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record000" "{\"ridges\":[[14,642],[15,770],[23,22],[24,38],[25,22],[33,518],[36,22],[36,517],[38,38],[38,517],[40,518],[41,518],[41,642],[42,770],[50,642],[51,770],[53,642],[56,770],[57,642],[58,642],[58,770],[61,28],[63,44],[65,652],[68,84],[69,660],[71,708],[75,904],[78,22],[80,38],[82,652],[84,22],[84,38],[86,660],[88,708],[92,904],[93,120],[94,204]],\"owners\":[[78,22,[1,25,34,36,84],[23,35,76,85,86]],[36,517,[65,66,70,71],[4,33,38,40,41,42,69]],[38,517,[65,66,69,71],[4,33,36,40,41,42,70]],[33,518,[86,87,88],[4,36,38,40,41,42,82,83]],[40,518,[82,83,86,87],[4,33,36,38,41,42,88]],[41,518,[83,87],[4,33,36,38,40,42,82,86,88]],[14,642,[82,86,88,92],[41,50,53,57,58]],[41,642,[92],[14,50,53,57,58,82,86,88]],[50,642,[86,88],[14,41,53,57,58,82,92]],[53,642,[82,88,92],[14,41,50,57,58,86]],[57,642,[82,86,92],[14,41,50,53,58,88]],[58,642,[82,86,88],[14,41,50,53,57,92]],[15,770,[83,87,92],[42,51,56,58]],[42,770,[92],[15,51,56,58,83,87]],[51,770,[87],[15,42,56,58,83,92]],[56,770,[83,92],[15,42,51,58,87]],[58,770,[83,87],[15,42,51,56,92]],[61,28,[23,76,77,93],[16,59,60,78,94]],[63,44,[24,76,79,93],[17,59,62,80]],[68,84,[25,77,84,93],[18,60,67,85,94]],[94,204,[64,81],[]],[65,652,[82],[]],[82,652,[65],[]],[69,660,[86],[]],[86,660,[69],[]],[71,708,[88],[]],[88,708,[71],[]],[93,120,[72,89],[]],[75,904,[92],[]],[92,904,[75],[]]],\"edges\":[[43,[14,41,50,53,57,58,65,69,71,75,82,86,88,92]],[44,[15,42,51,56,58,66,70,75,83,87,92]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-12,-7],[-12,-11],[-14,-1],[-14,-7],[-14,-8],[-14,-10],[-14,-11],[-14,-13],[-15,-12],[-15,-14],[-16,-1],[-16,-7],[-16,-10],[-16,-11],[-16,-15],[-18,-14],[-28,-25],[-30,-28],[-37,-12],[-38,-28],[-42,-25],[-42,-30],[-42,-38],[-44,-15],[-44,-16],[-44,-36],[-44,-37],[-44,-39],[-45,-6],[-45,-28],[-45,-42],[-45,-44],[-38,1,6,10,12,44],[-4,-12,-44],[-6,-12,-38],[-12,-38,-44],[-5,-14,-44],[-14,-40,-44],[-12,28,29,32,33],[-14,28,29,31,33],[-9,46,47,48],[-16,42,43,46,47],[-17,43,47],[-2,42,46,48,50],[-17,50],[-19,46,48],[-21,42,48,50],[-23,42,46,50],[-24,42,46,48],[-3,43,47,50],[-18,50],[-20,47],[-22,43,50],[-24,43,47],[-25,4,36,37,51],[-26,5,36,39,51],[-30,6,37,44,51],[-52,27,41],[-28,42],[-42,28],[-31,46],[-46,31],[-33,48],[-48,33],[-51,34,49],[-35,50],[-50,35],[-53,8,13,18,26,40],[-54,7,11,15,17,25,30,38,45],[-55,9,12,14,16],[-56,53],[-57,54],[-58,56],[-58,57],[-59,55],[-60,59],[-61,58],[-61,60],[61],[-29,62],[-32,62],[-43,63],[-47,63],[-64,28,35],[-28,64],[-35,64],[-65,42,50],[-42,65],[-50,65],[-27,66],[-34,66],[-41,67],[-49,67],[-68,51,52],[-51,68],[-69,31,33],[-31,69],[-33,69],[-70,46,48],[-46,70],[-48,70],[-63,71],[-62,71],[-72,64,65],[-65,72],[-64,72],[-64,-65,73],[-72,74],[-71,74],[-71,-73,75],[-67,76],[-66,76],[-77,69,70],[-69,-70,78],[-79,68,77],[-78,80],[-68,79],[-80,81],[-76,-79,81],[-74,-81,82],[-75,82],[-82],[2,17,19,21,23,24,28,31,33,35,42,46,48,50],[3,18,20,22,24,29,32,35,43,47,50]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":36,\"b\":31},{\"tag\":\"incompatible\",\"a\":36,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":1},{\"tag\":\"incompatible\",\"a\":38,\"b\":31},{\"tag\":\"incompatible\",\"a\":38,\"b\":32},{\"tag\":\"incompatible\",\"a\":38,\"b\":34},{\"tag\":\"incompatible\",\"a\":38,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":36},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":1},{\"tag\":\"incompatible\",\"a\":40,\"b\":31},{\"tag\":\"incompatible\",\"a\":40,\"b\":34},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":38},{\"tag\":\"incompatible\",\"a\":65,\"b\":61},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":77,\"b\":36},{\"tag\":\"incompatible\",\"a\":78,\"b\":65},{\"tag\":\"incompatible\",\"a\":82,\"b\":61},{\"tag\":\"incompatible\",\"a\":82,\"b\":68},{\"tag\":\"incompatible\",\"a\":82,\"b\":78},{\"tag\":\"incompatible\",\"a\":84,\"b\":39},{\"tag\":\"incompatible\",\"a\":84,\"b\":40},{\"tag\":\"incompatible\",\"a\":84,\"b\":76},{\"tag\":\"incompatible\",\"a\":84,\"b\":77},{\"tag\":\"incompatible\",\"a\":84,\"b\":79},{\"tag\":\"incompatible\",\"a\":85,\"b\":25},{\"tag\":\"incompatible\",\"a\":85,\"b\":65},{\"tag\":\"incompatible\",\"a\":85,\"b\":82},{\"tag\":\"incompatible\",\"a\":85,\"b\":84},{\"tag\":\"mate\",\"ridge\":22,\"a\":78,\"owners\":[1,25,34,36,84]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[23,36,84]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[25,36,78]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[36,78,84]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[24,38,84]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[38,80,84]},{\"tag\":\"mate\",\"ridge\":517,\"a\":36,\"owners\":[65,66,70,71]},{\"tag\":\"mate\",\"ridge\":517,\"a\":38,\"owners\":[65,66,69,71]},{\"tag\":\"mate\",\"ridge\":518,\"a\":33,\"owners\":[86,87,88]},{\"tag\":\"mate\",\"ridge\":518,\"a\":40,\"owners\":[82,83,86,87]},{\"tag\":\"mate\",\"ridge\":518,\"a\":41,\"owners\":[83,87]},{\"tag\":\"mate\",\"ridge\":642,\"a\":14,\"owners\":[82,86,88,92]},{\"tag\":\"mate\",\"ridge\":642,\"a\":41,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":642,\"a\":50,\"owners\":[86,88]},{\"tag\":\"mate\",\"ridge\":642,\"a\":53,\"owners\":[82,88,92]},{\"tag\":\"mate\",\"ridge\":642,\"a\":57,\"owners\":[82,86,92]},{\"tag\":\"mate\",\"ridge\":642,\"a\":58,\"owners\":[82,86,88]},{\"tag\":\"mate\",\"ridge\":770,\"a\":15,\"owners\":[83,87,92]},{\"tag\":\"mate\",\"ridge\":770,\"a\":42,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":770,\"a\":51,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":770,\"a\":56,\"owners\":[83,92]},{\"tag\":\"mate\",\"ridge\":770,\"a\":58,\"owners\":[83,87]},{\"tag\":\"mate\",\"ridge\":28,\"a\":61,\"owners\":[23,76,77,93]},{\"tag\":\"mate\",\"ridge\":44,\"a\":63,\"owners\":[24,76,79,93]},{\"tag\":\"mate\",\"ridge\":84,\"a\":68,\"owners\":[25,77,84,93]},{\"tag\":\"mate\",\"ridge\":204,\"a\":94,\"owners\":[64,81]},{\"tag\":\"mate\",\"ridge\":652,\"a\":65,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":652,\"a\":82,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":660,\"a\":69,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":660,\"a\":86,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":708,\"a\":71,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":708,\"a\":88,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":120,\"a\":93,\"owners\":[72,89]},{\"tag\":\"mate\",\"ridge\":904,\"a\":75,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":904,\"a\":92,\"owners\":[75]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[32,37,42,63,80],\"full_literals\":[-53,8,13,18,26,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[31,35,39,41,61,68,78,85],\"full_literals\":[-54,7,11,15,17,25,30,38,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[33,36,38,40],\"full_literals\":[-55,9,12,14,16]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-58,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-61,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-61,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-29,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-32,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-43,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-47,63]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[65,75],\"full_literals\":[-64,28,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-28,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-35,64]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[82,92],\"full_literals\":[-65,42,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-42,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":92,\"full_literals\":[-50,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":64,\"full_literals\":[-27,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":72,\"full_literals\":[-34,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-41,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":89,\"full_literals\":[-49,67]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[93,94],\"full_literals\":[-68,51,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":93,\"full_literals\":[-51,68]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[69,71],\"full_literals\":[-69,31,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":69,\"full_literals\":[-31,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":71,\"full_literals\":[-33,69]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[86,88],\"full_literals\":[-70,46,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":86,\"full_literals\":[-46,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":88,\"full_literals\":[-48,70]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-65,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-71,-73,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-69,-70,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,68,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-78,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-80,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-74,-81,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,82],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":43,\"owners\":[14,41,50,53,57,58,65,69,71,75,82,86,88,92]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[15,42,51,56,58,66,70,75,83,87,92]}]}"
  "125 58 0 79 77 0\n126 60 0 79 78 0\n127 56 0 125 73 0\n128 57 0 125 74 0\n129 59 0 126 76 0\n130 53 0 127 71 0\n131 54 0 128 72 0\n132 55 0 129 75 0\n133 -75 0 122 121 0\n134 74 0 108 109 105 106 102 103 89 86 82 83 80 81 51 53 50 54 52 124 0\n135 -81 0 134 122 120 0\n136 -80 0 135 118 0\n137 -78 0 136 116 0\n138 -70 0 137 114 97 98 62 64 99 0\n139 -46 0 138 100 0\n140 -48 0 138 101 0\n141 -31 0 139 61 0\n142 -19 0 139 140 46 0\n143 -33 0 140 63 0\n144 -69 0 141 143 96 0\n145 -77 0 144 138 113 0\n146 -79 0 135 145 119 115 111 112 92 93 90 91 65 58 94 0\n147 -68 0 146 117 0\n148 -51 0 147 95 0\n149 72 0 140 139 143 141 142 105 106 88 89 85 86 44 48 49 47 45 123 0\n150 65 0 149 88 89 104 59 66 84 0\n151 64 0 150 85 86 60 67 87 0\n152 73 0 151 150 107 0\n153 -71 0 152 133 110 0\n154 -63 0 153 102 0\n155 -62 0 153 103 0\n156 -43 0 154 82 0\n157 -47 0 154 83 0\n158 -29 0 155 80 0\n159 -32 0 155 81 0\n160 -17 0 156 157 43 0\n161 -9 0 157 139 140 41 0\n162 -12 44 6 0 158 159 143 148 160 131 1 2 9 19 39 57 17 20 30 69 0\n163 -16 44 6 0 139 157 156 160 131 162 11 12 13 14 15 42 33 21 22 31 69 0\n164 44 6 0 131 160 141 158 143 132 161 162 163 70 3 4 6 7 10 40 33 17 18 30 69 0\n165 -14 -44 0 148 130 28 26 5 8 16 37 38 56 68 0\n166 -44 0 161 132 158 159 143 148 160 131 24 25 26 27 32 165 70 1 2 34 36 39 55 18 69 0\n167 6 0 166 164 0\n168 -45 0 167 29 0\n169 -12 0 167 158 159 143 168 160 131 1 2 9 35 39 17 18 69 0\n170 -16 0 139 157 156 168 160 131 12 14 15 42 21 22 23 69 0\n171 14 0 170 132 161 169 70 0\n172 -7 0 171 4 0\n173 -11 0 171 7 0\n174 -15 0 171 10 0\n175 28 0 171 141 158 143 40 0\n176 -25 0 175 17 0\n177 -30 0 175 18 0\n178 -38 0 175 20 0\n179 0 177 176 131 172 173 174 160 178 168 69 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3d07c3caaaa68ba1e8e6358b61db0e4b86e4785e0f8f1aa6992e479394d52d475c352d1b51d1743de0ec3a8e932cc73a2e2b4acab1ae1b46c9b16c3bc1d4731d2729d1725c3783c4f388d2c28661590e0b81e384d1c24651550d0b41dc0e8330ca318c9314e0b42c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b4db6934924926db49a492492492492492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 58), (facetIndex 60), (facetIndex 62), (facetIndex 63)]))
 (.leaf ([(facetIndex 51), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57)])))
 (.branch 3
 (.leaf ([(facetIndex 73), (facetIndex 75), (facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 35), (facetIndex 37), (facetIndex 39), (facetIndex 52), (facetIndex 66), (facetIndex 67), (facetIndex 81), (facetIndex 82)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 32), (facetIndex 34), (facetIndex 36), (facetIndex 38), (facetIndex 40), (facetIndex 41)]))
 (.leaf ([(facetIndex 42), (facetIndex 64), (facetIndex 72), (facetIndex 79), (facetIndex 87)])))
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 47), (facetIndex 59), (facetIndex 61), (facetIndex 74), (facetIndex 76)]))
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 48), (facetIndex 49), (facetIndex 50)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "a000d8a965950006c5030c0924b3ffdffd6471c704z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 71)]))
 (.leaf ([(facetIndex 84), (facetIndex 85), (facetIndex 86)])))
 (.branch 3
 (.leaf ([(facetIndex 65), (facetIndex 68)]))
 (.branch 4
 (.leaf ([(facetIndex 80), (facetIndex 83)]))
 (.leaf ([(facetIndex 88), (facetIndex 89)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2404960300000000201z31;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record007" 76

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record007" "{\"ridges\":[[4,259],[14,642],[15,515],[26,262],[29,770],[36,259],[38,259],[40,259],[41,515],[46,515],[50,515],[51,641],[54,515],[54,642],[55,515],[55,642],[56,515],[56,642],[57,641],[57,642],[58,28],[58,44],[60,28],[62,44],[63,769],[65,180],[68,120],[75,262],[77,262],[78,770],[80,180],[83,120],[88,120],[89,180]],\"owners\":[[4,259,[7,15,45,49,57],[36,38,40]],[36,259,[7,15,49,57],[4,38,40,45]],[38,259,[7,15,45,57],[4,36,40,49]],[40,259,[7,15,45,49,57],[4,36,38]],[26,262,[4,36,38,40,41],[75,77,78]],[75,262,[4,38,40,41],[26,36,77,78]],[77,262,[4,36,40,41],[26,38,75,78]],[51,641,[],[14,54,55,56,57,70,71]],[57,641,[70,71],[14,51,54,55,56]],[14,642,[85,86],[51,54,55,56,57]],[54,642,[86],[14,51,55,56,57,85]],[55,642,[85],[14,51,54,56,57,86]],[56,642,[85,86],[14,51,54,55,57]],[57,642,[85,86],[14,51,54,55,56]],[63,769,[15,57],[21,41]],[29,770,[15,41,57],[78]],[78,770,[15,57],[29,41]],[58,28,[24,74,75],[16,59,60,73,88]],[60,28,[24,73,74,88],[16,58,59,75]],[58,44,[25,76,77],[17,61,62,73,88]],[62,44,[25,73,76,88],[17,58,61,77]],[65,180,[80,89],[]],[80,180,[65,89],[]],[89,180,[65,80],[]],[68,120,[83,88],[]],[83,120,[68,88],[]],[88,120,[68,83],[]]],\"edges\":[[15,[4,7,15,26,29,36,38,40,41,45,49,57,75,77,78]],[43,[14,51,54,55,56,57,70,71,85,86]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-17,-2],[-20,-2],[-22,-14],[-22,-15],[-23,-15],[-23,-17],[-24,-15],[-24,-20],[-25,-15],[-26,-17],[-26,-20],[-30,-16],[-30,-19],[-31,-22],[-34,-18],[-35,-15],[-35,-18],[-36,-15],[-36,-18],[-37,-22],[-38,-14],[-38,-31],[-38,-37],[-40,-6],[-40,-9],[-40,-16],[-40,-28],[-41,-40],[-42,-5],[-42,-9],[-42,-19],[-42,-29],[-42,-39],[-42,-40],[-43,-16],[-43,-19],[-44,-22],[-44,-38],[-49,-22],[-49,-38],[-1,2,4,16,19,26],[-10,2,4,19,26],[-11,2,4,16,26],[-12,2,4,16,19,26],[-7,1,10,11,12,13],[-40,1,11,12,13],[-42,1,10,12,13],[-4,-17,-24],[-4,-17,-25],[-4,-20,-23],[-4,-20,-25],[-13,-17,-25],[-13,-20,-25],[-21],[-26,35,36],[-3,47,48],[-23,48],[-24,47],[-25,47,48],[-26,47,48],[-30,4,26],[-8,4,13,26],[-43,4,26],[-27,5,39,40],[-28,5,38,39,50],[-27,6,41,42],[-29,6,38,41,50],[-32,45,51],[-45,32,51],[-51,32,45],[-33,46,50],[-46,33,50],[-50,33,46],[-52,9,27,28,29,30],[-53,21,22,23,24,25,26],[-54,38,40,42,43],[-55,14,31,37,44,49],[-56,15,16,17,18,19,20],[-57,52],[-57,53],[-58,54],[-59,57],[-59,58],[-60,55],[-61,56],[-62,60],[-62,61],[-63,59],[-63,62],[63],[-64,34,35,36],[-35,64],[-36,64],[-47,65],[-48,65],[-66,32,33],[-32,66],[-33,66],[-67,45,46],[-45,67],[-46,67],[-68,50,51],[-50,68],[-51,68],[-65,69],[-70,64],[-64,69],[-71,67,68],[-68,71],[-67,71],[-67,-68,72],[-73,66,71],[-72,74],[-66,-71,74],[-75,70,73],[-69,-74,76],[75],[-76],[1,2,4,7,8,10,11,12,13,16,19,26,40,42,43],[3,21,23,24,25,26,35,36,47,48]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":46,\"b\":7},{\"tag\":\"incompatible\",\"a\":50,\"b\":7},{\"tag\":\"incompatible\",\"a\":53,\"b\":42},{\"tag\":\"incompatible\",\"a\":53,\"b\":44},{\"tag\":\"incompatible\",\"a\":54,\"b\":44},{\"tag\":\"incompatible\",\"a\":54,\"b\":46},{\"tag\":\"incompatible\",\"a\":55,\"b\":44},{\"tag\":\"incompatible\",\"a\":55,\"b\":50},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":57,\"b\":46},{\"tag\":\"incompatible\",\"a\":57,\"b\":50},{\"tag\":\"incompatible\",\"a\":63,\"b\":45},{\"tag\":\"incompatible\",\"a\":63,\"b\":49},{\"tag\":\"incompatible\",\"a\":64,\"b\":53},{\"tag\":\"incompatible\",\"a\":69,\"b\":48},{\"tag\":\"incompatible\",\"a\":70,\"b\":44},{\"tag\":\"incompatible\",\"a\":70,\"b\":48},{\"tag\":\"incompatible\",\"a\":71,\"b\":44},{\"tag\":\"incompatible\",\"a\":71,\"b\":48},{\"tag\":\"incompatible\",\"a\":72,\"b\":53},{\"tag\":\"incompatible\",\"a\":73,\"b\":42},{\"tag\":\"incompatible\",\"a\":73,\"b\":64},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":75,\"b\":25},{\"tag\":\"incompatible\",\"a\":75,\"b\":33},{\"tag\":\"incompatible\",\"a\":75,\"b\":45},{\"tag\":\"incompatible\",\"a\":75,\"b\":60},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":24},{\"tag\":\"incompatible\",\"a\":77,\"b\":33},{\"tag\":\"incompatible\",\"a\":77,\"b\":49},{\"tag\":\"incompatible\",\"a\":77,\"b\":62},{\"tag\":\"incompatible\",\"a\":77,\"b\":74},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":45},{\"tag\":\"incompatible\",\"a\":78,\"b\":49},{\"tag\":\"incompatible\",\"a\":79,\"b\":53},{\"tag\":\"incompatible\",\"a\":79,\"b\":73},{\"tag\":\"incompatible\",\"a\":87,\"b\":53},{\"tag\":\"incompatible\",\"a\":87,\"b\":73},{\"tag\":\"mate\",\"ridge\":259,\"a\":4,\"owners\":[7,15,45,49,57]},{\"tag\":\"mate\",\"ridge\":259,\"a\":36,\"owners\":[7,15,49,57]},{\"tag\":\"mate\",\"ridge\":259,\"a\":38,\"owners\":[7,15,45,57]},{\"tag\":\"mate\",\"ridge\":259,\"a\":40,\"owners\":[7,15,45,49,57]},{\"tag\":\"mate\",\"ridge\":262,\"a\":26,\"owners\":[4,36,38,40,41]},{\"tag\":\"mate\",\"ridge\":262,\"a\":75,\"owners\":[4,38,40,41]},{\"tag\":\"mate\",\"ridge\":262,\"a\":77,\"owners\":[4,36,40,41]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[15,46,55]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[15,46,56]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[15,50,54]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[15,50,56]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[41,46,56]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[41,50,56]},{\"tag\":\"mate\",\"ridge\":641,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":641,\"a\":57,\"owners\":[70,71]},{\"tag\":\"mate\",\"ridge\":642,\"a\":14,\"owners\":[85,86]},{\"tag\":\"mate\",\"ridge\":642,\"a\":54,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":642,\"a\":55,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":642,\"a\":56,\"owners\":[85,86]},{\"tag\":\"mate\",\"ridge\":642,\"a\":57,\"owners\":[85,86]},{\"tag\":\"mate\",\"ridge\":769,\"a\":63,\"owners\":[15,57]},{\"tag\":\"mate\",\"ridge\":770,\"a\":29,\"owners\":[15,41,57]},{\"tag\":\"mate\",\"ridge\":770,\"a\":78,\"owners\":[15,57]},{\"tag\":\"mate\",\"ridge\":28,\"a\":58,\"owners\":[24,74,75]},{\"tag\":\"mate\",\"ridge\":28,\"a\":60,\"owners\":[24,73,74,88]},{\"tag\":\"mate\",\"ridge\":44,\"a\":58,\"owners\":[25,76,77]},{\"tag\":\"mate\",\"ridge\":44,\"a\":62,\"owners\":[25,73,76,88]},{\"tag\":\"mate\",\"ridge\":180,\"a\":65,\"owners\":[80,89]},{\"tag\":\"mate\",\"ridge\":180,\"a\":80,\"owners\":[65,89]},{\"tag\":\"mate\",\"ridge\":180,\"a\":89,\"owners\":[65,80]},{\"tag\":\"mate\",\"ridge\":120,\"a\":68,\"owners\":[83,88]},{\"tag\":\"mate\",\"ridge\":120,\"a\":83,\"owners\":[68,88]},{\"tag\":\"mate\",\"ridge\":120,\"a\":88,\"owners\":[68,83]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[33,58,60,62,63],\"full_literals\":[-52,9,27,28,29,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[51,53,54,55,56,57],\"full_literals\":[-53,21,22,23,24,25,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[73,75,77,78],\"full_literals\":[-54,38,40,42,43]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[42,64,72,79,87],\"full_literals\":[-55,14,31,37,44,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[44,45,46,48,49,50],\"full_literals\":[-56,15,16,17,18,19,20]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-62,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-63,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-63,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[69,70,71],\"full_literals\":[-64,34,35,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-35,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":71,\"full_literals\":[-36,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-47,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":86,\"full_literals\":[-48,65]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[65,68],\"full_literals\":[-66,32,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-32,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":68,\"full_literals\":[-33,66]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[80,83],\"full_literals\":[-67,45,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":80,\"full_literals\":[-45,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-46,67]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[88,89],\"full_literals\":[-68,50,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":88,\"full_literals\":[-50,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":89,\"full_literals\":[-51,68]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-70,64,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-71,67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-67,-68,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,66,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-71,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-75,70,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-69,-74,76],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":15,\"owners\":[4,7,15,26,29,36,38,40,41,45,49,57,75,77,78]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[14,51,54,55,56,57,70,71,85,86]}]}"
  "121 -53 22 23 24 25 26 0 54 75 0\n122 59 0 90 88 0\n123 62 0 90 89 0\n124 57 0 122 82 0\n125 58 0 122 83 0\n126 60 0 123 86 0\n127 61 0 123 87 0\n128 52 0 124 79 0\n129 53 0 124 80 0\n130 54 0 125 81 0\n131 55 0 126 84 0\n132 56 0 127 85 0\n133 3 23 24 25 26 35 36 47 48 0 54 120 0\n134 69 0 105 107 94 95 92 93 56 58 59 57 60 133 0\n135 -74 0 134 118 116 0\n136 -72 0 135 113 0\n137 -68 66 0 136 98 97 111 100 101 70 73 102 0\n138 -71 0 135 114 97 98 137 103 104 108 72 69 99 0\n139 -68 0 138 109 0\n140 -67 0 138 110 0\n141 -50 0 139 103 0\n142 -51 0 139 104 0\n143 -45 0 140 100 0\n144 -46 0 140 101 0\n145 -32 0 143 142 68 0\n146 -33 0 144 141 71 0\n147 -66 0 146 145 96 0\n148 -73 0 147 138 112 0\n149 70 0 148 117 115 0\n150 64 0 149 106 0\n151 -38 44 0 131 21 22 23 40 77 0\n152 -38 0 38 151 0\n153 -18 0 150 15 17 19 91 0\n154 -26 19 16 0 153 132 10 11 78 16 18 55 0\n155 -15 26 0 129 4 5 7 9 121 0\n156 -22 0 131 3 14 20 37 39 77 0\n157 -24 -4 19 16 0 153 132 154 155 8 48 78 0\n158 -23 -4 19 16 0 153 132 154 155 6 50 78 0\n159 -40 42 0 141 152 128 156 129 153 132 24 25 26 27 28 67 66 74 13 154 61 155 157 158 121 49 51 78 0\n160 -43 0 156 129 153 132 35 36 154 63 155 157 158 121 49 51 78 0\n161 -4 -25 19 16 15 0 153 132 49 51 78 0\n162 12 42 1 2 4 7 8 11 13 16 19 26 10 0 160 119 46 0\n163 -20 -25 19 16 26 0 155 161 2 53 41 42 44 43 62 45 47 162 0\n164 -25 19 16 26 0 153 132 155 161 163 78 1 52 41 42 44 43 62 45 47 162 0\n165 42 0 160 152 130 159 76 0\n166 -5 0 165 29 0\n167 -9 0 165 30 0\n168 -19 0 165 31 0\n169 -29 0 165 32 0\n170 -39 0 165 33 0\n171 -40 0 165 34 0\n172 -28 0 166 152 170 141 65 0\n173 -27 0 170 166 171 64 0\n174 30 0 173 128 169 172 167 74 0\n175 -16 0 174 12 0\n176 26 0 174 175 168 156 129 61 164 157 158 121 0\n177 0 176 168 175 154 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record078
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "7cca87ae19361db0ea38ce4b8ae1b89eca479e15351d70da34cd4b4ad1b49de0f234cc73c2e4b32e2b4acab1ae1b26f07a1d8751cc729c6745c9783d0f1703ca285a0e926158362384e0b81ea24590e525154352344d0b41dc0e8348c530ce0b22c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9a69349249a693492492492492492492492489249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 48), (facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 59), (facetIndex 70), (facetIndex 82)])))
 (.branch 3
 (.leaf ([(facetIndex 39), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 38), (facetIndex 40), (facetIndex 44), (facetIndex 45), (facetIndex 47)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 76), (facetIndex 78), (facetIndex 79)]))
 (.leaf ([(facetIndex 51), (facetIndex 58), (facetIndex 69), (facetIndex 72), (facetIndex 81), (facetIndex 84), (facetIndex 86)])))
 (.branch 7
 (.leaf ([(facetIndex 53), (facetIndex 57), (facetIndex 65), (facetIndex 77)]))
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 52), (facetIndex 54), (facetIndex 55), (facetIndex 56)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1450689349050684b2480377ff7bf861b24b4cz1c;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 68), (facetIndex 71)]))
 (.leaf ([(facetIndex 73), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 83)]))
 (.leaf ([(facetIndex 85)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "c810004z24;"⟩
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
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [2]
def grouped3_0020 : List Nat := [2, 3]
def grouped3_0021 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record078" "{\"atoms\":[{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record078" 46

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record078" "{\"ridges\":[[40,133],[40,134],[44,133],[44,134],[48,770],[62,133],[64,133],[66,133],[71,133],[71,900],[74,134],[76,134],[78,134],[83,134],[83,900]],\"owners\":[[48,770,[85],[15,57,60,61,80,83]],[71,900,[83],[]],[83,900,[71],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record078" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record078\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-11,-1],[-11,-5],[-13,-3],[-17,-4],[-19,-2],[-19,-13],[-19,-14],[-19,-15],[-19,-17],[-19,-18],[-21,-3],[-22,-14],[-25,-4],[-27,-2],[-27,-6],[-27,-7],[-27,-12],[-27,-18],[-27,-26],[-28,-9],[-28,-10],[-28,-16],[-28,-24],[-3,-15,-20],[-3,-17,-20],[-4,-13,-20],[-4,-15,-20],[-3,-23,-27],[-3,-25,-27],[-4,-21,-27],[-4,-23,-27],[-8,28],[-20,27],[-27,20],[-29,6,8,11,12],[-30,2,13,14,15,17,18],[-31,1,3,4,5,7],[-32,21,22,23,25,26],[-33,9,10,16,24],[-34,29],[-35,30],[-35,31],[-36,34],[-36,35],[-37,32],[-38,33],[-39,37],[-39,38],[-40,36],[-40,39],[40],[-41,19,20],[-42,27],[-43,28],[-44,41],[-45,42,43],[-46,44,45],[46]],\"atoms\":[{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":60,\"b\":38},{\"tag\":\"incompatible\",\"a\":60,\"b\":45},{\"tag\":\"incompatible\",\"a\":62,\"b\":40},{\"tag\":\"incompatible\",\"a\":66,\"b\":44},{\"tag\":\"incompatible\",\"a\":68,\"b\":39},{\"tag\":\"incompatible\",\"a\":68,\"b\":62},{\"tag\":\"incompatible\",\"a\":68,\"b\":63},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":74,\"b\":40},{\"tag\":\"incompatible\",\"a\":75,\"b\":63},{\"tag\":\"incompatible\",\"a\":78,\"b\":44},{\"tag\":\"incompatible\",\"a\":83,\"b\":39},{\"tag\":\"incompatible\",\"a\":83,\"b\":46},{\"tag\":\"incompatible\",\"a\":83,\"b\":47},{\"tag\":\"incompatible\",\"a\":83,\"b\":61},{\"tag\":\"incompatible\",\"a\":83,\"b\":67},{\"tag\":\"incompatible\",\"a\":83,\"b\":79},{\"tag\":\"incompatible\",\"a\":85,\"b\":53},{\"tag\":\"incompatible\",\"a\":85,\"b\":57},{\"tag\":\"incompatible\",\"a\":85,\"b\":65},{\"tag\":\"incompatible\",\"a\":85,\"b\":77},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[40,64,71]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[40,66,71]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[44,62,71]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[44,64,71]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[40,76,83]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[40,78,83]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[44,74,83]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[44,76,83]},{\"tag\":\"mate\",\"ridge\":770,\"a\":48,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":900,\"a\":71,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":900,\"a\":83,\"owners\":[71]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[46,48,60,61],\"full_literals\":[-29,6,8,11,12]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[39,62,63,64,66,67],\"full_literals\":[-30,2,13,14,15,17,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[38,40,44,45,47],\"full_literals\":[-31,1,3,4,5,7]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[74,75,76,78,79],\"full_literals\":[-32,21,22,23,25,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[53,57,65,77],\"full_literals\":[-33,9,10,16,24]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-34,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,30,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-35,false,31],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-36,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-36,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-39,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-40,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-40,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[68,71],\"full_literals\":[-41,19,20]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[83],\"full_literals\":[-42,27]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[85],\"full_literals\":[-43,28]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,41,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "59 36 0 51 49 0\n60 39 0 51 50 0\n61 34 0 59 43 0\n62 35 0 59 44 0\n63 37 0 60 47 0\n64 38 0 60 48 0\n65 29 0 61 40 0\n66 30 0 62 41 0\n67 31 0 62 42 0\n68 32 0 63 45 0\n69 33 0 64 46 0\n70 -28 0 69 20 21 22 23 39 0\n71 -8 0 70 32 0\n72 -43 0 70 54 0\n73 -4 -27 0 66 68 34 19 18 14 4 13 26 27 30 31 36 38 12 0\n74 -27 0 71 65 67 66 68 14 15 16 17 18 19 34 35 1 2 73 37 3 11 24 25 28 29 36 38 12 0\n75 -20 0 74 33 0\n76 -42 0 74 53 0\n77 -45 0 76 72 56 0\n78 44 0 77 58 57 0\n79 41 0 78 55 0\n80 19 0 79 75 52 0\n81 -2 0 80 5 0\n82 -13 0 80 6 0\n83 -14 0 80 7 0\n84 -15 0 80 8 0\n85 -17 0 80 9 0\n86 -18 0 80 10 0\n87 0 84 83 66 86 82 85 81 36 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00013.record078
