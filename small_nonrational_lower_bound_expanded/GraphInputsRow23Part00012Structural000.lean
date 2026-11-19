module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00012Data
public import GraphInputsRow23Part00012Frames
public import GraphInputsRow23Part00012Leaves
public import GraphInputsRow23Part00012Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00012.record056
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record056
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 9043245643946000384, (certNat% 6), (certNat% 7), 17979214137393152]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record056_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record056_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record056_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record056_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record056_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record056_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record056_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record056_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record056_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00012.record056

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00012.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5aa9a9687a69966a59964b86e8789e1783e5a6999647969565a55954b46d8749d1743de0dc368d9394d5334c73a2e4b52e2b4ac9b0ee8751ca719e1745c570de0f43c8f13d62a486a8685a619262582e07961a446986459615252542d0768360d4348c6384c9314e0b12c2b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "492492492492492492492492492492492492492491249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 39), (facetIndex 43), (facetIndex 46), (facetIndex 47), (facetIndex 61), (facetIndex 73), (facetIndex 87)]))
 (.leaf ([(facetIndex 48), (facetIndex 57), (facetIndex 60), (facetIndex 62), (facetIndex 63)])))
 (.branch 3
 (.leaf ([(facetIndex 58), (facetIndex 70), (facetIndex 84)]))
 (.branch 4
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 54), (facetIndex 59), (facetIndex 75), (facetIndex 89)]))
 (.leaf ([(facetIndex 45), (facetIndex 51), (facetIndex 53), (facetIndex 69), (facetIndex 77), (facetIndex 83), (facetIndex 91)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 44), (facetIndex 66), (facetIndex 67), (facetIndex 71), (facetIndex 76)]))
 (.leaf ([(facetIndex 80), (facetIndex 81), (facetIndex 85), (facetIndex 90)])))
 (.branch 8
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 40), (facetIndex 52), (facetIndex 55)]))
 (.branch 9
 (.leaf ([(facetIndex 42), (facetIndex 65), (facetIndex 68), (facetIndex 72), (facetIndex 79), (facetIndex 82), (facetIndex 86)]))
 (.leaf ([(facetIndex 41), (facetIndex 56), (facetIndex 64), (facetIndex 74), (facetIndex 78), (facetIndex 88)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "4639086248668945390852485589110132197347433100450897077z25;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [4]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6]
def grouped2_0010 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0011 : List Nat := [6]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8, 9]
def grouped2_0014 : List Nat := [8]
def grouped2_0015 : List Nat := [8, 9]
def grouped2_0016 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00012.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00012.record004" 63

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00012.record004" "{\"ridges\":[[8,521],[8,522],[9,82],[17,28],[18,13],[22,88],[23,529],[23,536],[27,28],[28,14],[32,26],[32,88],[33,26],[33,536],[40,521],[42,82],[49,26],[52,521],[54,521],[54,522],[55,521],[56,82],[57,82],[58,82],[59,82],[59,529],[64,28],[66,28],[69,13],[71,529],[74,88],[78,28],[79,28],[79,88],[80,26],[80,28],[81,28],[83,14],[88,88],[89,88],[89,536],[90,26],[90,522],[90,536]],\"owners\":[[18,13,[0,17,37,38,39,40,65,66,67],[68,69]],[69,13,[0,17,37,38,40,65,66,67],[18,39,68]],[28,14,[0,27,37,38,39,40,79,80,81],[82,83]],[83,14,[0,27,37,38,40,79,80,81],[28,39,82]],[8,521,[23,67,75,76],[40,52,54,55]],[40,521,[23,75,76],[8,52,54,55,67]],[52,521,[23,67,75,76],[8,40,54,55]],[54,521,[23,67,76],[8,40,52,55,75]],[55,521,[23,67,75],[8,40,52,54,76]],[8,522,[33,81,89,90],[40,52,54,55]],[54,522,[33,81,90],[8,40,52,55,89]],[90,522,[8,40,52,54],[33,55,81,89]],[9,82,[32,79,88,89],[42,56,57,58,59]],[42,82,[32,88,89],[9,56,57,58,59,79]],[56,82,[32,79,89],[9,42,57,58,59,88]],[57,82,[32,79,88,89],[9,42,56,58,59]],[58,82,[32,79,88,89],[9,42,56,57,59]],[59,82,[32,79,88],[9,42,56,57,58,89]],[17,28,[27,78,79,80,81],[64,65,66,67]],[27,28,[17,64,65,66,67],[78,79,80,81]],[64,28,[27,79,80,81],[17,65,66,67,78]],[66,28,[27,78,79,81],[17,64,65,67,80]],[78,28,[17,65,66,67],[27,64,79,80,81]],[79,28,[17,64,66,67],[27,65,78,80,81]],[80,28,[17,64,65,67],[27,66,78,79,81]],[81,28,[17,64,65,66],[27,67,78,79,80]],[22,88,[32,79,88,89],[65,74,75]],[32,88,[22,65,74,75],[79,88,89]],[74,88,[32,79,89],[22,65,75,88]],[79,88,[22,74,75],[32,65,88,89]],[88,88,[22,65,75],[32,74,79,89]],[89,88,[22,65,74],[32,75,79,88]],[23,536,[33,81,89,90],[67,75,76]],[33,536,[23,67,75,76],[81,89,90]],[89,536,[23,67,76],[33,75,81,90]],[90,536,[23,67,75],[33,76,81,89]]],\"edges\":[[17,[0,17,18,27,28,37,38,39,40,64,65,66,67,68,69,78,79,80,81,82,83]],[29,[8,23,33,40,52,54,55,67,75,76,81,89,90]],[31,[9,22,32,42,56,57,58,59,65,74,75,79,88,89]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00012.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00012.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-12,-2],[-16,-12],[-21,-1],[-21,-12],[-21,-14],[-21,-19],[-22,-12],[-22,-21],[-24,-12],[-26,-12],[-26,-22],[-27,-23],[-27,-26],[-28,-12],[-29,-7],[-30,-13],[-30,-23],[-30,-29],[-31,-6],[-31,-29],[-32,-21],[-34,-30],[-35,-15],[-35,-20],[-36,-12],[-36,-31],[-37,-4],[-37,-22],[-37,-28],[-37,-29],[-37,-30],[-37,-31],[-38,-13],[-38,-20],[-38,-23],[-38,-27],[-38,-29],[-38,-30],[-38,-37],[-39,-12],[-41,-18],[-41,-23],[-41,-30],[-41,-38],[-41,-40],[-42,-10],[-42,-18],[-42,-35],[-42,-40],[-43,-21],[-46,-15],[-46,-18],[-46,-20],[-46,-35],[-46,-42],[-46,-45],[-47,-12],[-47,-19],[-47,-22],[-47,-42],[-48,-8],[-48,-39],[-48,-40],[-48,-41],[-48,-42],[-49,-13],[-49,-18],[-49,-23],[-49,-27],[-49,-30],[-49,-38],[-49,-40],[-49,-48],[-5,1,4,12,13,14,15,29,30,31],[-33,1,4,12,13,15,29,30,31],[-9,1,8,12,13,14,15,40,41,42],[-44,1,8,12,13,15,40,41,42],[-10,-11,-41],[-10,-19,-49],[-2,7,31,37,38],[-15,7,37,38],[-21,7,31,37,38],[-22,7,31,38],[-23,7,31,37],[-2,11,42,48,49],[-22,11,42,49],[-49,2,15,21,22],[-3,10,40,47,48],[-17,10,47,48],[-24,10,40,48],[-25,10,40,47,48],[-26,10,40,47,48],[-27,10,40,47],[-7,-27,-35],[-4,8,39,40,41,42],[-8,4,28,29,30,31],[-28,8,40,41,42],[-30,8,39,40,42],[-39,4,29,30,31],[-40,4,28,30,31],[-41,4,28,29,31],[-42,4,28,29,30],[-6,10,40,47,48],[-10,6,29,36,37],[-36,10,40,48],[-40,6,36,37],[-47,6,29,37],[-48,6,29,36],[-7,11,42,48,49],[-11,7,31,37,38],[-48,7,31,38],[-49,7,31,37],[-50,26,34,45],[-51,19,20,22,27,37,48],[-52,18,30,31,35,38],[-53,41,42,46,49],[-54,12,13,15,21,23],[-55,16,24,28,36,39,47],[-56,51],[-57,50],[-57,56],[-58,57],[-59,52],[-59,53],[-60,55],[-61,54],[-61,60],[-62,59],[-62,61],[-63,58],[-63,62],[63],[1,4,5,8,9,12,13,14,15,28,29,30,31,32,33,39,40,41,42,43,44],[2,7,11,15,21,22,23,31,37,38,42,48,49],[3,6,10,17,24,25,26,27,29,36,37,40,47,48]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":37,\"b\":8},{\"tag\":\"incompatible\",\"a\":41,\"b\":37},{\"tag\":\"incompatible\",\"a\":52,\"b\":0},{\"tag\":\"incompatible\",\"a\":52,\"b\":37},{\"tag\":\"incompatible\",\"a\":52,\"b\":39},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":54,\"b\":37},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":37},{\"tag\":\"incompatible\",\"a\":58,\"b\":37},{\"tag\":\"incompatible\",\"a\":58,\"b\":54},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":37},{\"tag\":\"incompatible\",\"a\":65,\"b\":23},{\"tag\":\"incompatible\",\"a\":66,\"b\":38},{\"tag\":\"incompatible\",\"a\":66,\"b\":55},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":22},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":52},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":40},{\"tag\":\"incompatible\",\"a\":71,\"b\":50},{\"tag\":\"incompatible\",\"a\":74,\"b\":37},{\"tag\":\"incompatible\",\"a\":74,\"b\":67},{\"tag\":\"incompatible\",\"a\":75,\"b\":17},{\"tag\":\"incompatible\",\"a\":75,\"b\":54},{\"tag\":\"incompatible\",\"a\":75,\"b\":64},{\"tag\":\"incompatible\",\"a\":75,\"b\":65},{\"tag\":\"incompatible\",\"a\":75,\"b\":66},{\"tag\":\"incompatible\",\"a\":75,\"b\":67},{\"tag\":\"incompatible\",\"a\":76,\"b\":38},{\"tag\":\"incompatible\",\"a\":76,\"b\":50},{\"tag\":\"incompatible\",\"a\":76,\"b\":55},{\"tag\":\"incompatible\",\"a\":76,\"b\":59},{\"tag\":\"incompatible\",\"a\":76,\"b\":65},{\"tag\":\"incompatible\",\"a\":76,\"b\":66},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":37},{\"tag\":\"incompatible\",\"a\":80,\"b\":44},{\"tag\":\"incompatible\",\"a\":80,\"b\":55},{\"tag\":\"incompatible\",\"a\":80,\"b\":66},{\"tag\":\"incompatible\",\"a\":80,\"b\":76},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"incompatible\",\"a\":81,\"b\":32},{\"tag\":\"incompatible\",\"a\":81,\"b\":44},{\"tag\":\"incompatible\",\"a\":81,\"b\":71},{\"tag\":\"incompatible\",\"a\":81,\"b\":79},{\"tag\":\"incompatible\",\"a\":82,\"b\":52},{\"tag\":\"incompatible\",\"a\":85,\"b\":40},{\"tag\":\"incompatible\",\"a\":85,\"b\":44},{\"tag\":\"incompatible\",\"a\":85,\"b\":50},{\"tag\":\"incompatible\",\"a\":85,\"b\":71},{\"tag\":\"incompatible\",\"a\":85,\"b\":81},{\"tag\":\"incompatible\",\"a\":85,\"b\":84},{\"tag\":\"incompatible\",\"a\":88,\"b\":37},{\"tag\":\"incompatible\",\"a\":88,\"b\":49},{\"tag\":\"incompatible\",\"a\":88,\"b\":54},{\"tag\":\"incompatible\",\"a\":88,\"b\":81},{\"tag\":\"incompatible\",\"a\":89,\"b\":27},{\"tag\":\"incompatible\",\"a\":89,\"b\":78},{\"tag\":\"incompatible\",\"a\":89,\"b\":79},{\"tag\":\"incompatible\",\"a\":89,\"b\":80},{\"tag\":\"incompatible\",\"a\":89,\"b\":81},{\"tag\":\"incompatible\",\"a\":90,\"b\":38},{\"tag\":\"incompatible\",\"a\":90,\"b\":44},{\"tag\":\"incompatible\",\"a\":90,\"b\":55},{\"tag\":\"incompatible\",\"a\":90,\"b\":59},{\"tag\":\"incompatible\",\"a\":90,\"b\":66},{\"tag\":\"incompatible\",\"a\":90,\"b\":76},{\"tag\":\"incompatible\",\"a\":90,\"b\":79},{\"tag\":\"incompatible\",\"a\":90,\"b\":89},{\"tag\":\"mate\",\"ridge\":13,\"a\":18,\"owners\":[0,17,37,38,39,40,65,66,67]},{\"tag\":\"mate\",\"ridge\":13,\"a\":69,\"owners\":[0,17,37,38,40,65,66,67]},{\"tag\":\"mate\",\"ridge\":14,\"a\":28,\"owners\":[0,27,37,38,39,40,79,80,81]},{\"tag\":\"mate\",\"ridge\":14,\"a\":83,\"owners\":[0,27,37,38,40,79,80,81]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[32,33,80]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[32,49,90]},{\"tag\":\"mate\",\"ridge\":521,\"a\":8,\"owners\":[23,67,75,76]},{\"tag\":\"mate\",\"ridge\":521,\"a\":40,\"owners\":[23,75,76]},{\"tag\":\"mate\",\"ridge\":521,\"a\":52,\"owners\":[23,67,75,76]},{\"tag\":\"mate\",\"ridge\":521,\"a\":54,\"owners\":[23,67,76]},{\"tag\":\"mate\",\"ridge\":521,\"a\":55,\"owners\":[23,67,75]},{\"tag\":\"mate\",\"ridge\":522,\"a\":8,\"owners\":[33,81,89,90]},{\"tag\":\"mate\",\"ridge\":522,\"a\":54,\"owners\":[33,81,90]},{\"tag\":\"mate\",\"ridge\":522,\"a\":90,\"owners\":[8,40,52,54]},{\"tag\":\"mate\",\"ridge\":82,\"a\":9,\"owners\":[32,79,88,89]},{\"tag\":\"mate\",\"ridge\":82,\"a\":42,\"owners\":[32,88,89]},{\"tag\":\"mate\",\"ridge\":82,\"a\":56,\"owners\":[32,79,89]},{\"tag\":\"mate\",\"ridge\":82,\"a\":57,\"owners\":[32,79,88,89]},{\"tag\":\"mate\",\"ridge\":82,\"a\":58,\"owners\":[32,79,88,89]},{\"tag\":\"mate\",\"ridge\":82,\"a\":59,\"owners\":[32,79,88]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[23,59,71]},{\"tag\":\"mate\",\"ridge\":28,\"a\":17,\"owners\":[27,78,79,80,81]},{\"tag\":\"mate\",\"ridge\":28,\"a\":27,\"owners\":[17,64,65,66,67]},{\"tag\":\"mate\",\"ridge\":28,\"a\":64,\"owners\":[27,79,80,81]},{\"tag\":\"mate\",\"ridge\":28,\"a\":66,\"owners\":[27,78,79,81]},{\"tag\":\"mate\",\"ridge\":28,\"a\":78,\"owners\":[17,65,66,67]},{\"tag\":\"mate\",\"ridge\":28,\"a\":79,\"owners\":[17,64,66,67]},{\"tag\":\"mate\",\"ridge\":28,\"a\":80,\"owners\":[17,64,65,67]},{\"tag\":\"mate\",\"ridge\":28,\"a\":81,\"owners\":[17,64,65,66]},{\"tag\":\"mate\",\"ridge\":88,\"a\":22,\"owners\":[32,79,88,89]},{\"tag\":\"mate\",\"ridge\":88,\"a\":32,\"owners\":[22,65,74,75]},{\"tag\":\"mate\",\"ridge\":88,\"a\":74,\"owners\":[32,79,89]},{\"tag\":\"mate\",\"ridge\":88,\"a\":79,\"owners\":[22,74,75]},{\"tag\":\"mate\",\"ridge\":88,\"a\":88,\"owners\":[22,65,75]},{\"tag\":\"mate\",\"ridge\":88,\"a\":89,\"owners\":[22,65,74]},{\"tag\":\"mate\",\"ridge\":536,\"a\":23,\"owners\":[33,81,89,90]},{\"tag\":\"mate\",\"ridge\":536,\"a\":33,\"owners\":[23,67,75,76]},{\"tag\":\"mate\",\"ridge\":536,\"a\":89,\"owners\":[23,67,76]},{\"tag\":\"mate\",\"ridge\":536,\"a\":90,\"owners\":[23,67,75]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[58,70,84],\"full_literals\":[-50,26,34,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[49,50,54,59,75,89],\"full_literals\":[-51,19,20,22,27,37,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[44,66,67,71,76],\"full_literals\":[-52,18,30,31,35,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[80,81,85,90],\"full_literals\":[-53,41,42,46,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[37,38,40,52,55],\"full_literals\":[-54,12,13,15,21,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[41,56,64,74,78,88],\"full_literals\":[-55,16,24,28,36,39,47]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-57,50,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-58,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-61,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-62,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-62,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-63,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-63,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":17,\"owners\":[0,17,18,27,28,37,38,39,40,64,65,66,67,68,69,78,79,80,81,82,83]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[8,23,33,40,52,54,55,67,75,76,81,89,90]},{\"tag\":\"edge\",\"edge\":31,\"owners\":[9,22,32,42,56,57,58,59,65,74,75,79,88,89]}]}"
  "136 58 0 132 130 0\n137 62 0 132 131 0\n138 57 0 136 122 0\n139 59 0 137 128 0\n140 61 0 137 129 0\n141 50 0 138 120 0\n142 56 0 138 121 0\n143 52 0 139 123 0\n144 53 0 139 124 0\n145 54 0 140 126 0\n146 60 0 140 127 0\n147 51 0 142 119 0\n148 55 0 146 125 0\n149 37 7 2 49 11 22 23 31 15 38 42 48 0 134 82 0\n150 -42 30 38 31 0 143 47 48 115 0\n151 -18 42 46 0 144 41 67 116 0\n152 -49 12 27 20 15 37 0 145 147 66 68 73 117 6 8 114 0\n153 -29 0 15 18 20 30 37 80 111 83 150 110 112 84 81 149 0\n154 48 10 47 40 37 0 153 93 92 88 103 89 91 105 90 135 0\n155 -48 40 38 31 0 144 143 61 62 64 65 73 98 116 52 54 115 0\n156 -46 48 37 38 31 0 143 141 145 147 51 52 53 54 56 115 16 17 22 113 10 11 13 117 114 6 0\n157 -30 42 46 0 144 43 70 116 0\n158 49 -10 48 37 38 31 0 143 144 46 156 151 157 115 23 116 42 78 85 109 86 149 0\n159 -10 48 37 38 31 0 143 147 156 46 151 157 115 23 24 158 69 152 79 114 7 0\n160 40 37 38 31 0 143 147 155 156 159 154 58 59 60 157 151 115 23 24 114 12 69 94 80 110 149 0\n161 37 38 31 0 144 160 45 49 63 72 156 116 0\n162 12 15 23 13 -37 31 0 145 153 31 27 29 102 100 96 101 99 117 3 5 21 50 77 76 75 74 133 0\n163 46 38 31 0 153 144 143 161 31 27 29 102 101 28 116 151 66 68 115 23 162 1 4 87 0\n164 38 31 0 143 161 31 163 52 54 115 0\n165 -12 0 148 2 9 14 25 40 57 118 0\n166 -46 31 0 145 147 153 165 164 44 39 38 36 35 34 33 51 55 117 3 5 6 8 21 50 114 61 62 63 95 97 77 76 75 74 133 0\n167 31 0 144 164 39 44 71 166 116 46 49 60 65 154 0\n168 -6 0 167 19 0\n169 -36 0 167 26 0\n170 -37 0 167 32 0\n171 -47 0 168 170 153 107 0\n172 -10 0 169 168 170 153 104 0\n173 -40 0 169 168 170 106 0\n174 -48 0 169 168 153 108 0\n175 0 172 171 174 173 170 154 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00012.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00012.record004
