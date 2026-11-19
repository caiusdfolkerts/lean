module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00013Data
public import GraphInputsRow16Part00013Frames
public import GraphInputsRow16Part00013Leaves
public import GraphInputsRow16Part00013Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00013.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 432345564227567616, (certNat% 4), 527766118203392, 233001975808]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), 109126529056768, 495395959010754560, (certNat% 4), (certNat% 7)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), 495395959010754560, 529689726681088, (certNat% 4), (certNat% 9)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 4), 270215977642229760, 164282499072, 297237575406452736, (certNat% 11)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 14), 563087526592512, 270215977642229760, 288230376151711744]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), 72066939886764032, 163208757248, 949978046398464, 140737488355328]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 19), 529415385645056, 486388759957340160, (certNat% 20), 25769803776]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00013.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00013.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "c723cc693ac58d62db0e3386e8791e0fb198e539c5695356352d70d934cd8b46d8751d0f71364cd34ccb3c2d4b32d2b1ae1b46c3bc1ca719e1745c5783d0f23c1f318960d84e0bb11c24c5854950d60d1342d30d1324c3342c4b0ac8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6da4d26d26d24924924d24924924d2692492489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 27), (facetIndex 33), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 26), (facetIndex 34), (facetIndex 65), (facetIndex 71)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 42)]))
 (.leaf ([(facetIndex 30), (facetIndex 46), (facetIndex 59), (facetIndex 72)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 37), (facetIndex 43), (facetIndex 48), (facetIndex 64)]))
 (.leaf ([(facetIndex 29), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55)])))
 (.branch 7
 (.leaf ([(facetIndex 32), (facetIndex 49), (facetIndex 51), (facetIndex 57), (facetIndex 58), (facetIndex 60)]))
 (.branch 8
 (.leaf ([(facetIndex 31), (facetIndex 56), (facetIndex 61)]))
 (.leaf ([(facetIndex 36), (facetIndex 44), (facetIndex 45), (facetIndex 47)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "31000001400763667555560648388422220480106735201z1a;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 38), (facetIndex 50)]))
 (.leaf ([(facetIndex 66), (facetIndex 67), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 73), (facetIndex 75), (facetIndex 77)]))
 (.branch 4
 (.leaf ([(facetIndex 62), (facetIndex 63)]))
 (.leaf ([(facetIndex 74), (facetIndex 76)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "145100402406cz2e;"⟩
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
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1]
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [2]
def grouped3_0022 : List Nat := [2, 3, 4]
def grouped3_0023 : List Nat := [3]
def grouped3_0024 : List Nat := [3, 4]
def grouped3_0025 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00013.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00013.record008" 84

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00013.record008" "{\"ridges\":[[19,769],[19,776],[20,784],[29,524],[31,273],[31,274],[32,529],[37,266],[37,274],[43,266],[43,776],[48,274],[48,784],[51,529],[56,524],[56,769],[56,776],[58,529],[60,529],[61,532],[61,784],[64,776],[64,784],[70,774],[73,774],[73,784],[75,538],[77,284],[77,784]],\"owners\":[[37,266,[70],[7,28,40,42,43,66,74,75]],[43,266,[66,74],[7,28,37,40,42,70,75]],[31,273,[20,62,64],[10,37,45,47,50,61]],[31,274,[74,75],[10,37,45,47,48,66,73]],[37,274,[73],[10,31,45,47,48,66,74,75]],[48,274,[66,74],[10,31,37,45,47,73,75]],[29,524,[76,77],[14,51,53,55,56,67,70]],[56,524,[67,76],[14,29,51,53,55,70,77]],[32,529,[20,63,64],[17,38,48,51,58,60]],[51,529,[20,48],[17,32,38,58,60,63,64]],[58,529,[20,38,48,64],[17,32,51,60,63]],[60,529,[20,38,48,63,64],[17,32,51,58]],[61,532,[67,76],[17,32,51,58,60,73,77]],[19,769,[20,35,48,61],[43,56]],[56,769,[20,48],[19,35,43,61]],[19,776,[70,75,77],[43,56,64]],[43,776,[77],[19,56,64,70,75]],[56,776,[75],[19,43,64,70,77]],[64,776,[70],[19,43,56,75,77]],[20,784,[73,75,77],[48,61,64]],[48,784,[77],[20,61,64,73,75]],[61,784,[75],[20,48,64,73,77]],[64,784,[73],[20,48,61,75,77]],[73,784,[20,64],[48,61,75,77]],[77,784,[20,48],[61,64,73,75]],[70,774,[35,73],[]],[73,774,[35,70],[]],[75,538,[38,67],[]],[77,284,[50,66],[]]],\"edges\":[[44,[19,20,35,43,48,56,61,64,70,73,75,77]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00013.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00013.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-7],[-12,-8],[-13,-8],[-14,-3],[-15,-8],[-18,-4],[-18,-10],[-20,-5],[-20,-16],[-20,-17],[-20,-19],[-21,-8],[-22,-8],[-23,-11],[-24,-8],[-31,-4],[-31,-10],[-33,-29],[-33,-30],[-33,-32],[-36,-11],[-38,-2],[-38,-9],[-38,-25],[-38,-28],[-38,-34],[-38,-35],[-38,-37],[-41,-3],[-41,-33],[-41,-38],[-42,-14],[-42,-41],[-43,-3],[-43,-38],[-43,-42],[-44,-26],[-45,-43],[-45,-44],[-46,-18],[-46,-31],[-47,-8],[-47,-33],[-47,-38],[-48,-43],[-48,-44],[-49,-11],[-50,-48],[-52,-26],[-54,-8],[-54,-33],[-14,47],[-20,43,51],[-8,2,39,41],[-8,51,52],[-14,50],[-25,43,51],[-6,53,54],[-33,44,53],[-9,2,40,41],[-28,2,25],[-35,2,15,25,41],[-37,2,15,25,40,41],[-38,44,53],[-1,2,12,25,38],[-33,2,25],[-1,47,52,54],[-20,54],[-33,52],[-41,47],[-2,50,52,54],[-25,54],[-38,52],[-41,50],[-50,2,41],[-54,2,25],[-47,12,50],[-50,12,47],[-52,15,44],[-54,27,43],[-55,4,10,45,46],[-56,3,11,42,48],[-57,5,16,17,18,19],[-58,7,23,36,49],[-59,14,20,25,41],[-25,59],[-41,59],[-60,6,29,30,31,32],[-61,9,26,28,34,35,37],[-62,8,33,38],[-63,13,21,22,24],[-64,55],[-64,56],[-65,57],[-65,58],[-66,64],[-66,65],[-67,59,60],[-68,59],[-59,-60,68],[-69,62],[-69,63],[-70,61],[-70,69],[-71,67],[-71,68,70],[-72,68],[-72,70],[-68,-70,72],[-73,66,72],[-73,71],[73],[-12,74],[-15,74],[-27,74],[-75,43,44,47],[-43,75],[-44,75],[-47,75],[-76,50,52,54],[-50,76],[-52,76],[-54,76],[-39,77],[-40,77],[-51,78],[-53,78],[-75,79],[-74,79],[-74,-75,80],[-78,81],[-77,81],[-76,82],[-76,-81,83],[-79,-83,84],[-80,-82,84],[-84],[1,2,12,20,25,33,38,41,47,50,52,54]],\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":34,\"b\":30},{\"tag\":\"incompatible\",\"a\":35,\"b\":31},{\"tag\":\"incompatible\",\"a\":36,\"b\":31},{\"tag\":\"incompatible\",\"a\":37,\"b\":26},{\"tag\":\"incompatible\",\"a\":38,\"b\":31},{\"tag\":\"incompatible\",\"a\":41,\"b\":27},{\"tag\":\"incompatible\",\"a\":41,\"b\":33},{\"tag\":\"incompatible\",\"a\":43,\"b\":28},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":40},{\"tag\":\"incompatible\",\"a\":43,\"b\":42},{\"tag\":\"incompatible\",\"a\":44,\"b\":31},{\"tag\":\"incompatible\",\"a\":45,\"b\":31},{\"tag\":\"incompatible\",\"a\":46,\"b\":34},{\"tag\":\"incompatible\",\"a\":47,\"b\":31},{\"tag\":\"incompatible\",\"a\":54,\"b\":27},{\"tag\":\"incompatible\",\"a\":54,\"b\":33},{\"tag\":\"incompatible\",\"a\":56,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":34},{\"tag\":\"incompatible\",\"a\":61,\"b\":20},{\"tag\":\"incompatible\",\"a\":61,\"b\":32},{\"tag\":\"incompatible\",\"a\":61,\"b\":48},{\"tag\":\"incompatible\",\"a\":61,\"b\":51},{\"tag\":\"incompatible\",\"a\":61,\"b\":57},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":64,\"b\":26},{\"tag\":\"incompatible\",\"a\":64,\"b\":56},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":65,\"b\":37},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":26},{\"tag\":\"incompatible\",\"a\":66,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":49},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":41},{\"tag\":\"incompatible\",\"a\":69,\"b\":54},{\"tag\":\"incompatible\",\"a\":70,\"b\":31},{\"tag\":\"incompatible\",\"a\":70,\"b\":56},{\"tag\":\"incompatible\",\"a\":70,\"b\":61},{\"tag\":\"incompatible\",\"a\":71,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":67},{\"tag\":\"incompatible\",\"a\":72,\"b\":34},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":75,\"b\":49},{\"tag\":\"incompatible\",\"a\":77,\"b\":31},{\"tag\":\"incompatible\",\"a\":77,\"b\":56},{\"tag\":\"mate\",\"ridge\":266,\"a\":37,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":266,\"a\":43,\"owners\":[66,74]},{\"tag\":\"mate\",\"ridge\":273,\"a\":31,\"owners\":[20,62,64]},{\"tag\":\"mate\",\"ridge\":274,\"a\":31,\"owners\":[74,75]},{\"tag\":\"mate\",\"ridge\":274,\"a\":37,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":274,\"a\":48,\"owners\":[66,74]},{\"tag\":\"mate\",\"ridge\":524,\"a\":29,\"owners\":[76,77]},{\"tag\":\"mate\",\"ridge\":524,\"a\":56,\"owners\":[67,76]},{\"tag\":\"mate\",\"ridge\":529,\"a\":32,\"owners\":[20,63,64]},{\"tag\":\"mate\",\"ridge\":529,\"a\":51,\"owners\":[20,48]},{\"tag\":\"mate\",\"ridge\":529,\"a\":58,\"owners\":[20,38,48,64]},{\"tag\":\"mate\",\"ridge\":529,\"a\":60,\"owners\":[20,38,48,63,64]},{\"tag\":\"mate\",\"ridge\":532,\"a\":61,\"owners\":[67,76]},{\"tag\":\"mate\",\"ridge\":769,\"a\":19,\"owners\":[20,35,48,61]},{\"tag\":\"mate\",\"ridge\":769,\"a\":56,\"owners\":[20,48]},{\"tag\":\"mate\",\"ridge\":776,\"a\":19,\"owners\":[70,75,77]},{\"tag\":\"mate\",\"ridge\":776,\"a\":43,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":776,\"a\":56,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":776,\"a\":64,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":784,\"a\":20,\"owners\":[73,75,77]},{\"tag\":\"mate\",\"ridge\":784,\"a\":48,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":784,\"a\":61,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":784,\"a\":64,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":784,\"a\":73,\"owners\":[20,64]},{\"tag\":\"mate\",\"ridge\":784,\"a\":77,\"owners\":[20,48]},{\"tag\":\"mate\",\"ridge\":774,\"a\":70,\"owners\":[35,73]},{\"tag\":\"mate\",\"ridge\":774,\"a\":73,\"owners\":[35,70]},{\"tag\":\"mate\",\"ridge\":538,\"a\":75,\"owners\":[38,67]},{\"tag\":\"mate\",\"ridge\":284,\"a\":77,\"owners\":[50,66]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[27,33,68,69],\"full_literals\":[-55,4,10,45,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[26,34,65,71],\"full_literals\":[-56,3,11,42,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[28,39,40,41,42],\"full_literals\":[-57,5,16,17,18,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[30,46,59,72],\"full_literals\":[-58,7,23,36,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[37,43,48,64],\"full_literals\":[-59,14,20,25,41]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":48,\"full_literals\":[-25,59]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":64,\"full_literals\":[-41,59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[29,52,53,54,55],\"full_literals\":[-60,6,29,30,31,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[32,49,51,57,58,60],\"full_literals\":[-61,9,26,28,34,35,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[31,56,61],\"full_literals\":[-62,8,33,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[36,44,45,47],\"full_literals\":[-63,13,21,22,24]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,59,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-60,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-69,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-70,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-70,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-71,67,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-71,68,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-72,68,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-72,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-68,-70,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-73,66,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-73,false,71],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":35,\"full_literals\":[-12,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":38,\"full_literals\":[-15,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":50,\"full_literals\":[-27,74]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[66,67,70],\"full_literals\":[-75,43,44,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-43,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-44,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":70,\"full_literals\":[-47,75]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[73,75,77],\"full_literals\":[-76,50,52,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":73,\"full_literals\":[-50,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-52,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":77,\"full_literals\":[-54,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":62,\"full_literals\":[-39,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":63,\"full_literals\":[-40,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-51,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-53,78]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-74,-75,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-77,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-81,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-79,-83,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-80,-82,84],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":44,\"owners\":[19,20,35,43,48,56,61,64,70,73,75,77]}]}"
  "139 71 0 112 111 0\n140 67 0 139 105 0\n141 79 0 128 129 117 118 119 113 114 115 79 70 78 80 69 73 67 71 68 72 138 0\n142 -83 0 141 137 135 0\n143 76 0 139 121 122 123 56 71 74 69 73 68 72 85 99 106 104 101 90 2 42 65 138 0\n144 82 0 143 133 0\n145 -81 0 143 142 134 0\n146 -80 0 144 137 136 0\n147 -78 0 145 131 0\n148 -77 0 145 132 0\n149 -51 0 147 126 0\n150 -53 0 147 127 0\n151 -39 0 148 124 0\n152 -40 0 148 125 0\n153 75 0 150 139 149 117 118 119 53 57 59 64 52 70 85 99 106 104 101 90 5 55 79 0\n154 -74 0 153 146 130 0\n155 -12 0 154 113 0\n156 -15 0 154 114 0\n157 2 59 -70 0 151 152 156 143 87 86 104 101 103 61 66 76 54 60 63 75 62 120 90 49 26 89 0\n158 -54 38 -62 0 50 51 90 0\n159 -8 -63 0 3 12 13 15 91 0\n160 -60 68 -70 -55 0 150 104 102 159 101 100 157 22 158 58 90 18 19 20 59 88 39 16 17 41 81 0\n161 38 -59 8 -62 0 158 90 68 72 30 43 85 52 0\n162 -70 72 0 112 140 150 110 96 92 103 104 109 101 102 159 160 98 161 23 25 26 27 28 64 89 37 0\n163 -38 -59 0 149 24 31 35 44 53 52 85 0\n164 -20 -66 0 149 97 94 96 92 8 9 10 11 53 83 38 6 7 40 81 0\n165 -11 -58 0 1 14 21 47 84 0\n166 -42 25 72 0 139 112 110 164 162 106 99 32 33 85 0\n167 -48 0 153 155 45 46 48 116 77 0\n168 25 72 0 139 112 167 110 97 95 165 164 162 106 99 96 93 166 82 4 29 85 0\n169 72 0 112 149 167 110 96 97 93 95 165 168 57 34 36 82 0\n170 68 0 169 107 0\n171 70 0 169 108 0\n172 59 0 170 99 0\n173 69 0 171 104 0\n174 -38 0 172 163 0\n175 62 0 173 101 0\n176 63 0 173 102 0\n177 8 0 175 172 174 161 0\n178 0 177 176 159 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00013.record008
