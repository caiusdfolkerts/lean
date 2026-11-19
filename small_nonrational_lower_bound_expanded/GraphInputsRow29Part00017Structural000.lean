module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00017Data
public import GraphInputsRow29Part00017Frames
public import GraphInputsRow29Part00017Leaves
public import GraphInputsRow29Part00017Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record012
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨87, by decide⟩, ⟨98, by decide⟩, ⟨101, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 12177733399154262016, (certNat% 3), 1134851826647040, 567416736186368, (certNat% 4), 9193914368]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record012_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record022
def vertexColumn : Fields := ⟨10, (certNat% 5)⟩
def kindColumn : Fields := ⟨3, (certNat% 6)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨85, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 8071578631178027008, (certNat% 8), (certNat% 9), 256323648225280, 126664014397702144, (certNat% 10)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record022_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ec3a89d32c1f392cca72e2b2a5a8da1eb2699a9695a361db0ea3a2e4b86e2785e0fba1e4731ac5b16a569364b91e725a56354b49d1743de0f2358f13a4d9334e334cc7352ccb4ac6b26c5b0ef07a1e2749c6785c970dd0f23c2f07e341d06ce0a9262a161584e1c5894a469194550d44d0b58324c5342c8b12c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6d349b4db6da4936da69b6db49b4da4d24db4936924926db692492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 39), (facetIndex 58), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 73), (facetIndex 75), (facetIndex 88)])))
 (.branch 3
 (.leaf ([(facetIndex 68), (facetIndex 69), (facetIndex 98)]))
 (.branch 4
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 47), (facetIndex 52), (facetIndex 99)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 35), (facetIndex 38), (facetIndex 96)]))
 (.leaf ([(facetIndex 36), (facetIndex 53), (facetIndex 77), (facetIndex 85), (facetIndex 87), (facetIndex 90), (facetIndex 93)])))
 (.branch 8
 (.leaf ([(facetIndex 37), (facetIndex 48), (facetIndex 62), (facetIndex 70), (facetIndex 72)]))
 (.branch 9
 (.leaf ([(facetIndex 54), (facetIndex 86), (facetIndex 89), (facetIndex 92)]))
 (.leaf ([(facetIndex 61), (facetIndex 71)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "42050068068168600003336010179722000007900000086400074000000005765z23;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
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
def grouped3_0009 : List Nat := [5, 6]
def grouped3_0010 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0011 : List Nat := [6]
def grouped3_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [7, 8, 9]
def grouped3_0014 : List Nat := [8]
def grouped3_0015 : List Nat := [8, 9]
def grouped3_0016 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record001" 71

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record001" "{\"ridges\":[[15,296],[20,530],[22,530],[23,770],[26,532],[38,773],[43,296],[47,306],[52,530],[52,785],[54,800],[55,896],[59,296],[62,773],[62,800],[66,296],[67,296],[68,432],[69,673],[70,289],[70,785],[70,800],[71,656],[71,785],[72,673],[72,800],[78,554],[79,652],[80,780],[82,548],[83,518],[85,518],[86,294],[86,800],[89,354],[90,554],[90,800],[91,770],[93,306],[93,800],[94,896],[96,780],[96,800],[97,548],[98,680],[99,432],[99,800]],\"owners\":[[70,289,[15,35,43,53,59,66,67],[47,54,62,68,72]],[15,296,[77,89,90,96,98],[43,59,66,67]],[43,296,[96,98],[15,59,66,67,77,89,90]],[59,296,[89,90,98],[15,43,66,67,77,96]],[66,296,[77,90,96,98],[15,43,59,67,89]],[67,296,[77,89,90,96],[15,43,59,66,98]],[83,518,[36,37,38,78,79,80,86],[20,33,82,84,85]],[85,518,[20,33,37,38,79,80,84],[36,78,82,83,86]],[26,532,[20,33,61,83,84],[60,97]],[71,656,[22,84],[51,61,69,94,99]],[23,770,[38,52,54,80,86,90,93],[55,91,94]],[91,770,[38,52,54,86,93],[23,55,80,90,94]],[55,896,[98,99],[23,71,72,91,94]],[94,896,[72,98],[23,55,71,91,99]],[82,548,[62,96],[26,36,60,78,85,86,97]],[97,548,[36,62,78,86,96],[26,60,82,85]],[86,294,[35,77],[]],[38,773,[62],[]],[62,773,[38],[]],[47,306,[93],[]],[93,306,[47],[]],[52,785,[70,71],[]],[70,785,[52,71],[]],[71,785,[52,70],[]],[89,354,[53],[]],[54,800,[96,98,99],[62,70,72,86,90,93]],[62,800,[90,93,98,99],[54,70,72,86,96]],[70,800,[86,90,96,98],[54,62,72,93,99]],[72,800,[86,90,93,96],[54,62,70,98,99]],[86,800,[70,72,98,99],[54,62,90,93,96]],[90,800,[62,70,72,99],[54,86,93,96,98]],[93,800,[62,72,96,98],[54,70,86,90,99]],[96,800,[54,70,72,93,99],[62,86,90,98]],[99,800,[54,62,86,90,96],[70,72,93,98]],[68,432,[99],[]],[99,432,[68],[]],[69,673,[72],[]],[72,673,[69],[]],[78,554,[90],[]],[90,554,[78],[]],[79,652,[],[]],[80,780,[96],[]],[96,780,[80],[]],[98,680,[],[]]],\"edges\":[[23,[20,26,33,36,37,38,60,61,62,78,79,80,82,83,84,85,86,96,97]],[37,[15,35,43,47,53,54,59,62,66,67,68,70,72,77,86,89,90,93,96,98,99]],[44,[23,38,52,54,55,62,70,71,72,80,86,90,91,93,94,96,98,99]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-6],[-13,-8],[-13,-9],[-18,-13],[-19,-13],[-34,-13],[-25,1,7,11,14,17,21,22],[-1,28,37,38,42,44],[-11,42,44],[-17,37,38,44],[-21,28,38,42,44],[-22,28,37,38,42],[-33,8,9,10,29,30,31,36],[-35,2,6,9,10,30,31,34],[-2,-3,-13],[-5,2,6,19,33,34],[-26,3,34],[-4,10,13,15,31,36,38,40],[-39,10,13,15,36,40],[-16,44,45],[-41,27,44],[-32,20,42],[-43,8,20,29,36,42],[-36,7,28],[-10,20],[-20,10],[-12,40],[-40,12],[-13,25,26],[-25,13,26],[-26,13,25],[-37,14],[-15,42,44,45],[-20,38,40,44,45],[-25,36,38,42,44],[-27,36,38,40,42],[-36,25,27,44,45],[-38,20,25,27,45],[-40,20,27,42,44],[-42,15,25,27,40,45],[-45,15,20,36,38,42],[-23,45],[-45,23],[-24,27],[-27,24],[-29,38],[-38,29],[-30],[-31,42],[-42,31],[-44],[-46,23,24,44],[-23,46],[-24,46],[-47,29,30,31],[-29,47],[-31,47],[-48,12,13,45],[-12,48],[-13,48],[-45,48],[-7,49],[-10,49],[-42,49],[-14,50],[-28,50],[-38,50],[-40,50],[-20,51],[-25,51],[-27,51],[-15,52],[-36,52],[-26,53],[-54,47,48],[-48,54],[-47,54],[-47,-48,55],[-56,46,54],[-54,56],[-46,56],[-46,-54,57],[-46,-55,58],[-56,59],[-57,60],[-58,61],[-50,62],[-49,62],[-49,-50,63],[-52,64],[-52,-53,65],[-64,66],[-65,67],[-51,66],[-51,-64,67],[-66,68],[-67,69],[-62,-66,69],[-62,-67,70],[-63,69],[-70,71],[-59,-69,71],[-60,-68,71],[-61,71],[-71],[2,5,6,8,9,10,18,19,20,29,30,31,32,33,34,35,36,42,43],[1,7,11,12,14,15,17,20,21,22,23,25,27,28,36,37,38,40,42,44,45],[4,10,13,15,16,20,25,26,27,31,36,38,39,40,41,42,44,45]],\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":52,\"b\":33},{\"tag\":\"incompatible\",\"a\":52,\"b\":36},{\"tag\":\"incompatible\",\"a\":52,\"b\":37},{\"tag\":\"incompatible\",\"a\":60,\"b\":52},{\"tag\":\"incompatible\",\"a\":61,\"b\":52},{\"tag\":\"incompatible\",\"a\":84,\"b\":52},{\"tag\":\"mate\",\"ridge\":289,\"a\":70,\"owners\":[15,35,43,53,59,66,67]},{\"tag\":\"mate\",\"ridge\":296,\"a\":15,\"owners\":[77,89,90,96,98]},{\"tag\":\"mate\",\"ridge\":296,\"a\":43,\"owners\":[96,98]},{\"tag\":\"mate\",\"ridge\":296,\"a\":59,\"owners\":[89,90,98]},{\"tag\":\"mate\",\"ridge\":296,\"a\":66,\"owners\":[77,90,96,98]},{\"tag\":\"mate\",\"ridge\":296,\"a\":67,\"owners\":[77,89,90,96]},{\"tag\":\"mate\",\"ridge\":518,\"a\":83,\"owners\":[36,37,38,78,79,80,86]},{\"tag\":\"mate\",\"ridge\":518,\"a\":85,\"owners\":[20,33,37,38,79,80,84]},{\"tag\":\"three\",\"ridge\":530,\"vertices\":[20,22,52]},{\"tag\":\"mate\",\"ridge\":532,\"a\":26,\"owners\":[20,33,61,83,84]},{\"tag\":\"mate\",\"ridge\":656,\"a\":71,\"owners\":[22,84]},{\"tag\":\"mate\",\"ridge\":770,\"a\":23,\"owners\":[38,52,54,80,86,90,93]},{\"tag\":\"mate\",\"ridge\":770,\"a\":91,\"owners\":[38,52,54,86,93]},{\"tag\":\"mate\",\"ridge\":896,\"a\":55,\"owners\":[98,99]},{\"tag\":\"mate\",\"ridge\":896,\"a\":94,\"owners\":[72,98]},{\"tag\":\"mate\",\"ridge\":548,\"a\":82,\"owners\":[62,96]},{\"tag\":\"mate\",\"ridge\":548,\"a\":97,\"owners\":[36,62,78,86,96]},{\"tag\":\"mate\",\"ridge\":294,\"a\":86,\"owners\":[35,77]},{\"tag\":\"mate\",\"ridge\":773,\"a\":38,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":773,\"a\":62,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":306,\"a\":47,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":306,\"a\":93,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":785,\"a\":52,\"owners\":[70,71]},{\"tag\":\"mate\",\"ridge\":785,\"a\":70,\"owners\":[52,71]},{\"tag\":\"mate\",\"ridge\":785,\"a\":71,\"owners\":[52,70]},{\"tag\":\"mate\",\"ridge\":354,\"a\":89,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":800,\"a\":54,\"owners\":[96,98,99]},{\"tag\":\"mate\",\"ridge\":800,\"a\":62,\"owners\":[90,93,98,99]},{\"tag\":\"mate\",\"ridge\":800,\"a\":70,\"owners\":[86,90,96,98]},{\"tag\":\"mate\",\"ridge\":800,\"a\":72,\"owners\":[86,90,93,96]},{\"tag\":\"mate\",\"ridge\":800,\"a\":86,\"owners\":[70,72,98,99]},{\"tag\":\"mate\",\"ridge\":800,\"a\":90,\"owners\":[62,70,72,99]},{\"tag\":\"mate\",\"ridge\":800,\"a\":93,\"owners\":[62,72,96,98]},{\"tag\":\"mate\",\"ridge\":800,\"a\":96,\"owners\":[54,70,72,93,99]},{\"tag\":\"mate\",\"ridge\":800,\"a\":99,\"owners\":[54,62,86,90,96]},{\"tag\":\"mate\",\"ridge\":432,\"a\":68,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":432,\"a\":99,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":673,\"a\":69,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":673,\"a\":72,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":554,\"a\":78,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":554,\"a\":90,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":652,\"a\":79,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":780,\"a\":80,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":780,\"a\":96,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":680,\"a\":98,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[68,69,98],\"full_literals\":[-46,23,24,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":68,\"full_literals\":[-23,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-24,46]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[78,79,80],\"full_literals\":[-47,29,30,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":78,\"full_literals\":[-29,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":80,\"full_literals\":[-31,47]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[47,52,99],\"full_literals\":[-48,12,13,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":47,\"full_literals\":[-12,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":52,\"full_literals\":[-13,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":99,\"full_literals\":[-45,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":35,\"full_literals\":[-7,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":38,\"full_literals\":[-10,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":96,\"full_literals\":[-42,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":53,\"full_literals\":[-14,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":77,\"full_literals\":[-28,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":90,\"full_literals\":[-38,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":93,\"full_literals\":[-40,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":62,\"full_literals\":[-20,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":70,\"full_literals\":[-25,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":72,\"full_literals\":[-27,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":54,\"full_literals\":[-15,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":86,\"full_literals\":[-36,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":71,\"full_literals\":[-26,53]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-48,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,46,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-54,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-46,-55,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-57,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-58,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-50,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-53,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-64,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-62,-66,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-62,-67,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-59,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-68,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[20,26,33,36,37,38,60,61,62,78,79,80,82,83,84,85,86,96,97]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[15,35,43,47,53,54,59,62,66,67,68,70,72,77,86,89,90,93,96,98,99]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[23,38,52,54,55,62,70,71,72,80,86,90,91,93,94,96,98,99]}]}"
  "109 -46 23 24 0 51 52 0\n110 -47 29 31 0 48 55 0\n111 -70 0 105 101 0\n112 -61 0 105 104 0\n113 -58 0 112 86 0\n114 2 5 6 8 9 10 18 19 20 29 31 32 33 34 35 36 42 43 0 48 106 0\n115 1 7 11 12 14 15 17 20 21 22 23 25 27 28 36 37 38 40 42 45 0 51 107 0\n116 4 10 13 15 16 20 25 26 27 31 36 38 39 40 41 42 45 0 51 108 0\n117 1 14 11 12 45 15 7 20 21 22 23 17 27 28 36 37 38 40 42 0 115 7 0\n118 62 56 0 51 80 76 61 77 57 50 33 9 59 28 56 47 34 81 54 45 53 87 88 65 66 62 32 8 11 12 24 10 117 0\n119 36 56 0 51 80 76 61 59 28 77 56 47 34 25 57 50 33 81 54 45 21 20 60 35 18 19 31 116 0\n120 56 0 111 51 80 81 76 54 60 61 45 118 99 93 119 37 73 30 91 74 0\n121 59 0 120 84 0\n122 -69 0 121 105 102 0\n123 -67 0 122 97 0\n124 -63 0 122 100 0\n125 -36 45 0 123 51 73 90 95 70 71 37 0\n126 2 43 6 8 9 10 18 19 20 29 31 32 33 34 35 36 42 0 114 16 0\n127 38 40 42 45 0 51 120 48 27 49 125 42 34 46 25 22 110 35 36 44 109 79 75 58 1 2 3 4 5 6 29 23 13 17 15 14 126 0\n128 -38 45 0 124 122 67 87 89 98 63 94 26 70 71 38 0\n129 38 42 45 0 51 122 124 127 68 87 89 98 63 94 26 71 39 0\n130 38 45 0 122 124 129 64 88 89 98 68 92 94 90 70 71 72 40 0\n131 45 0 128 130 0\n132 23 0 131 43 0\n133 48 0 131 61 0\n134 46 0 132 53 0\n135 54 0 133 76 0\n136 57 0 134 135 82 0\n137 -55 0 134 113 83 0\n138 60 0 136 85 0\n139 -47 0 137 133 78 0\n140 -68 0 138 105 103 0\n141 -29 0 139 56 0\n142 -31 0 139 57 0\n143 -66 0 140 96 0\n144 -38 0 141 47 0\n145 -42 0 142 50 0\n146 -64 0 143 92 0\n147 -51 0 143 94 0\n148 -52 0 146 90 0\n149 -20 0 147 69 0\n150 -15 0 148 72 0\n151 -36 0 148 73 0\n152 0 150 149 131 151 144 145 41 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ec338ad3a2aca72ca96a8e87aa99a6a58d68d8b61d98e4b89e1783ee47319c7295a719666394e479a54d58d4756352d1b49d0f72398d63a4e5334e331cf0b62d4b8ad2b1ae1b26c5b0ee8761cc789d2719e1725c570dd0f23c2f07c781d06c1703ce0b224a86a1984e0bb81a4459254551341dc0e8360d0b12c8711c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6da6d269b6db4d34936db6da49a6d249b4db69269369a49b4d2692449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 40), (facetIndex 55), (facetIndex 67), (facetIndex 77)]))
 (.leaf ([(facetIndex 50), (facetIndex 58), (facetIndex 93), (facetIndex 96)])))
 (.branch 3
 (.leaf ([(facetIndex 59), (facetIndex 60), (facetIndex 64), (facetIndex 66)]))
 (.leaf ([(facetIndex 78), (facetIndex 81), (facetIndex 90), (facetIndex 92)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 39), (facetIndex 49)]))
 (.leaf ([(facetIndex 28), (facetIndex 35), (facetIndex 45), (facetIndex 46), (facetIndex 61), (facetIndex 68)])))
 (.branch 7
 (.leaf ([(facetIndex 27), (facetIndex 32), (facetIndex 33), (facetIndex 42), (facetIndex 79), (facetIndex 83)]))
 (.branch 8
 (.leaf ([(facetIndex 38)]))
 (.leaf ([(facetIndex 48)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "1001303000000603063000000000502020052210000000148055006004700506604456z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 63), (facetIndex 71)]))
 (.leaf ([(facetIndex 36), (facetIndex 82), (facetIndex 88)])))
 (.branch 3
 (.leaf ([(facetIndex 69), (facetIndex 72), (facetIndex 99)]))
 (.branch 4
 (.leaf ([(facetIndex 34), (facetIndex 84), (facetIndex 89)]))
 (.leaf ([(facetIndex 85), (facetIndex 95), (facetIndex 97)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 44), (facetIndex 47), (facetIndex 98)]))
 (.leaf ([(facetIndex 31), (facetIndex 53), (facetIndex 54), (facetIndex 80), (facetIndex 87), (facetIndex 91)])))
 (.branch 8
 (.leaf ([(facetIndex 37), (facetIndex 41), (facetIndex 56), (facetIndex 57), (facetIndex 62), (facetIndex 70), (facetIndex 76)]))
 (.branch 9
 (.leaf ([(facetIndex 51), (facetIndex 65), (facetIndex 73), (facetIndex 74), (facetIndex 75)]))
 (.leaf ([(facetIndex 52), (facetIndex 86), (facetIndex 94)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "254049006031694301060007888207200080070000770669800050050070007103006z1f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7, 8]
def grouped2_0008 : List Nat := [7]
def grouped2_0009 : List Nat := [7, 8]
def grouped2_0010 : List Nat := [8]
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record002" 83

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record002" "{\"ridges\":[[19,296],[20,800],[36,293],[37,549],[38,134],[44,538],[46,265],[46,296],[47,553],[48,265],[57,609],[58,800],[62,293],[69,305],[70,553],[71,408],[73,353],[74,553],[76,305],[76,560],[80,154],[81,296],[85,560],[87,534],[88,420],[89,546],[92,296],[93,800],[94,594],[95,560],[96,800],[97,560],[98,560],[98,792],[99,432]],\"owners\":[[38,134,[80,82,84,87,88,89],[2,29,33,39,40,86]],[46,265,[63,71,72],[4,30,48,49,50,62,69,73,74]],[48,265,[62,63,69,71,72,74],[4,30,46,49,50,73]],[19,296,[62,69,73,74,98],[46,81,92,93]],[46,296,[98],[19,62,69,73,74,81,92,93]],[81,296,[69,73,74,98],[19,46,62,92,93]],[92,296,[62,69,74,98],[19,46,73,81,93]],[89,546,[20,47,52,57,58,91,93,94],[37,85,95,96]],[20,800,[74,76,98,99],[58,93,96]],[58,800,[98,99],[20,74,76,93,96]],[93,800,[76,99],[20,58,74,96,98]],[96,800,[74,76,98],[20,58,93,99]],[87,534,[34,85],[]],[36,293,[62],[]],[62,293,[36],[]],[37,549,[65],[]],[80,154,[43],[]],[44,538,[91],[]],[47,553,[70,74],[]],[70,553,[47,74],[]],[74,553,[47,70],[]],[76,560,[85,91,94,95,97],[52,65,70,75,98,99]],[85,560,[70,75,76,98,99],[52,65,91,94,95,97]],[95,560,[65,70,75,76,98],[52,85,91,94,97,99]],[97,560,[52,70,75,76,91,94,98],[65,85,95,99]],[98,560,[52,65,75,85,94,95,97],[70,76,91,99]],[94,594,[54],[]],[73,353,[56],[]],[57,609,[75],[]],[69,305,[76],[]],[76,305,[69],[]],[71,408,[],[]],[98,792,[72],[]],[88,420,[],[]],[99,432,[],[]]],\"edges\":[[37,[19,20,36,46,56,58,62,69,73,74,76,81,88,92,93,96,98,99]],[38,[20,37,47,52,57,58,65,70,74,75,76,85,89,91,93,94,95,96,97,98,99]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-3],[-14,-11],[-30,-5],[-30,-20],[-30,-24],[-8,33,35,36,38,39,40],[-12,22,27,28],[-14,21,22,25,27,28,30],[-1,21,25,29,30,48],[-12,48],[-34,25,29,30,48],[-42,21,25,30,48],[-40,2,13,15,18,19,41,43,44],[-2,30,32,48,49],[-19,48,49],[-43,32,49],[-46,30,32,48],[-38,4,37],[-6,21],[-21,6],[-7,23],[-33,9],[-10,41],[-13,26,30],[-26,13,30],[-30,13,26],[-32,37,41,44,45,47],[-37,26,31,32,48,49],[-45,23,26,31,32,48],[-47,15,26,31,32,41,44,48],[-48,15,23,31,37,44,45,47],[-44,16],[-29,17],[-18,31],[-25,32],[-32,25],[-27],[-48,28],[-39],[-49],[-50,3,5,11,12,20,24],[-51,8],[-52,14],[-53,50],[-54,51,52],[-55,51],[-56,54],[-57,55],[-58,53,57],[-58,56],[-59,58],[59],[-9,60],[-22,60],[-6,61],[-35,61],[-25,62],[-28,62],[-4,63],[-36,63],[-40,63],[-37,64],[-45,64],[-47,64],[-65,10,13,48],[-13,65],[-48,65],[-16,66],[-41,66],[-17,67],[-21,67],[-26,67],[-32,67],[-23,68],[-30,68],[-31,68],[-15,69],[-44,69],[-61,70],[-60,70],[-64,71],[-63,71],[-71,72],[-62,72],[-62,-71,73],[-72,74],[-73,75],[-70,74],[-66,76],[-65,76],[-65,-66,77],[-69,78],[-68,78],[-78,79],[-67,79],[-67,-78,80],[-79,81],[-80,82],[-76,81],[-76,-79,82],[-77,82],[-74,-82,83],[-75,-81,83],[-83],[1,2,6,12,17,19,21,25,29,30,32,34,39,42,43,46,48,49],[2,7,13,15,18,19,23,26,30,31,32,37,40,41,43,44,45,46,47,48,49]],\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":48,\"b\":28},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":74,\"b\":35},{\"tag\":\"incompatible\",\"a\":74,\"b\":61},{\"tag\":\"incompatible\",\"a\":74,\"b\":68},{\"tag\":\"mate\",\"ridge\":134,\"a\":38,\"owners\":[80,82,84,87,88,89]},{\"tag\":\"mate\",\"ridge\":265,\"a\":46,\"owners\":[63,71,72]},{\"tag\":\"mate\",\"ridge\":265,\"a\":48,\"owners\":[62,63,69,71,72,74]},{\"tag\":\"mate\",\"ridge\":296,\"a\":19,\"owners\":[62,69,73,74,98]},{\"tag\":\"mate\",\"ridge\":296,\"a\":46,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":296,\"a\":81,\"owners\":[69,73,74,98]},{\"tag\":\"mate\",\"ridge\":296,\"a\":92,\"owners\":[62,69,74,98]},{\"tag\":\"mate\",\"ridge\":546,\"a\":89,\"owners\":[20,47,52,57,58,91,93,94]},{\"tag\":\"mate\",\"ridge\":800,\"a\":20,\"owners\":[74,76,98,99]},{\"tag\":\"mate\",\"ridge\":800,\"a\":58,\"owners\":[98,99]},{\"tag\":\"mate\",\"ridge\":800,\"a\":93,\"owners\":[76,99]},{\"tag\":\"mate\",\"ridge\":800,\"a\":96,\"owners\":[74,76,98]},{\"tag\":\"mate\",\"ridge\":534,\"a\":87,\"owners\":[34,85]},{\"tag\":\"mate\",\"ridge\":293,\"a\":36,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":293,\"a\":62,\"owners\":[36]},{\"tag\":\"mate\",\"ridge\":549,\"a\":37,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":154,\"a\":80,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":538,\"a\":44,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":553,\"a\":47,\"owners\":[70,74]},{\"tag\":\"mate\",\"ridge\":553,\"a\":70,\"owners\":[47,74]},{\"tag\":\"mate\",\"ridge\":553,\"a\":74,\"owners\":[47,70]},{\"tag\":\"mate\",\"ridge\":560,\"a\":76,\"owners\":[85,91,94,95,97]},{\"tag\":\"mate\",\"ridge\":560,\"a\":85,\"owners\":[70,75,76,98,99]},{\"tag\":\"mate\",\"ridge\":560,\"a\":95,\"owners\":[65,70,75,76,98]},{\"tag\":\"mate\",\"ridge\":560,\"a\":97,\"owners\":[52,70,75,76,91,94,98]},{\"tag\":\"mate\",\"ridge\":560,\"a\":98,\"owners\":[52,65,75,85,94,95,97]},{\"tag\":\"mate\",\"ridge\":594,\"a\":94,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":353,\"a\":73,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":609,\"a\":57,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":305,\"a\":69,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":305,\"a\":76,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":408,\"a\":71,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":792,\"a\":98,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":420,\"a\":88,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":432,\"a\":99,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[28,35,45,46,61,68],\"full_literals\":[-50,3,5,11,12,20,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[38],\"full_literals\":[-51,8]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[48],\"full_literals\":[-52,14]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,51,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-58,53,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":43,\"full_literals\":[-9,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-22,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":36,\"full_literals\":[-6,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-35,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-25,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":72,\"full_literals\":[-28,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":34,\"full_literals\":[-4,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":84,\"full_literals\":[-36,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-40,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":85,\"full_literals\":[-37,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":95,\"full_literals\":[-45,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":97,\"full_literals\":[-47,64]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[44,47,98],\"full_literals\":[-65,10,13,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":47,\"full_literals\":[-13,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":98,\"full_literals\":[-48,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":54,\"full_literals\":[-16,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":91,\"full_literals\":[-41,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":56,\"full_literals\":[-17,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":62,\"full_literals\":[-21,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":70,\"full_literals\":[-26,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":76,\"full_literals\":[-32,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":65,\"full_literals\":[-23,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":74,\"full_literals\":[-30,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":75,\"full_literals\":[-31,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":52,\"full_literals\":[-15,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":94,\"full_literals\":[-44,69]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-62,-71,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-73,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-66,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-67,-78,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-80,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-79,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-77,false,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-74,-82,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-75,-81,83],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[19,20,36,46,56,58,62,69,73,74,76,81,88,92,93,96,98,99]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[20,37,47,52,57,58,65,70,74,75,76,85,89,91,93,94,95,96,97,98,99]}]}"
  "107 58 0 52 51 0\n108 56 0 107 50 0\n109 54 0 108 47 0\n110 1 2 6 12 17 19 21 25 29 30 32 34 42 43 46 48 0 39 40 105 0\n111 2 7 13 15 18 19 23 26 30 31 32 37 40 41 43 44 45 46 47 48 0 40 106 0\n112 74 0 39 109 37 107 86 88 83 84 79 80 81 82 57 58 55 56 53 54 62 59 60 61 20 22 7 18 6 42 45 46 43 48 1 2 8 49 3 4 5 44 41 0\n113 -82 0 112 104 102 0\n114 -80 0 113 98 0\n115 -77 0 113 101 0\n116 67 65 0 40 67 15 10 66 70 71 72 73 33 19 26 16 35 11 12 14 17 9 110 0\n117 2 32 7 13 18 19 23 15 30 31 48 26 37 41 43 44 45 46 47 0 111 13 0\n118 -32 66 73 0 68 32 69 36 57 85 81 62 63 64 27 0\n119 32 47 7 13 18 19 23 15 30 31 48 26 37 41 43 44 45 2 0 117 17 0\n120 76 73 0 114 40 89 90 68 69 66 67 32 15 116 96 92 93 77 74 75 76 21 25 34 118 16 14 28 29 30 119 0\n121 73 0 113 115 120 100 94 95 92 93 72 116 77 78 74 75 76 24 91 69 23 65 38 58 85 81 62 63 64 31 0\n122 75 0 121 87 0\n123 -81 0 122 104 103 0\n124 -79 0 123 97 0\n125 -76 0 123 99 0\n126 -67 0 124 95 0\n127 -65 0 125 90 0\n128 0 126 127 116 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "7ce8b929cb2a5ab1a66a3a1eaa669a9635a361d98e4b89e0fba1e4671ca569c65998e479a95a5a54d58d4756352d2743de0f23a8da398d63c4e9364e5334e331cf0b62d4b8ad2b1ae1b46c9b16c3ba1d8731e2749ca719e1725c570dd0f23c4f0bc1f1b05ce0b22a492a1a85a198961584e0b81ee0721a45291a459194951544d0b41d"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "249a4db4da4d34924d26da6d269a4926db69b6db6da4db4db6db4d26da489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 58), (facetIndex 65), (facetIndex 83), (facetIndex 102)]))
 (.leaf ([(facetIndex 64), (facetIndex 84), (facetIndex 103)])))
 (.branch 3
 (.leaf ([(facetIndex 48), (facetIndex 68), (facetIndex 80), (facetIndex 81)]))
 (.leaf ([(facetIndex 33), (facetIndex 86), (facetIndex 91), (facetIndex 92)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 67), (facetIndex 72), (facetIndex 73)]))
 (.leaf ([(facetIndex 87), (facetIndex 99), (facetIndex 100)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 66), (facetIndex 70), (facetIndex 76), (facetIndex 85), (facetIndex 89), (facetIndex 95), (facetIndex 104)]))
 (.leaf ([(facetIndex 26), (facetIndex 27), (facetIndex 32), (facetIndex 35), (facetIndex 43), (facetIndex 47)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6205a00c03630af1012006024182981000000000002e00e00000e1f006fcz13;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 69), (facetIndex 74)]))
 (.leaf ([(facetIndex 36), (facetIndex 75), (facetIndex 93)])))
 (.branch 3
 (.leaf ([(facetIndex 45), (facetIndex 78), (facetIndex 79)]))
 (.branch 4
 (.leaf ([(facetIndex 31), (facetIndex 71), (facetIndex 77), (facetIndex 82)]))
 (.leaf ([(facetIndex 29), (facetIndex 88), (facetIndex 97)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 34), (facetIndex 90), (facetIndex 94)]))
 (.leaf ([(facetIndex 46), (facetIndex 96), (facetIndex 98)])))
 (.branch 8
 (.leaf ([(facetIndex 42), (facetIndex 56), (facetIndex 101)]))
 (.branch 9
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 39), (facetIndex 44), (facetIndex 49), (facetIndex 50), (facetIndex 53), (facetIndex 57), (facetIndex 61), (facetIndex 62)]))
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 51), (facetIndex 52), (facetIndex 54), (facetIndex 55), (facetIndex 59), (facetIndex 60), (facetIndex 63)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "7006460510050400000300223010003000000098899087998998800628079988810500304z1d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
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
def grouped3_0017 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0019 : List Nat := [1]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [2, 3, 4]
def grouped3_0022 : List Nat := [3]
def grouped3_0023 : List Nat := [3, 4]
def grouped3_0024 : List Nat := [4]
def grouped3_0025 : List Nat := [5]
def grouped3_0026 : List Nat := [5, 6]
def grouped3_0027 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0028 : List Nat := [6]
def grouped3_0029 : List Nat := [7]
def grouped3_0030 : List Nat := [7, 8, 9]
def grouped3_0031 : List Nat := [8]
def grouped3_0032 : List Nat := [8, 9]
def grouped3_0033 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0032\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record003" 97

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record003" "{\"ridges\":[[35,38],[43,81],[43,82],[59,275],[64,290],[67,133],[71,564],[72,81],[73,133],[73,529],[74,420],[75,676],[81,545],[82,81],[82,624],[83,529],[86,134],[91,82],[91,134],[92,134],[93,290],[94,676],[99,290],[100,546],[101,82]],\"owners\":[[67,133,[36,39,40,41,74,75],[4,29,33,69,72,73]],[73,133,[29,36,39,40,69,74],[4,33,41,67,72,75]],[73,529,[46,54,56,59,77,79,82],[9,34,58,71,83]],[83,529,[34,46,54,56,71,77,82],[9,58,59,73,79]],[81,545,[38,54,61,63,71,75,82],[10,49,64,77,84]],[35,38,[13,85,87,90,93,94],[17,27,31,36,37,38,89]],[86,134,[36,39,40,41,93,94],[16,29,33,88,91,92]],[91,134,[29,36,40,41,88,93,94],[16,33,39,86,92]],[92,134,[29,36,39,40,88,93],[16,33,41,86,91,94]],[100,546,[38,54,61,63,90,94,101],[22,49,64,96,103]],[59,275,[45,57],[]],[71,564,[90],[]],[74,420,[93],[]],[75,676,[94],[]],[94,676,[75],[]],[82,624,[101],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-5,-3],[-7,-2],[-7,-6],[-9,-5],[-9,-7],[-10,-2],[-10,-3],[-10,-6],[-10,-9],[-12,-2],[-12,-6],[-12,-9],[-13,-2],[-13,-3],[-13,-6],[-13,-9],[-14,-2],[-14,-3],[-14,-6],[-14,-9],[-15,-4],[-15,-5],[-15,-7],[-15,-8],[-15,-10],[-15,-11],[-15,-12],[-15,-13],[-15,-14],[-17,-15],[-18,-5],[-18,-10],[-18,-13],[-18,-14],[-19,-3],[-19,-15],[-19,-18],[-20,-15],[-21,-15],[-23,-9],[-23,-15],[-25,-15],[-26,-15],[-27,-9],[-27,-15],[-27,-23],[-28,-9],[-28,-15],[-28,-27],[-31,-3],[-31,-18],[-35,-2],[-35,-6],[-35,-29],[-35,-33],[-36,-22],[-39,-15],[-42,-3],[-42,-18],[-45,-38],[-46,-45],[-49,-3],[-49,-18],[-50,-31],[-50,-47],[-50,-49],[-51,-40],[-53,-2],[-53,-6],[-53,-35],[-53,-52],[-54,-34],[-54,-36],[-54,-52],[-55,-46],[-55,-49],[-56,-46],[-57,-15],[-58,-1],[-58,-3],[-58,-18],[-58,-42],[-59,-43],[-59,-55],[-61,-54],[-61,-56],[-62,-55],[-62,-56],[-62,-59],[-63,-15],[-15,-35,-44],[-30,10,12,13,14,37,38],[-36,5,10,12,13,32,37],[-36,17,20,21,24,40,41,44],[-45,8,17,20,21,34,40,44],[-43,11,20,25,26,34,38,44],[-9,1,47,49,52,55,56],[-15,-53,-60],[-48,10,12,13,14,55,56],[-53,5,10,13,14,50,55,56],[-54,5,10,12,13,50,55],[-27,-55,-58],[-59,11,20,25,26,52,56,60],[-24,16,22],[-34,52],[-37,55],[-38,56],[-56,38],[-44,60],[-64,23,28,45,61],[-65,27,46,62],[-66,19,31,42,43],[-67,7,48,53,54],[-68,30,35,36],[-69,49,58,59],[-70,4,29,33,39,47,51,57,63],[-71,2,3,6,9,15,18],[-72,64],[-72,65],[-73,66],[-73,67],[-74,72],[-74,73],[-75,68],[-75,69],[-76,70],[-76,71],[-77,75],[-77,76],[-78,74],[-78,77],[78],[-32,79],[-16,80],[-41,80],[-40,81],[-44,81],[-50,82],[-17,83],[-21,84],[-20,85],[-79,86],[-82,87],[-81,-82,88],[-87,89],[-88,90],[-80,-87,90],[-86,-89,91],[-86,-90,92],[-83,93],[-85,94],[-94,95],[-84,95],[-95,96],[-93,96],[-91,-96,97],[-92,97],[-97]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":29,\"b\":27},{\"tag\":\"incompatible\",\"a\":33,\"b\":26},{\"tag\":\"incompatible\",\"a\":33,\"b\":32},{\"tag\":\"incompatible\",\"a\":35,\"b\":29},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":36,\"b\":26},{\"tag\":\"incompatible\",\"a\":36,\"b\":27},{\"tag\":\"incompatible\",\"a\":36,\"b\":32},{\"tag\":\"incompatible\",\"a\":36,\"b\":35},{\"tag\":\"incompatible\",\"a\":39,\"b\":26},{\"tag\":\"incompatible\",\"a\":39,\"b\":32},{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":26},{\"tag\":\"incompatible\",\"a\":40,\"b\":27},{\"tag\":\"incompatible\",\"a\":40,\"b\":32},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":41,\"b\":26},{\"tag\":\"incompatible\",\"a\":41,\"b\":27},{\"tag\":\"incompatible\",\"a\":41,\"b\":32},{\"tag\":\"incompatible\",\"a\":41,\"b\":35},{\"tag\":\"incompatible\",\"a\":43,\"b\":28},{\"tag\":\"incompatible\",\"a\":43,\"b\":29},{\"tag\":\"incompatible\",\"a\":43,\"b\":33},{\"tag\":\"incompatible\",\"a\":43,\"b\":34},{\"tag\":\"incompatible\",\"a\":43,\"b\":36},{\"tag\":\"incompatible\",\"a\":43,\"b\":38},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":40},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":46,\"b\":43},{\"tag\":\"incompatible\",\"a\":47,\"b\":29},{\"tag\":\"incompatible\",\"a\":47,\"b\":36},{\"tag\":\"incompatible\",\"a\":47,\"b\":40},{\"tag\":\"incompatible\",\"a\":47,\"b\":41},{\"tag\":\"incompatible\",\"a\":48,\"b\":27},{\"tag\":\"incompatible\",\"a\":48,\"b\":43},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":54,\"b\":43},{\"tag\":\"incompatible\",\"a\":56,\"b\":43},{\"tag\":\"incompatible\",\"a\":58,\"b\":35},{\"tag\":\"incompatible\",\"a\":58,\"b\":43},{\"tag\":\"incompatible\",\"a\":61,\"b\":43},{\"tag\":\"incompatible\",\"a\":63,\"b\":43},{\"tag\":\"incompatible\",\"a\":64,\"b\":35},{\"tag\":\"incompatible\",\"a\":64,\"b\":43},{\"tag\":\"incompatible\",\"a\":64,\"b\":58},{\"tag\":\"incompatible\",\"a\":65,\"b\":35},{\"tag\":\"incompatible\",\"a\":65,\"b\":43},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":27},{\"tag\":\"incompatible\",\"a\":68,\"b\":47},{\"tag\":\"incompatible\",\"a\":72,\"b\":26},{\"tag\":\"incompatible\",\"a\":72,\"b\":32},{\"tag\":\"incompatible\",\"a\":72,\"b\":66},{\"tag\":\"incompatible\",\"a\":72,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":57},{\"tag\":\"incompatible\",\"a\":76,\"b\":43},{\"tag\":\"incompatible\",\"a\":80,\"b\":27},{\"tag\":\"incompatible\",\"a\":80,\"b\":47},{\"tag\":\"incompatible\",\"a\":83,\"b\":75},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"incompatible\",\"a\":87,\"b\":27},{\"tag\":\"incompatible\",\"a\":87,\"b\":47},{\"tag\":\"incompatible\",\"a\":88,\"b\":68},{\"tag\":\"incompatible\",\"a\":88,\"b\":85},{\"tag\":\"incompatible\",\"a\":88,\"b\":87},{\"tag\":\"incompatible\",\"a\":89,\"b\":77},{\"tag\":\"incompatible\",\"a\":91,\"b\":26},{\"tag\":\"incompatible\",\"a\":91,\"b\":32},{\"tag\":\"incompatible\",\"a\":91,\"b\":72},{\"tag\":\"incompatible\",\"a\":91,\"b\":90},{\"tag\":\"incompatible\",\"a\":92,\"b\":71},{\"tag\":\"incompatible\",\"a\":92,\"b\":73},{\"tag\":\"incompatible\",\"a\":92,\"b\":90},{\"tag\":\"incompatible\",\"a\":93,\"b\":84},{\"tag\":\"incompatible\",\"a\":93,\"b\":87},{\"tag\":\"incompatible\",\"a\":94,\"b\":84},{\"tag\":\"incompatible\",\"a\":95,\"b\":43},{\"tag\":\"incompatible\",\"a\":99,\"b\":13},{\"tag\":\"incompatible\",\"a\":99,\"b\":27},{\"tag\":\"incompatible\",\"a\":99,\"b\":47},{\"tag\":\"incompatible\",\"a\":99,\"b\":80},{\"tag\":\"incompatible\",\"a\":100,\"b\":81},{\"tag\":\"incompatible\",\"a\":100,\"b\":93},{\"tag\":\"incompatible\",\"a\":102,\"b\":92},{\"tag\":\"incompatible\",\"a\":102,\"b\":94},{\"tag\":\"incompatible\",\"a\":103,\"b\":93},{\"tag\":\"incompatible\",\"a\":103,\"b\":94},{\"tag\":\"incompatible\",\"a\":103,\"b\":100},{\"tag\":\"incompatible\",\"a\":104,\"b\":43},{\"tag\":\"three\",\"ridge\":81,\"vertices\":[43,72,82]},{\"tag\":\"mate\",\"ridge\":133,\"a\":67,\"owners\":[36,39,40,41,74,75]},{\"tag\":\"mate\",\"ridge\":133,\"a\":73,\"owners\":[29,36,39,40,69,74]},{\"tag\":\"mate\",\"ridge\":529,\"a\":73,\"owners\":[46,54,56,59,77,79,82]},{\"tag\":\"mate\",\"ridge\":529,\"a\":83,\"owners\":[34,46,54,56,71,77,82]},{\"tag\":\"mate\",\"ridge\":545,\"a\":81,\"owners\":[38,54,61,63,71,75,82]},{\"tag\":\"mate\",\"ridge\":38,\"a\":35,\"owners\":[13,85,87,90,93,94]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[43,91,101]},{\"tag\":\"mate\",\"ridge\":134,\"a\":86,\"owners\":[36,39,40,41,93,94]},{\"tag\":\"mate\",\"ridge\":134,\"a\":91,\"owners\":[29,36,40,41,88,93,94]},{\"tag\":\"mate\",\"ridge\":134,\"a\":92,\"owners\":[29,36,39,40,88,93]},{\"tag\":\"three\",\"ridge\":290,\"vertices\":[64,93,99]},{\"tag\":\"mate\",\"ridge\":546,\"a\":100,\"owners\":[38,54,61,63,90,94,101]},{\"tag\":\"mate\",\"ridge\":275,\"a\":59,\"owners\":[45,57]},{\"tag\":\"mate\",\"ridge\":564,\"a\":71,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":420,\"a\":74,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":676,\"a\":75,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":676,\"a\":94,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":624,\"a\":82,\"owners\":[101]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[58,65,83,102],\"full_literals\":[-64,23,28,45,61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[64,84,103],\"full_literals\":[-65,27,46,62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[48,68,80,81],\"full_literals\":[-66,19,31,42,43]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[33,86,91,92],\"full_literals\":[-67,7,48,53,54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[67,72,73],\"full_literals\":[-68,30,35,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[87,99,100],\"full_literals\":[-69,49,58,59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[28,66,70,76,85,89,95,104],\"full_literals\":[-70,4,29,33,39,47,51,57,63]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[26,27,32,35,43,47],\"full_literals\":[-71,2,3,6,9,15,18]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-72,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,66,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-74,72,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-74,false,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-75,68,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-75,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-76,70,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-76,false,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-77,75,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-77,false,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-78,74,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-78,false,77],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":69,\"full_literals\":[-32,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":45,\"full_literals\":[-16,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":79,\"full_literals\":[-41,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":77,\"full_literals\":[-40,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-44,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":88,\"full_literals\":[-50,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":46,\"full_literals\":[-17,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":56,\"full_literals\":[-21,84]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":54,\"full_literals\":[-20,85]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-79,false,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-82,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-81,-82,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-88,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-80,-87,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-86,-89,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-86,-90,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0033\",\"joined_name\":\"grouped3_0032\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-85,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-94,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-84,false,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-95,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-93,false,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-91,-96,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-92,false,97],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "159 74 0 132 130 0\n160 77 0 132 131 0\n161 72 0 159 122 0\n162 73 0 159 123 0\n163 75 0 160 128 0\n164 76 0 160 129 0\n165 64 0 161 118 0\n166 65 0 161 119 0\n167 66 0 162 120 0\n168 67 0 162 121 0\n169 68 0 163 124 0\n170 69 0 163 125 0\n171 70 0 164 126 0\n172 71 0 164 127 0\n173 -92 0 158 157 0\n174 -13 15 0 172 13 14 15 16 33 117 0\n175 -14 15 0 172 17 18 19 20 34 117 0\n176 55 56 53 -15 12 13 14 0 168 169 165 171 107 90 78 57 48 41 39 38 30 25 24 23 22 21 106 99 92 113 72 73 85 101 114 110 65 54 55 91 95 116 67 0\n177 -55 27 0 166 75 87 111 0\n178 -56 27 0 166 77 88 111 0\n179 -15 12 13 14 0 170 167 22 25 26 36 38 42 43 45 177 178 107 176 71 98 100 105 109 103 64 66 96 115 112 82 0\n180 5 10 55 56 -53 12 13 14 0 169 173 158 70 107 106 92 114 56 100 93 138 133 143 142 145 149 148 146 147 156 144 134 135 154 155 136 137 104 152 153 150 151 140 139 141 94 0\n181 -5 -53 15 0 172 69 68 1 4 31 117 0\n182 -10 -53 15 0 172 69 68 7 9 32 117 0\n183 -55 0 170 76 84 177 115 102 0\n184 -37 0 183 106 0\n185 -56 0 165 86 108 178 60 46 49 110 0\n186 -38 0 185 107 0\n187 -53 12 13 14 0 185 183 179 181 182 180 0\n188 -2 30 48 53 0 168 169 2 52 113 114 73 0\n189 -6 30 48 53 0 168 169 3 53 113 114 73 0\n190 -18 0 167 170 37 51 59 63 81 112 115 83 0\n191 -3 0 167 170 35 50 58 62 80 112 115 83 0\n192 10 12 13 14 0 186 184 190 191 172 168 165 185 183 166 170 187 179 99 92 188 189 117 4 5 40 44 47 113 74 85 101 110 65 66 61 97 111 79 89 115 0\n193 12 13 14 0 172 191 190 179 192 6 8 9 117 0\n194 -12 0 190 191 172 10 11 12 27 117 0\n195 -13 0 28 174 0\n196 14 0 195 194 193 0\n197 -15 0 196 29 0\n198 0 196 197 175 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record032
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "38ce4b8ac695a4e87ae1a96358b61db0ea398ee2719965598e5391e785a5655356352d475c368d6364d8b783c4e9354cd34ccb3c2e8b62d4b4ae1b46c5b0ef07a1d8731ca785c9715c3783d0f23f901b1921c86a1984e0bb81c469164471c2469a14658344d0b58318d1324c530cd0b12c2b21c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "d36da6db4db49b6d24db692692492493493493492692491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 61), (facetIndex 62), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 66), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 83), (facetIndex 88)]))
 (.leaf ([(facetIndex 43), (facetIndex 53), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 93)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 71), (facetIndex 72), (facetIndex 79)]))
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 40), (facetIndex 41), (facetIndex 42)])))
 (.branch 7
 (.leaf ([(facetIndex 47), (facetIndex 49), (facetIndex 50), (facetIndex 51)]))
 (.branch 8
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57)]))
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 78)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3000020000200048000014400001000003337777306660688035550777055z21;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 44), (facetIndex 52), (facetIndex 63)]))
 (.branch 2
 (.leaf ([(facetIndex 39), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 48), (facetIndex 74), (facetIndex 75), (facetIndex 76), (facetIndex 77)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 80), (facetIndex 81), (facetIndex 82)]))
 (.leaf ([(facetIndex 84), (facetIndex 85), (facetIndex 86)])))
 (.branch 6
 (.leaf ([(facetIndex 89), (facetIndex 90), (facetIndex 91)]))
 (.leaf ([(facetIndex 87), (facetIndex 92), (facetIndex 94)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "186b68d240db0124800492000000000000020000002z1d;"⟩
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
def grouped3_0018 : List Nat := [0, 1, 2]
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [1, 2]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [3]
def grouped3_0024 : List Nat := [3, 4]
def grouped3_0025 : List Nat := [3, 4, 5, 6]
def grouped3_0026 : List Nat := [4]
def grouped3_0027 : List Nat := [5]
def grouped3_0028 : List Nat := [5, 6]
def grouped3_0029 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record032" "{\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record032" 78

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record032" "{\"ridges\":[[43,644],[53,776],[58,529],[59,529],[68,564],[70,596],[71,644],[72,644],[75,568],[77,600],[79,776],[81,650],[82,774],[93,656],[93,784]],\"owners\":[[43,644,[94],[17,64,71,72,81,86,87]],[71,644,[81,87,94],[17,43,64,72,86]],[72,644,[81,86],[17,43,64,71,87,94]],[53,776,[94],[19,65,78,79,82,91,92]],[79,776,[82,91],[19,53,65,78,92,94]],[58,529,[23,68,70,75,77,78],[22,39,48,59,71]],[59,529,[22,68,70,71,75,77],[23,39,48,58,78]],[93,656,[22,71],[32,58,86]],[93,784,[23,78],[32,59,91]],[82,774,[44,87],[]],[81,650,[52,92],[]],[68,564,[],[]],[70,596,[],[]],[75,568,[],[]],[77,600,[],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record032" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record032\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-14,-9],[-14,-10],[-15,-9],[-15,-10],[-16,-9],[-16,-10],[-17,-9],[-17,-10],[-22,-6],[-23,-22],[-25,-22],[-27,-12],[-27,-22],[-28,-1],[-28,-8],[-28,-12],[-28,-18],[-28,-20],[-28,-21],[-28,-27],[-29,-9],[-29,-10],[-34,-28],[-34,-29],[-35,-2],[-35,-8],[-35,-19],[-35,-20],[-35,-34],[-38,-3],[-38,-4],[-38,-5],[-38,-22],[-38,-27],[-39,-22],[-40,-22],[-41,-22],[-41,-38],[-42,-18],[-42,-19],[-42,-20],[-43,-9],[-43,-10],[-43,-11],[-43,-29],[-43,-30],[-43,-32],[-43,-34],[-44,-43],[-45,-43],[-46,-29],[-46,-43],[-47,-18],[-47,-19],[-47,-20],[-48,-42],[-48,-47],[-49,-28],[-49,-35],[-7,49],[-27,36,42,49],[-28,36,41],[-13,49],[-35,37,46],[-18,2,24,26,31,33,34],[-19,1,24,26,27,31,33],[-48,1,27],[-48,2,34],[-37,8,42],[-36,12,47],[-24],[-26],[-31],[-33],[-50,22,29],[-51,38,43],[-52,7,13,18,19,20,48],[-53,27,28,35],[-54,3,4,5,14,15,16,17],[-55,9,10,34],[-56,50],[-57,51,52],[-58,51],[-58,52],[-59,56,58],[-60,56],[-59,57],[-60,58],[-61,53],[-62,54],[-62,55],[-63,62],[-64,61,63],[-65,61],[-65,63],[-66,59],[-66,60,65],[-66,64],[66],[-67,8,12,21],[-68,6,23,24,25,26],[-69,11,30,31,32,33],[-70,39,40,41],[-71,44,45,46],[-72,42,47,49],[-42,72],[-47,72],[-49,72],[-73,68,69],[-74,67,73],[-75,70],[-76,71,72],[-77,75,76],[-78,74,77],[78]],\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":54,\"b\":45},{\"tag\":\"incompatible\",\"a\":54,\"b\":46},{\"tag\":\"incompatible\",\"a\":55,\"b\":45},{\"tag\":\"incompatible\",\"a\":55,\"b\":46},{\"tag\":\"incompatible\",\"a\":56,\"b\":45},{\"tag\":\"incompatible\",\"a\":56,\"b\":46},{\"tag\":\"incompatible\",\"a\":57,\"b\":45},{\"tag\":\"incompatible\",\"a\":57,\"b\":46},{\"tag\":\"incompatible\",\"a\":66,\"b\":39},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":52},{\"tag\":\"incompatible\",\"a\":71,\"b\":66},{\"tag\":\"incompatible\",\"a\":72,\"b\":22},{\"tag\":\"incompatible\",\"a\":72,\"b\":44},{\"tag\":\"incompatible\",\"a\":72,\"b\":52},{\"tag\":\"incompatible\",\"a\":72,\"b\":58},{\"tag\":\"incompatible\",\"a\":72,\"b\":60},{\"tag\":\"incompatible\",\"a\":72,\"b\":63},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":45},{\"tag\":\"incompatible\",\"a\":73,\"b\":46},{\"tag\":\"incompatible\",\"a\":78,\"b\":72},{\"tag\":\"incompatible\",\"a\":78,\"b\":73},{\"tag\":\"incompatible\",\"a\":79,\"b\":23},{\"tag\":\"incompatible\",\"a\":79,\"b\":44},{\"tag\":\"incompatible\",\"a\":79,\"b\":59},{\"tag\":\"incompatible\",\"a\":79,\"b\":60},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":83,\"b\":36},{\"tag\":\"incompatible\",\"a\":83,\"b\":37},{\"tag\":\"incompatible\",\"a\":83,\"b\":38},{\"tag\":\"incompatible\",\"a\":83,\"b\":66},{\"tag\":\"incompatible\",\"a\":83,\"b\":71},{\"tag\":\"incompatible\",\"a\":84,\"b\":66},{\"tag\":\"incompatible\",\"a\":85,\"b\":66},{\"tag\":\"incompatible\",\"a\":86,\"b\":66},{\"tag\":\"incompatible\",\"a\":86,\"b\":83},{\"tag\":\"incompatible\",\"a\":87,\"b\":58},{\"tag\":\"incompatible\",\"a\":87,\"b\":59},{\"tag\":\"incompatible\",\"a\":87,\"b\":60},{\"tag\":\"incompatible\",\"a\":88,\"b\":45},{\"tag\":\"incompatible\",\"a\":88,\"b\":46},{\"tag\":\"incompatible\",\"a\":88,\"b\":48},{\"tag\":\"incompatible\",\"a\":88,\"b\":73},{\"tag\":\"incompatible\",\"a\":88,\"b\":74},{\"tag\":\"incompatible\",\"a\":88,\"b\":76},{\"tag\":\"incompatible\",\"a\":88,\"b\":78},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":90,\"b\":88},{\"tag\":\"incompatible\",\"a\":91,\"b\":73},{\"tag\":\"incompatible\",\"a\":91,\"b\":88},{\"tag\":\"incompatible\",\"a\":92,\"b\":58},{\"tag\":\"incompatible\",\"a\":92,\"b\":59},{\"tag\":\"incompatible\",\"a\":92,\"b\":60},{\"tag\":\"incompatible\",\"a\":93,\"b\":87},{\"tag\":\"incompatible\",\"a\":93,\"b\":92},{\"tag\":\"incompatible\",\"a\":94,\"b\":72},{\"tag\":\"incompatible\",\"a\":94,\"b\":79},{\"tag\":\"mate\",\"ridge\":644,\"a\":43,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":644,\"a\":71,\"owners\":[81,87,94]},{\"tag\":\"mate\",\"ridge\":644,\"a\":72,\"owners\":[81,86]},{\"tag\":\"mate\",\"ridge\":776,\"a\":53,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":776,\"a\":79,\"owners\":[82,91]},{\"tag\":\"mate\",\"ridge\":529,\"a\":58,\"owners\":[23,68,70,75,77,78]},{\"tag\":\"mate\",\"ridge\":529,\"a\":59,\"owners\":[22,68,70,71,75,77]},{\"tag\":\"mate\",\"ridge\":656,\"a\":93,\"owners\":[22,71]},{\"tag\":\"mate\",\"ridge\":784,\"a\":93,\"owners\":[23,78]},{\"tag\":\"mate\",\"ridge\":774,\"a\":82,\"owners\":[44,87]},{\"tag\":\"mate\",\"ridge\":650,\"a\":81,\"owners\":[52,92]},{\"tag\":\"mate\",\"ridge\":564,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":596,\"a\":70,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":568,\"a\":75,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":600,\"a\":77,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[66,73],\"full_literals\":[-50,22,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[83,88],\"full_literals\":[-51,38,43]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[43,53,58,59,60,93],\"full_literals\":[-52,7,13,18,19,20,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[71,72,79],\"full_literals\":[-53,27,28,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[36,37,38,54,55,56,57],\"full_literals\":[-54,3,4,5,14,15,16,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[45,46,78],\"full_literals\":[-55,9,10,34]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,51,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,56,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-60,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-64,61,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-65,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-66,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-66,60,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-66,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[44,52,63],\"full_literals\":[-67,8,12,21]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[39,67,68,69,70],\"full_literals\":[-68,6,23,24,25,26]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[48,74,75,76,77],\"full_literals\":[-69,11,30,31,32,33]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[84,85,86],\"full_literals\":[-70,39,40,41]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[89,90,91],\"full_literals\":[-71,44,45,46]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[87,92,94],\"full_literals\":[-72,42,47,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-42,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":92,\"full_literals\":[-47,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":94,\"full_literals\":[-49,72]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,67,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-75,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-76,71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,75,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-78,74,77],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "116 59 0 99 96 0\n117 64 0 99 98 0\n118 57 0 116 87 0\n119 -68 6 23 25 0 71 72 101 0\n120 -69 11 30 32 0 73 74 102 0\n121 -47 49 -52 0 63 60 53 54 55 57 77 0\n122 49 -52 -72 0 60 63 121 105 39 40 41 56 77 0\n123 -43 -55 0 42 43 48 80 0\n124 -9 -38 -54 0 32 31 30 1 3 5 7 79 0\n125 -10 -38 -54 0 32 31 30 2 4 6 8 79 0\n126 -38 -65 0 95 92 91 90 94 89 34 124 125 80 23 29 78 0\n127 -65 -72 0 118 116 94 95 89 92 91 123 126 76 82 83 122 85 58 59 81 78 13 75 21 22 24 80 0\n128 -55 -60 0 88 83 86 81 123 76 33 75 21 22 24 80 0\n129 -72 0 99 117 127 97 86 88 81 83 84 122 58 59 128 91 92 93 89 78 13 34 75 76 45 0\n130 -42 0 129 106 0\n131 -47 0 129 107 0\n132 -49 0 129 108 0\n133 -7 0 132 60 0\n134 -13 0 132 63 0\n135 -35 46 0 130 26 64 69 0\n136 -43 63 0 117 99 129 115 95 97 86 81 93 89 44 45 46 47 49 50 52 75 120 104 9 10 11 13 35 36 37 112 119 103 109 111 113 114 110 135 78 15 16 19 100 0\n137 63 0 117 99 131 95 93 97 89 86 88 81 83 136 76 33 34 38 75 51 135 78 16 62 70 0\n138 62 0 137 92 0\n139 55 0 138 91 0\n140 -43 0 139 123 0\n141 -60 0 139 128 0\n142 65 0 141 99 97 0\n143 61 0 142 94 0\n144 -38 0 142 126 0\n145 53 0 143 89 0\n146 -51 0 144 140 76 0\n147 52 0 146 118 82 0\n148 -28 0 74 73 72 71 134 147 133 14 17 18 20 66 67 77 0\n149 -35 0 74 73 72 71 134 147 133 25 27 28 29 65 68 77 0\n150 27 0 149 145 148 78 0\n151 -12 0 150 12 0\n152 36 0 150 130 132 61 0\n153 0 152 151 131 70 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00017.record032_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00017.record032
