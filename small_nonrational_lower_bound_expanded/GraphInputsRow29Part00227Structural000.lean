module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00227Data
public import GraphInputsRow29Part00227Frames
public import GraphInputsRow29Part00227Leaves
public import GraphInputsRow29Part00227Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨103, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 1946157056, 2053641430089334784, (certNat% 4), 824684052480]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), (certNat% 7), 2199107141632, (certNat% 8)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 10), (certNat% 11)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 11), 72057594054705152, (certNat% 8)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17), (certNat% 18), 67108864]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 21), (certNat% 22), (certNat% 23), 13194810621952]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 15), 1140850688]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), (certNat% 27), 35185714266112, 1152921504673955840]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 27), (certNat% 29)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), (certNat% 29), 1152921504673955840, (certNat% 32)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), (certNat% 35), 1149239296, 1188950301625810944, (certNat% 36)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 34), 2199123918848, (certNat% 17), (certNat% 38), 48379048493056]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), (certNat% 41), 1188950301701308416, (certNat% 4), 824667275264]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), 155759673344, (certNat% 43), (certNat% 44)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), 1152921521853825024, (certNat% 21), (certNat% 46), 1476395008, (certNat% 47)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), 1711276032, (certNat% 34), (certNat% 49), (certNat% 50), 13194139533312]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 52), (certNat% 21), 3023698919424, (certNat% 53), 2080374784, (certNat% 54)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c26 c19
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c27 c18
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c28 c17
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c29 c8
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c30 c7
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c31 c0
  c32
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3707a1e45d1cc6b16c3b15c37362b89e2d4b329c972729aa5a8ea9695a369a68d9366392e2b89eb86715c5693a659564d9594e5554d58d5351d54d3352d2b46d4749d176c3a8e6358ce394d5334e334cc7392d4b32d2b2ac6b86d1b26c5b89d2785d1725c3743c2f5611c46926299164388e07a6138651324592948d0762328e1322c1b21c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6da6db6db6db69a6924926d249a6db6d34d24d269369b6d34d2492492489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 63), (facetIndex 65), (facetIndex 94)]))
 (.leaf ([(facetIndex 64), (facetIndex 83), (facetIndex 92), (facetIndex 105), (facetIndex 108)])))
 (.branch 3
 (.leaf ([(facetIndex 58), (facetIndex 62), (facetIndex 66), (facetIndex 104)]))
 (.branch 4
 (.leaf ([(facetIndex 67), (facetIndex 99), (facetIndex 101), (facetIndex 106)]))
 (.leaf ([(facetIndex 38), (facetIndex 40), (facetIndex 90), (facetIndex 102)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 60), (facetIndex 88), (facetIndex 103)]))
 (.leaf ([(facetIndex 74), (facetIndex 89), (facetIndex 107)])))
 (.branch 8
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 47), (facetIndex 54), (facetIndex 91), (facetIndex 93), (facetIndex 95)]))
 (.branch 9
 (.leaf ([(facetIndex 48), (facetIndex 85), (facetIndex 87), (facetIndex 96), (facetIndex 97), (facetIndex 98)]))
 (.leaf ([(facetIndex 51), (facetIndex 69), (facetIndex 75)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "16312543038887071746580801000000096000090320102050200070090087000770404z26;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record011" 85

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record011" "{\"ridges\":[[8,546],[14,592],[16,608],[22,290],[22,292],[32,292],[33,546],[40,297],[42,323],[43,586],[47,210],[48,323],[49,530],[49,592],[51,352],[52,546],[52,608],[53,546],[54,706],[60,297],[69,325],[69,352],[72,592],[74,297],[74,352],[75,305],[76,592],[77,224],[77,608],[80,290],[80,292],[82,292],[84,290],[84,292],[85,210],[87,586],[88,106],[89,352],[90,424],[91,450],[92,352],[93,114],[94,290],[94,816],[95,834],[96,352],[97,706],[98,352],[98,834],[102,352],[103,424],[105,116],[106,452],[107,352],[107,424],[108,816]],\"owners\":[[49,530,[83,94],[6,31,37,46,87,93,95]],[8,546,[83,93,94,97,98],[33,46,52,53]],[33,546,[93,94,97,98],[8,46,52,53,83]],[52,546,[83,94],[8,33,46,53,93,97,98]],[53,546,[83,93,94,98],[8,33,46,52,97]],[14,592,[87,93,95,108],[49,72,76]],[49,592,[108],[14,72,76,87,93,95]],[72,592,[93,95,108],[14,49,76,87]],[76,592,[87,95],[14,49,72,93,108]],[77,224,[88,96,101,106,107],[15,50,68,73,97]],[16,608,[93,97,98,108],[52,76,77]],[52,608,[108],[16,76,77,93,97,98]],[77,608,[93,98,108],[16,52,76,97]],[22,290,[40,45,51,89,90,92,94,96,98],[32,80,82,84]],[80,290,[45,51,92,94,96,98],[22,32,40,82,84,89,90]],[84,290,[40,45,51,89,92,94,98],[22,32,80,82,90,96]],[94,290,[22,32,40,51,80,84,89,90,96],[45,82,92,98]],[22,292,[60,64,69,102,103,105,106],[32,80,82,84]],[32,292,[102,103,105,106],[22,60,64,69,80,82,84]],[80,292,[64,69,105,106],[22,32,60,82,84,102,103]],[82,292,[60,69,102,103,106],[22,32,64,80,84,105]],[84,292,[60,64,69,102,105],[22,32,80,82,103,106]],[88,106,[38,89],[]],[40,297,[60,74],[]],[60,297,[40,74],[]],[74,297,[40,60],[]],[42,323,[48,51],[]],[48,323,[42,51],[]],[43,586,[87],[]],[87,586,[43],[]],[93,114,[44,92],[]],[75,305,[45,64],[]],[47,210,[85],[]],[85,210,[47],[]],[51,352,[102,105,106,107,108],[69,74,75,89,92,96,98]],[69,352,[89,92,96,98,107,108],[51,74,75,102,105,106]],[74,352,[92,96,98,105,106,108],[51,69,75,89,102,107]],[89,352,[69,75,105,106,108],[51,74,92,96,98,102,107]],[92,352,[69,74,102,106,107],[51,75,89,96,98,105,108]],[96,352,[69,74,75,102,105,108],[51,89,92,98,106,107]],[98,352,[69,74,75,102,105,106,107],[51,89,92,96,108]],[102,352,[51,75,92,96,98,108],[69,74,89,105,106,107]],[107,352,[51,69,75,92,98,105,108],[74,89,96,102,106]],[54,706,[97],[]],[97,706,[54],[]],[69,325,[62,67],[]],[105,116,[63],[]],[90,424,[103,107],[]],[103,424,[90,107],[]],[107,424,[90,103],[]],[91,450,[96],[]],[94,816,[108],[]],[108,816,[94],[]],[95,834,[98],[]],[98,834,[95],[]],[106,452,[104],[]]],\"edges\":[[37,[22,32,40,45,51,60,64,69,74,75,80,82,84,89,90,92,94,96,98,102,103,105,106,107,108]],[38,[8,16,33,46,52,53,65,76,77,83,93,94,97,98,108]],[41,[14,16,43,49,52,54,72,76,77,87,93,95,97,98,108]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-17,-10],[-20,-17],[-30,-13],[-30,-25],[-31,-30],[-32,-17],[-32,-30],[-35,-30],[-38,-17],[-44,-12],[-44,-17],[-44,-24],[-44,-30],[-47,-10],[-47,-20],[-47,-38],[-47,-44],[-48,-17],[-48,-47],[-57,-24],[-57,-54],[-16,35,45],[-1,35,44,45,48,49],[-6,44,45,48,49],[-18,35,45],[-19,35,44,45,49],[-2,38,44,46,57],[-16,57],[-28,44,46,57],[-31,38,46],[-32,39,47,50,55,56],[-3,44,48,49,57],[-18,57],[-32,44,49,57],[-4,8,12,17,40,41,43,45,47,49],[-33,12,17,43,45,47,49],[-36,8,12,17,40,43,45,49],[-45,4,5,8,17,33,36,40,41,47],[-4,21,24,27,51,52,54,55],[-5,51,52,54,55],[-33,24,27,54,55],[-34,21,27,51,52,55],[-36,21,24,27,51,54],[-39,7,40],[-8,21,29],[-21,8,29],[-29,8,21],[-9,15,17],[-15,9,17],[-10,38],[-38,10],[-44,11,43],[-30,12,24],[-14,37],[-37,14],[-17,51,54,55,56,57],[-27,40,43,47,49,56,57],[-29,43,47,49,54,55,57],[-40,27,30,54,55,57],[-43,27,29,51,55,56],[-47,27,29,30,51,54,57],[-49,27,29,30,51,54,55,56],[-51,17,30,43,47,49,57],[-56,17,27,30,43,49,54,57],[-20,48],[-48,20],[-27,22,26],[-54,23],[-41,52,56],[-52,41,56],[-56,41,52],[-42,47],[-45,57],[-57,45],[-46,49],[-49,46],[-55,53],[-11,58],[-12,58],[-23,58],[-45,58],[-24,59],[-35,59],[-43,59],[-54,59],[-57,59],[-22,60],[-53,60],[-26,61],[-50,61],[-55,61],[-7,62],[-8,62],[-41,62],[-51,62],[-63,21,39,52],[-21,63],[-52,63],[-64,29,40,56],[-29,64],[-40,64],[-56,64],[-65,9,10,14,20,42,44,46],[-9,65],[-10,65],[-14,65],[-20,65],[-44,65],[-46,65],[-66,15,37,38,47,48,49],[-15,66],[-37,66],[-38,66],[-47,66],[-48,66],[-49,66],[-67,17,27,30],[-17,67],[-30,67],[-59,68],[-58,68],[-58,-59,69],[-62,70],[-61,70],[-70,71],[-60,71],[-60,-70,72],[-71,73],[-72,74],[-68,73],[-68,-71,74],[-69,74],[-69,-71,75],[-76,63,64],[-64,76],[-63,76],[-63,-64,77],[-78,66,67],[-67,78],[-66,78],[-66,-67,79],[-80,65,78],[-78,80],[-79,81],[-65,80],[-65,-78,81],[-80,82],[-81,83],[-76,82],[-76,-80,83],[-77,-80,84],[-84,85],[-73,-83,85],[-74,-82,85],[-75,85],[-85],[4,5,8,12,17,21,24,27,29,30,33,34,36,40,41,43,45,47,49,51,52,54,55,56,57],[1,3,6,13,18,19,25,31,32,35,44,45,48,49,57],[2,3,10,16,18,20,28,31,32,38,44,46,48,49,57]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":51,\"b\":43},{\"tag\":\"incompatible\",\"a\":54,\"b\":51},{\"tag\":\"incompatible\",\"a\":75,\"b\":46},{\"tag\":\"incompatible\",\"a\":75,\"b\":65},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":51},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":83,\"b\":75},{\"tag\":\"incompatible\",\"a\":87,\"b\":51},{\"tag\":\"incompatible\",\"a\":93,\"b\":45},{\"tag\":\"incompatible\",\"a\":93,\"b\":51},{\"tag\":\"incompatible\",\"a\":93,\"b\":64},{\"tag\":\"incompatible\",\"a\":93,\"b\":75},{\"tag\":\"incompatible\",\"a\":96,\"b\":43},{\"tag\":\"incompatible\",\"a\":96,\"b\":54},{\"tag\":\"incompatible\",\"a\":96,\"b\":87},{\"tag\":\"incompatible\",\"a\":96,\"b\":93},{\"tag\":\"incompatible\",\"a\":97,\"b\":51},{\"tag\":\"incompatible\",\"a\":97,\"b\":96},{\"tag\":\"incompatible\",\"a\":108,\"b\":64},{\"tag\":\"incompatible\",\"a\":108,\"b\":105},{\"tag\":\"mate\",\"ridge\":530,\"a\":49,\"owners\":[83,94]},{\"tag\":\"mate\",\"ridge\":546,\"a\":8,\"owners\":[83,93,94,97,98]},{\"tag\":\"mate\",\"ridge\":546,\"a\":33,\"owners\":[93,94,97,98]},{\"tag\":\"mate\",\"ridge\":546,\"a\":52,\"owners\":[83,94]},{\"tag\":\"mate\",\"ridge\":546,\"a\":53,\"owners\":[83,93,94,98]},{\"tag\":\"mate\",\"ridge\":592,\"a\":14,\"owners\":[87,93,95,108]},{\"tag\":\"mate\",\"ridge\":592,\"a\":49,\"owners\":[108]},{\"tag\":\"mate\",\"ridge\":592,\"a\":72,\"owners\":[93,95,108]},{\"tag\":\"mate\",\"ridge\":592,\"a\":76,\"owners\":[87,95]},{\"tag\":\"mate\",\"ridge\":224,\"a\":77,\"owners\":[88,96,101,106,107]},{\"tag\":\"mate\",\"ridge\":608,\"a\":16,\"owners\":[93,97,98,108]},{\"tag\":\"mate\",\"ridge\":608,\"a\":52,\"owners\":[108]},{\"tag\":\"mate\",\"ridge\":608,\"a\":77,\"owners\":[93,98,108]},{\"tag\":\"mate\",\"ridge\":290,\"a\":22,\"owners\":[40,45,51,89,90,92,94,96,98]},{\"tag\":\"mate\",\"ridge\":290,\"a\":80,\"owners\":[45,51,92,94,96,98]},{\"tag\":\"mate\",\"ridge\":290,\"a\":84,\"owners\":[40,45,51,89,92,94,98]},{\"tag\":\"mate\",\"ridge\":290,\"a\":94,\"owners\":[22,32,40,51,80,84,89,90,96]},{\"tag\":\"mate\",\"ridge\":292,\"a\":22,\"owners\":[60,64,69,102,103,105,106]},{\"tag\":\"mate\",\"ridge\":292,\"a\":32,\"owners\":[102,103,105,106]},{\"tag\":\"mate\",\"ridge\":292,\"a\":80,\"owners\":[64,69,105,106]},{\"tag\":\"mate\",\"ridge\":292,\"a\":82,\"owners\":[60,69,102,103,106]},{\"tag\":\"mate\",\"ridge\":292,\"a\":84,\"owners\":[60,64,69,102,105]},{\"tag\":\"mate\",\"ridge\":106,\"a\":88,\"owners\":[38,89]},{\"tag\":\"mate\",\"ridge\":297,\"a\":40,\"owners\":[60,74]},{\"tag\":\"mate\",\"ridge\":297,\"a\":60,\"owners\":[40,74]},{\"tag\":\"mate\",\"ridge\":297,\"a\":74,\"owners\":[40,60]},{\"tag\":\"mate\",\"ridge\":323,\"a\":42,\"owners\":[48,51]},{\"tag\":\"mate\",\"ridge\":323,\"a\":48,\"owners\":[42,51]},{\"tag\":\"mate\",\"ridge\":586,\"a\":43,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":586,\"a\":87,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":114,\"a\":93,\"owners\":[44,92]},{\"tag\":\"mate\",\"ridge\":305,\"a\":75,\"owners\":[45,64]},{\"tag\":\"mate\",\"ridge\":210,\"a\":47,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":210,\"a\":85,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":352,\"a\":51,\"owners\":[102,105,106,107,108]},{\"tag\":\"mate\",\"ridge\":352,\"a\":69,\"owners\":[89,92,96,98,107,108]},{\"tag\":\"mate\",\"ridge\":352,\"a\":74,\"owners\":[92,96,98,105,106,108]},{\"tag\":\"mate\",\"ridge\":352,\"a\":89,\"owners\":[69,75,105,106,108]},{\"tag\":\"mate\",\"ridge\":352,\"a\":92,\"owners\":[69,74,102,106,107]},{\"tag\":\"mate\",\"ridge\":352,\"a\":96,\"owners\":[69,74,75,102,105,108]},{\"tag\":\"mate\",\"ridge\":352,\"a\":98,\"owners\":[69,74,75,102,105,106,107]},{\"tag\":\"mate\",\"ridge\":352,\"a\":102,\"owners\":[51,75,92,96,98,108]},{\"tag\":\"mate\",\"ridge\":352,\"a\":107,\"owners\":[51,69,75,92,98,105,108]},{\"tag\":\"mate\",\"ridge\":706,\"a\":54,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":706,\"a\":97,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":325,\"a\":69,\"owners\":[62,67]},{\"tag\":\"mate\",\"ridge\":116,\"a\":105,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":424,\"a\":90,\"owners\":[103,107]},{\"tag\":\"mate\",\"ridge\":424,\"a\":103,\"owners\":[90,107]},{\"tag\":\"mate\",\"ridge\":424,\"a\":107,\"owners\":[90,103]},{\"tag\":\"mate\",\"ridge\":450,\"a\":91,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":816,\"a\":94,\"owners\":[108]},{\"tag\":\"mate\",\"ridge\":816,\"a\":108,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":834,\"a\":95,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":834,\"a\":98,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":452,\"a\":106,\"owners\":[104]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":44,\"full_literals\":[-11,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":45,\"full_literals\":[-12,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-23,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":94,\"full_literals\":[-45,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":64,\"full_literals\":[-24,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-35,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":92,\"full_literals\":[-43,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":105,\"full_literals\":[-54,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":108,\"full_literals\":[-57,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":62,\"full_literals\":[-22,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":104,\"full_literals\":[-53,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-26,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":101,\"full_literals\":[-50,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":106,\"full_literals\":[-55,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":38,\"full_literals\":[-7,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":40,\"full_literals\":[-8,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":90,\"full_literals\":[-41,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":102,\"full_literals\":[-51,62]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[60,88,103],\"full_literals\":[-63,21,39,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":60,\"full_literals\":[-21,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":103,\"full_literals\":[-52,63]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[74,89,107],\"full_literals\":[-64,29,40,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":74,\"full_literals\":[-29,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":89,\"full_literals\":[-40,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":107,\"full_literals\":[-56,64]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[42,43,47,54,91,93,95],\"full_literals\":[-65,9,10,14,20,42,44,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":42,\"full_literals\":[-9,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":43,\"full_literals\":[-10,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":47,\"full_literals\":[-14,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":54,\"full_literals\":[-20,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":93,\"full_literals\":[-44,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":95,\"full_literals\":[-46,65]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[48,85,87,96,97,98],\"full_literals\":[-66,15,37,38,47,48,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":48,\"full_literals\":[-15,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":85,\"full_literals\":[-37,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":87,\"full_literals\":[-38,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":96,\"full_literals\":[-47,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":97,\"full_literals\":[-48,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":98,\"full_literals\":[-49,66]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[51,69,75],\"full_literals\":[-67,17,27,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":51,\"full_literals\":[-17,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":75,\"full_literals\":[-30,67]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-59,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-71,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-69,-71,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-76,63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-64,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,66,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-67,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,65,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-78,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-80,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-81,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-80,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-77,-80,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-84,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-73,-83,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-74,-82,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,85],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[22,32,40,45,51,60,64,69,74,75,80,82,84,89,90,92,94,96,98,102,103,105,106,107,108]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[8,16,33,46,52,53,65,76,77,83,93,94,97,98,108]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[14,16,43,49,52,54,72,76,77,87,93,95,97,98,108]}]}"
  "160 -84 0 156 152 0\n161 -75 0 156 155 0\n162 76 73 0 130 120 86 128 125 124 91 85 121 79 82 53 89 126 87 67 59 41 123 95 94 93 81 84 135 136 100 102 97 98 61 62 56 43 39 42 40 157 0\n163 64 73 0 162 128 125 123 92 130 120 86 124 91 85 121 79 82 53 89 126 87 67 59 44 94 93 100 102 134 46 70 96 0\n164 80 73 0 128 125 123 92 130 120 86 124 91 85 121 79 82 53 89 126 87 67 59 44 78 84 52 81 83 25 22 90 143 145 139 140 105 107 109 118 113 114 115 116 29 30 64 27 31 32 159 0\n165 73 0 160 128 130 125 126 120 121 123 124 87 82 85 86 79 93 94 89 91 67 53 59 163 164 151 137 97 98 47 71 99 0\n166 -83 0 165 156 153 0\n167 -81 0 166 148 0\n168 -79 0 167 144 0\n169 -44 63 17 27 30 43 47 49 54 55 57 56 0 63 98 40 69 97 42 58 45 59 73 10 12 37 36 35 157 0\n170 -65 44 17 42 46 0 167 146 140 111 112 113 115 48 54 50 65 103 0\n171 -80 17 27 30 43 47 49 54 55 57 56 0 166 117 72 75 150 136 169 170 104 105 106 107 142 49 51 55 66 138 110 0\n172 80 49 57 0 75 33 28 143 145 140 105 107 108 113 115 34 29 30 27 32 159 0\n173 -17 49 57 0 75 33 28 1 2 6 9 11 18 30 27 29 32 159 0\n174 -30 49 57 0 168 73 33 3 4 5 7 8 13 119 26 141 115 24 32 23 158 0\n175 43 47 49 54 55 57 56 0 166 174 173 172 150 135 101 57 171 0\n176 -43 -80 55 56 0 156 166 150 135 100 147 154 84 120 131 125 126 123 124 87 95 89 67 60 0\n177 49 54 55 57 56 0 33 28 75 172 176 175 14 15 16 17 19 30 34 29 27 32 159 0\n178 -49 0 167 76 116 109 140 146 0\n179 -54 69 0 68 85 80 122 0\n180 57 56 0 156 178 172 147 154 129 132 179 177 77 91 88 124 127 0\n181 -57 0 161 156 20 21 74 86 81 122 132 133 154 125 126 147 149 123 124 87 143 135 136 93 94 95 89 91 67 139 140 101 97 98 40 43 39 41 118 114 38 0\n182 80 0 181 178 172 0\n183 56 0 181 180 0\n184 -76 0 182 166 150 0\n185 64 0 183 102 0\n186 0 185 184 135 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record019
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "370ba2789723a719a6558d64d8b6538ce4b8ae1783ed86e178751cc6715c4f1b26a99a5693a6598e479715a5954d54d4b59354d4b4ad8745d0f5c368d5334e332cd4b32e2b4ae1b16c3b61d4731d2729c9715c3743c4f0bc1f550cc4c8aa4588e945518c531924c98a4a9514c5454552344d48ca344c3322c2b41c8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6d34da69b6da4934934934d24d269a6d2693493692492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 71), (facetIndex 73), (facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 47), (facetIndex 58), (facetIndex 86), (facetIndex 88)])))
 (.branch 3
 (.leaf ([(facetIndex 52), (facetIndex 63), (facetIndex 91), (facetIndex 93)]))
 (.branch 4
 (.leaf ([(facetIndex 42), (facetIndex 46), (facetIndex 69), (facetIndex 74)]))
 (.leaf ([(facetIndex 56), (facetIndex 65), (facetIndex 70), (facetIndex 80)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 41), (facetIndex 53), (facetIndex 67)]))
 (.branch 7
 (.leaf ([(facetIndex 32), (facetIndex 60), (facetIndex 61), (facetIndex 75)]))
 (.leaf ([(facetIndex 36), (facetIndex 49), (facetIndex 64)]))))
 (.branch 9
 (.leaf ([(facetIndex 34), (facetIndex 50), (facetIndex 79)]))
 (.branch 10
 (.leaf ([(facetIndex 31), (facetIndex 33), (facetIndex 37), (facetIndex 38), (facetIndex 45)]))
 (.leaf ([(facetIndex 30), (facetIndex 35), (facetIndex 39), (facetIndex 40)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "20200101000004800063000430504720660104005208701390035aa997a8969az1e;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 68), (facetIndex 72), (facetIndex 76), (facetIndex 81), (facetIndex 82), (facetIndex 83)]))
 (.leaf ([(facetIndex 98), (facetIndex 99), (facetIndex 100)])))
 (.branch 3
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 55), (facetIndex 57)]))
 (.leaf ([(facetIndex 84), (facetIndex 85), (facetIndex 96), (facetIndex 97)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 48), (facetIndex 51), (facetIndex 54)]))
 (.leaf ([(facetIndex 59), (facetIndex 62), (facetIndex 66)])))
 (.branch 7
 (.leaf ([(facetIndex 89), (facetIndex 92), (facetIndex 95)]))
 (.leaf ([(facetIndex 87), (facetIndex 90), (facetIndex 94)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "125bdc61f0e1b000000000000140140a105008040024z20;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5, 6, 7]
def grouped2_0011 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0012 : List Nat := [8]
def grouped2_0013 : List Nat := [8, 9, 10]
def grouped2_0014 : List Nat := [9, 10]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0017 : List Nat := [0, 1, 2, 3]
def grouped3_0019 : List Nat := [1]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [2, 3]
def grouped3_0022 : List Nat := [3]
def grouped3_0023 : List Nat := [4, 5, 6, 7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record019" "{\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record019" 52

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record019" "{\"ridges\":[[17,552],[19,584],[21,49],[21,560],[23,592],[34,49],[44,538],[46,552],[50,560],[57,540],[61,584],[65,592],[68,49],[69,552],[69,560],[70,584],[70,592],[73,552],[73,584],[74,552],[75,584],[78,560],[78,592],[79,560],[80,592],[96,538],[97,540],[98,120],[98,560]],\"owners\":[[17,552,[96,98,99],[46,69,73,74]],[46,552,[98,99],[17,69,73,74,96]],[69,552,[99],[17,46,73,74,96,98]],[73,552,[96],[17,46,69,74,98,99]],[74,552,[96,98],[17,46,69,73,99]],[19,584,[97,98,99],[61,70,73,75]],[61,584,[98,99],[19,70,73,75,97]],[70,584,[99],[19,61,73,75,97,98]],[73,584,[97],[19,61,70,75,98,99]],[75,584,[97,98],[19,61,70,73,99]],[21,560,[96,98,100],[50,69,78,79]],[50,560,[98,100],[21,69,78,79,96]],[69,560,[100],[21,50,78,79,96,98]],[78,560,[96],[21,50,69,79,98,100]],[79,560,[96,98],[21,50,69,78,100]],[98,560,[21,50,79],[69,78,96,100]],[23,592,[97,98,100],[65,70,78,80]],[65,592,[98,100],[23,70,78,80,97]],[70,592,[100],[23,65,78,80,97,98]],[78,592,[97],[23,65,70,80,98,100]],[80,592,[97,98],[23,65,70,78,100]],[44,538,[96],[]],[96,538,[44],[]],[57,540,[97],[]],[97,540,[57],[]],[98,120,[68],[]]],\"edges\":[[29,[17,19,44,46,57,61,69,70,73,74,75,96,97,98,99]],[34,[21,23,44,50,57,65,69,70,78,79,80,96,97,98,100]],[38,[17,21,46,50,69,73,74,78,79,82,83,96,98,99,100]],[41,[19,23,61,65,70,73,75,78,80,82,83,97,98,99,100]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record019" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record019\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-8],[-14,-9],[-14,-13],[-19,-14],[-23,-14],[-24,-14],[-28,-27],[-29,-6],[-29,-10],[-29,-17],[-29,-21],[-30,-29],[-31,-30],[-3,-5,-14],[-1,27,29,30],[-8,29,30],[-15,30],[-18,27],[-19,27,29],[-2,28,29,30],[-12,29,30],[-16,30],[-18,28],[-20,28,29],[-3,27,29,31],[-9,29,31],[-15,31],[-22,27],[-23,27,29],[-29,3,9,23],[-4,28,29,31],[-13,29,31],[-16,31],[-22,28],[-24,28,29],[-7,27],[-27,7],[-11,28],[-28,11],[-29,14],[-32,17,18,21,22],[-33,6,8,15,19],[-34,10,13,16,24],[-35,5,9,23],[-36,32],[-37,33,34],[-38,37],[-39,36,38],[-40,35],[-41,40],[-42,39,41],[42],[-14,43],[-25,43],[-26,43],[-29,44],[-30,44],[-31,44],[-7,45],[-11,45],[-27,46],[-28,46],[-44,47],[-43,47],[-43,-44,48],[-46,49],[-45,49],[-45,-46,50],[-47,-50,51],[-48,-49,51],[-51,52],[-52],[1,2,7,8,11,12,15,16,18,19,20,27,28,29,30],[3,4,7,9,11,13,15,16,22,23,24,27,28,29,31],[1,3,8,9,15,18,19,22,23,25,26,27,29,30,31],[2,4,12,13,16,18,20,22,24,25,26,28,29,30,31]],\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":68,\"b\":46},{\"tag\":\"incompatible\",\"a\":68,\"b\":50},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":74,\"b\":68},{\"tag\":\"incompatible\",\"a\":79,\"b\":68},{\"tag\":\"incompatible\",\"a\":80,\"b\":68},{\"tag\":\"incompatible\",\"a\":97,\"b\":96},{\"tag\":\"incompatible\",\"a\":98,\"b\":42},{\"tag\":\"incompatible\",\"a\":98,\"b\":56},{\"tag\":\"incompatible\",\"a\":98,\"b\":71},{\"tag\":\"incompatible\",\"a\":98,\"b\":77},{\"tag\":\"incompatible\",\"a\":99,\"b\":98},{\"tag\":\"incompatible\",\"a\":100,\"b\":99},{\"tag\":\"three\",\"ridge\":49,\"vertices\":[21,34,68]},{\"tag\":\"mate\",\"ridge\":552,\"a\":17,\"owners\":[96,98,99]},{\"tag\":\"mate\",\"ridge\":552,\"a\":46,\"owners\":[98,99]},{\"tag\":\"mate\",\"ridge\":552,\"a\":69,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":552,\"a\":73,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":552,\"a\":74,\"owners\":[96,98]},{\"tag\":\"mate\",\"ridge\":584,\"a\":19,\"owners\":[97,98,99]},{\"tag\":\"mate\",\"ridge\":584,\"a\":61,\"owners\":[98,99]},{\"tag\":\"mate\",\"ridge\":584,\"a\":70,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":584,\"a\":73,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":584,\"a\":75,\"owners\":[97,98]},{\"tag\":\"mate\",\"ridge\":560,\"a\":21,\"owners\":[96,98,100]},{\"tag\":\"mate\",\"ridge\":560,\"a\":50,\"owners\":[98,100]},{\"tag\":\"mate\",\"ridge\":560,\"a\":69,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":560,\"a\":78,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":560,\"a\":79,\"owners\":[96,98]},{\"tag\":\"mate\",\"ridge\":560,\"a\":98,\"owners\":[21,50,79]},{\"tag\":\"mate\",\"ridge\":592,\"a\":23,\"owners\":[97,98,100]},{\"tag\":\"mate\",\"ridge\":592,\"a\":65,\"owners\":[98,100]},{\"tag\":\"mate\",\"ridge\":592,\"a\":70,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":592,\"a\":78,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":592,\"a\":80,\"owners\":[97,98]},{\"tag\":\"mate\",\"ridge\":538,\"a\":44,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":538,\"a\":96,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":540,\"a\":57,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":540,\"a\":97,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":120,\"a\":98,\"owners\":[68]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[71,73,77,78],\"full_literals\":[-32,17,18,21,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[42,46,69,74],\"full_literals\":[-33,6,8,15,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[56,65,70,80],\"full_literals\":[-34,10,13,16,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[34,50,79],\"full_literals\":[-35,5,9,23]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-36,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-37,33,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,36,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-40,35,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-41,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-42,39,41],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":68,\"full_literals\":[-14,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":82,\"full_literals\":[-25,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":83,\"full_literals\":[-26,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":98,\"full_literals\":[-29,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":99,\"full_literals\":[-30,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":100,\"full_literals\":[-31,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":44,\"full_literals\":[-7,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":57,\"full_literals\":[-11,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":96,\"full_literals\":[-27,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":97,\"full_literals\":[-28,46]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-44,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-46,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-47,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-48,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[17,19,44,46,57,61,69,70,73,74,75,96,97,98,99]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[21,23,44,50,57,65,69,70,78,79,80,96,97,98,100]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[17,21,46,50,69,73,74,78,79,82,83,96,98,99,100]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[19,23,61,65,70,73,75,78,80,82,83,97,98,99,100]}]}"
  "77 -51 0 72 71 0\n78 -30 49 0 66 61 28 67 60 59 62 12 13 26 32 25 29 31 35 27 33 74 0\n79 -29 -35 0 40 2 5 30 44 14 0\n80 29 49 0 78 22 17 66 61 18 67 60 59 62 16 21 15 19 20 24 73 0\n81 49 0 52 66 61 18 28 78 17 22 80 8 9 10 11 40 79 41 1 3 4 6 49 45 42 43 50 46 51 47 48 0\n82 -48 0 81 77 70 0\n83 -29 0 82 40 56 53 65 0\n84 28 30 27 0 83 15 21 16 22 17 19 36 18 38 24 20 73 0\n85 -28 50 0 39 62 60 68 0\n86 27 28 0 83 35 38 28 36 29 84 13 27 33 26 32 25 31 74 0\n87 50 0 85 86 37 61 59 68 0\n88 -47 0 87 77 69 0\n89 -44 0 88 63 0\n90 -43 0 88 64 0\n91 -30 0 89 57 0\n92 -31 0 89 58 0\n93 -25 0 90 54 0\n94 -26 0 90 55 0\n95 -15 0 91 17 0\n96 -16 0 91 22 0\n97 -8 0 91 83 16 0\n98 -12 0 91 83 21 0\n99 -9 0 92 83 26 0\n100 -13 0 92 83 32 0\n101 28 0 92 91 83 94 93 96 100 98 23 34 24 35 20 31 76 0\n102 -27 0 101 7 0\n103 -18 0 102 18 0\n104 -22 0 102 28 0\n105 -23 0 102 83 29 0\n106 -19 0 102 83 19 0\n107 -1 0 102 91 83 15 0\n108 -3 0 102 92 83 25 0\n109 0 107 108 99 97 92 103 106 104 105 93 95 102 83 91 94 75 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record029
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2d8ae25c3723c2f1e2968da8e8ba598e6558d62d8ce4b8ae2785e0fb61b85e1b46b1b26a9a6659366392e665594e595555356352d64d3362d4b4ad8749d1743d70da398d6338e5354e332ce4b32e2b4ae1b16c3b31ca719d1725c3743c8f13cd22a89a519261582e07a51346292a61926545494550b41d50cc348ca324c5322c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6da69349b4924db4da4924d34936da4924926924d3492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 55), (facetIndex 72), (facetIndex 74), (facetIndex 84), (facetIndex 85), (facetIndex 86)]))
 (.branch 2
 (.leaf ([(facetIndex 96), (facetIndex 102)]))
 (.leaf ([(facetIndex 48), (facetIndex 65), (facetIndex 66), (facetIndex 81)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 50), (facetIndex 67), (facetIndex 68), (facetIndex 82)]))
 (.leaf ([(facetIndex 92), (facetIndex 101), (facetIndex 106), (facetIndex 108)])))
 (.branch 6
 (.leaf ([(facetIndex 93), (facetIndex 99), (facetIndex 104), (facetIndex 107)]))
 (.leaf ([(facetIndex 103), (facetIndex 105)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4b35c60a0102c0000000d00000000036900000000000c2z24;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [3, 4, 5, 6]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5, 6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record029" "{\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record029" 34

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record029" "{\"ridges\":[[22,545],[24,577],[24,592],[46,545],[48,586],[52,577],[52,592],[55,610],[64,545],[66,588],[71,577],[71,592],[74,612],[76,552],[78,592],[80,545],[81,712],[83,577],[83,592],[85,736],[86,864],[99,562],[101,586],[104,564],[106,588],[107,688],[108,712]],\"owners\":[[22,545,[50,55,68,74,82,85,86],[46,64,76,80]],[46,545,[68,74,82,85,86],[22,50,55,64,76,80]],[64,545,[50,55,82,85,86],[22,46,68,74,76,80]],[80,545,[50,55,68,74,86],[22,46,64,76,82,85]],[76,552,[],[22,46,64,80,99,104,107]],[24,577,[48,55,66,74,81,85,86],[52,71,78,83]],[52,577,[66,74,81,85,86],[24,48,55,71,78,83]],[71,577,[48,55,81,85,86],[24,52,66,74,78,83]],[83,577,[48,55,66,74,86],[24,52,71,78,81,85]],[24,592,[101,106,108],[52,71,78,83]],[52,592,[106,108],[24,71,78,83,101]],[71,592,[101,108],[24,52,78,83,106]],[78,592,[],[24,52,71,83,101,106,108]],[83,592,[101,106],[24,52,71,78,108]],[48,586,[101],[]],[101,586,[48],[]],[99,562,[50],[]],[55,610,[],[]],[66,588,[106],[]],[106,588,[66],[]],[104,564,[68],[]],[74,612,[],[]],[81,712,[108],[]],[108,712,[81],[]],[107,688,[82],[]],[85,736,[],[]],[86,864,[],[]]],\"edges\":[[38,[22,46,50,55,64,68,74,76,80,82,85,86,99,104,107]],[41,[24,48,52,55,66,71,74,78,81,83,85,86,101,106,108]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record029" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record029\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,5,7,10,12,17,19,20],[-3,10,12,17,19,20],[-8,5,7,17,19,20],[-15,5,7,10,12,20],[-13],[-2,4,7,9,12,16,19,20],[-6,9,12,16,19,20],[-11,4,7,16,19,20],[-18,4,7,9,12,20],[-2,22,24,26],[-6,24,26],[-11,22,26],[-14],[-18,22,24],[-4,22],[-22,4],[-21,5],[-7],[-9,24],[-24,9],[-23,10],[-12],[-16,26],[-26,16],[-25,17],[-19],[-20],[-4,27],[-9,27],[-16,27],[-5,28],[-10,28],[-17,28],[-22,29],[-24,29],[-26,29],[-27,30],[-30,31],[-28,-29,32],[-32,33],[-31,-33,34],[-34],[1,3,5,7,8,10,12,13,15,17,19,20,21,23,25],[2,4,6,7,9,11,12,14,16,18,19,20,22,24,26]],\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":545,\"a\":22,\"owners\":[50,55,68,74,82,85,86]},{\"tag\":\"mate\",\"ridge\":545,\"a\":46,\"owners\":[68,74,82,85,86]},{\"tag\":\"mate\",\"ridge\":545,\"a\":64,\"owners\":[50,55,82,85,86]},{\"tag\":\"mate\",\"ridge\":545,\"a\":80,\"owners\":[50,55,68,74,86]},{\"tag\":\"mate\",\"ridge\":552,\"a\":76,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":577,\"a\":24,\"owners\":[48,55,66,74,81,85,86]},{\"tag\":\"mate\",\"ridge\":577,\"a\":52,\"owners\":[66,74,81,85,86]},{\"tag\":\"mate\",\"ridge\":577,\"a\":71,\"owners\":[48,55,81,85,86]},{\"tag\":\"mate\",\"ridge\":577,\"a\":83,\"owners\":[48,55,66,74,86]},{\"tag\":\"mate\",\"ridge\":592,\"a\":24,\"owners\":[101,106,108]},{\"tag\":\"mate\",\"ridge\":592,\"a\":52,\"owners\":[106,108]},{\"tag\":\"mate\",\"ridge\":592,\"a\":71,\"owners\":[101,108]},{\"tag\":\"mate\",\"ridge\":592,\"a\":78,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":592,\"a\":83,\"owners\":[101,106]},{\"tag\":\"mate\",\"ridge\":586,\"a\":48,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":586,\"a\":101,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":562,\"a\":99,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":610,\"a\":55,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":588,\"a\":66,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":588,\"a\":106,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":564,\"a\":104,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":612,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":712,\"a\":81,\"owners\":[108]},{\"tag\":\"mate\",\"ridge\":712,\"a\":108,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":688,\"a\":107,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":736,\"a\":85,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":864,\"a\":86,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":48,\"full_literals\":[-4,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-9,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":81,\"full_literals\":[-16,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":50,\"full_literals\":[-5,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":68,\"full_literals\":[-10,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-17,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":101,\"full_literals\":[-22,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":106,\"full_literals\":[-24,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":108,\"full_literals\":[-26,29]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-28,-29,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-31,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[22,46,50,55,64,68,74,76,80,82,85,86,99,104,107]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[24,48,52,55,66,71,74,78,81,83,85,86,101,106,108]}]}"
  "45 1 3 5 8 10 15 17 21 23 25 0 18 22 5 26 27 43 0\n46 2 4 6 9 11 16 18 22 24 26 0 18 22 13 26 27 44 0\n47 27 0 22 27 26 18 28 29 30 16 7 20 6 9 24 8 46 0\n48 30 0 47 37 0\n49 31 0 48 38 0\n50 -33 0 49 42 41 0\n51 -32 0 50 40 0\n52 29 0 34 35 36 15 11 19 10 14 23 12 46 0\n53 -28 0 52 51 39 0\n54 -5 0 53 31 0\n55 -10 0 53 32 0\n56 -17 0 53 33 0\n57 -21 0 54 17 0\n58 -3 0 55 22 56 26 27 2 0\n59 -23 0 55 21 0\n60 -15 0 55 18 54 22 27 4 0\n61 -25 0 56 25 0\n62 -8 0 56 18 54 26 27 3 0\n63 -1 0 56 18 54 22 55 26 27 1 0\n64 0 59 61 54 58 63 60 56 57 62 55 45 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record029

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record030
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "d915c3723c2f2e2b4ab236a3a2ea66598e635a362d94e33a2e4b8ae8789e1783e785c96a559364b99956539655554d58d4b5534cd2b51d2745d0f66358ce394e332cd4b32d2b16c3b91d4731e2749ca719e1725c3743c8f13e544b252348aa26a4689a161582e078d14a4a926545494554342d074c328c9314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6d34d26d26da49249b4d269a49b4d24936934d2492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 50), (facetIndex 62), (facetIndex 74), (facetIndex 76)]))
 (.branch 2
 (.leaf ([(facetIndex 52), (facetIndex 64), (facetIndex 94), (facetIndex 96)]))
 (.leaf ([(facetIndex 65), (facetIndex 87), (facetIndex 100)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 85), (facetIndex 86), (facetIndex 102)]))
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 69), (facetIndex 77), (facetIndex 98), (facetIndex 103)])))
 (.branch 6
 (.leaf ([(facetIndex 71), (facetIndex 90), (facetIndex 91)]))
 (.leaf ([(facetIndex 99), (facetIndex 101)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "8f2d01040b404d8000020000a20011000004801z27;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [3, 4, 5, 6]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record030" "{\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record030" 45

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record030" "{\"ridges\":[[16,321],[16,324],[25,548],[42,548],[44,321],[44,324],[50,330],[55,354],[56,609],[62,204],[63,321],[63,324],[67,321],[70,321],[70,324],[71,609],[74,344],[76,456],[77,480],[84,548],[86,330],[88,548],[91,354],[92,548],[96,688],[98,736],[102,344],[103,864]],\"owners\":[[16,321,[50,55,74,76,77],[44,63,67,70]],[44,321,[74,76,77],[16,50,55,63,67,70]],[63,321,[55,77],[16,44,50,67,70,74,76]],[67,321,[50,55,76,77],[16,44,63,70,74]],[70,321,[50,74,76],[16,44,55,63,67,77]],[16,324,[86,91,102,103],[44,63,67,70]],[44,324,[102,103],[16,63,67,70,86,91]],[63,324,[91,103],[16,44,67,70,86,102]],[70,324,[86,102],[16,44,63,67,91,103]],[25,548,[65,71,100,103],[42,84,88,92]],[42,548,[100,103],[25,65,71,84,88,92]],[84,548,[65,71,103],[25,42,88,92,100]],[88,548,[71,103],[25,42,65,84,92,100]],[92,548,[65,100],[25,42,71,84,88,103]],[50,330,[86],[]],[86,330,[50],[]],[55,354,[91],[]],[91,354,[55],[]],[56,609,[71],[]],[71,609,[56],[]],[62,204,[85,101],[]],[74,344,[102],[]],[102,344,[74],[]],[76,456,[],[]],[77,480,[],[]],[96,688,[],[]],[98,736,[],[]],[103,864,[],[]]],\"edges\":[[38,[25,42,52,56,65,71,84,88,92,94,96,98,100,103]],[40,[16,44,50,55,63,67,70,74,76,77,86,91,102,103]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record030" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record030\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-7],[-14,-12],[-22,-14],[-1,5,7,15,16,17],[-4,15,16,17],[-10,7,17],[-12,5,7,16,17],[-13,5,15,16],[-1,20,22,29,30],[-4,29,30],[-10,22,30],[-13,20,29],[-2,11,14,27,30],[-3,27,30],[-18,11,14,30],[-21,14,30],[-23,11,27],[-5,20],[-20,5],[-7,22],[-22,7],[-8,14],[-14,8],[-9,19,28],[-15,29],[-29,15],[-16],[-17],[-25],[-26],[-30],[-31,5,9,15,16],[-5,31],[-15,31],[-6,32],[-24,32],[-11,33],[-27,33],[-19,34],[-20,34],[-29,34],[-7,35],[-8,35],[-14,36],[-22,36],[-28,37],[-33,38],[-32,38],[-38,39],[-31,39],[-31,-38,40],[-35,41],[-34,41],[-37,42],[-36,42],[-42,43],[-41,43],[-41,-42,44],[-39,-44,45],[-40,-43,45],[-45],[2,3,6,8,11,14,18,21,23,24,25,26,27,30],[1,4,5,7,10,12,13,15,16,17,20,22,29,30]],\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":71,\"b\":55},{\"tag\":\"incompatible\",\"a\":71,\"b\":67},{\"tag\":\"incompatible\",\"a\":91,\"b\":71},{\"tag\":\"mate\",\"ridge\":321,\"a\":16,\"owners\":[50,55,74,76,77]},{\"tag\":\"mate\",\"ridge\":321,\"a\":44,\"owners\":[74,76,77]},{\"tag\":\"mate\",\"ridge\":321,\"a\":63,\"owners\":[55,77]},{\"tag\":\"mate\",\"ridge\":321,\"a\":67,\"owners\":[50,55,76,77]},{\"tag\":\"mate\",\"ridge\":321,\"a\":70,\"owners\":[50,74,76]},{\"tag\":\"mate\",\"ridge\":324,\"a\":16,\"owners\":[86,91,102,103]},{\"tag\":\"mate\",\"ridge\":324,\"a\":44,\"owners\":[102,103]},{\"tag\":\"mate\",\"ridge\":324,\"a\":63,\"owners\":[91,103]},{\"tag\":\"mate\",\"ridge\":324,\"a\":70,\"owners\":[86,102]},{\"tag\":\"mate\",\"ridge\":548,\"a\":25,\"owners\":[65,71,100,103]},{\"tag\":\"mate\",\"ridge\":548,\"a\":42,\"owners\":[100,103]},{\"tag\":\"mate\",\"ridge\":548,\"a\":84,\"owners\":[65,71,103]},{\"tag\":\"mate\",\"ridge\":548,\"a\":88,\"owners\":[71,103]},{\"tag\":\"mate\",\"ridge\":548,\"a\":92,\"owners\":[65,100]},{\"tag\":\"mate\",\"ridge\":330,\"a\":50,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":330,\"a\":86,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":354,\"a\":55,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":354,\"a\":91,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":609,\"a\":56,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":609,\"a\":71,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":204,\"a\":62,\"owners\":[85,101]},{\"tag\":\"mate\",\"ridge\":344,\"a\":74,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":344,\"a\":102,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":456,\"a\":76,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":480,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":688,\"a\":96,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":98,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":864,\"a\":103,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[50,62,74,76],\"full_literals\":[-31,5,9,15,16]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":50,\"full_literals\":[-5,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":74,\"full_literals\":[-15,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":52,\"full_literals\":[-6,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":94,\"full_literals\":[-24,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-11,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":100,\"full_literals\":[-27,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":85,\"full_literals\":[-19,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":86,\"full_literals\":[-20,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":102,\"full_literals\":[-29,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":55,\"full_literals\":[-7,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":56,\"full_literals\":[-8,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":71,\"full_literals\":[-14,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":91,\"full_literals\":[-22,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":101,\"full_literals\":[-28,37]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-38,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-42,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-39,-44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[25,42,52,56,65,71,84,88,92,94,96,98,100,103]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[16,44,50,55,63,67,70,74,76,77,86,91,102,103]}]}"
  "64 -31 5 9 15 0 27 32 0\n65 2 3 6 8 11 14 18 21 23 24 27 0 29 30 31 62 0\n66 1 4 5 7 10 12 13 15 20 22 29 0 27 28 31 63 0\n67 14 38 0 31 47 37 38 17 14 48 36 35 16 22 15 13 65 0\n68 39 0 28 27 49 50 33 34 19 5 26 8 67 1 2 3 6 4 66 0\n69 -44 0 68 61 59 0\n70 -14 0 69 23 44 43 55 52 58 0\n71 38 0 70 67 0\n72 -42 0 69 61 71 28 27 31 56 58 60 52 53 51 42 40 41 33 34 6 21 7 9 10 12 66 0\n73 -37 0 72 54 0\n74 -36 0 72 55 0\n75 -28 0 73 46 0\n76 -22 0 74 45 0\n77 -10 0 76 31 11 0\n78 -7 0 76 20 0\n79 31 0 28 27 76 78 77 33 34 19 4 7 5 26 8 66 0\n80 40 0 79 71 51 0\n81 -43 0 80 61 60 0\n82 -41 0 81 57 0\n83 -34 0 82 53 0\n84 -19 0 83 39 0\n85 -20 0 83 40 0\n86 -29 0 83 41 0\n87 -9 0 84 75 24 0\n88 -5 0 85 18 0\n89 -15 0 86 25 0\n90 0 87 89 88 79 64 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record030
