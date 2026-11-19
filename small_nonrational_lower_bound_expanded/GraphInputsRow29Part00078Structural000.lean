module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00078Data
public import GraphInputsRow29Part00078Frames
public import GraphInputsRow29Part00078Leaves
public import GraphInputsRow29Part00078Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨95, by decide⟩, ⟨98, by decide⟩, ⟨103, by decide⟩, ⟨121, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 4467570873301204992]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), 578712552117108736]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 4), (certNat% 12), 17451451240415232]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17), (certNat% 18)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 15), (certNat% 21), (certNat% 17), (certNat% 18)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 7), (certNat% 9), (certNat% 23), 18253611008]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), (certNat% 26), (certNat% 27)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), (certNat% 9)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), (certNat% 32), (certNat% 33), 6192451635118080]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 6403557867651072, (certNat% 35), (certNat% 36), (certNat% 37)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), 568009424896, (certNat% 9), (certNat% 7)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), (certNat% 42), 2320479710150131712, (certNat% 43), 536870912]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 703687441776640, (certNat% 45), (certNat% 46)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 48), (certNat% 14), (certNat% 49), (certNat% 50), (certNat% 51)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 9), (certNat% 53), (certNat% 7)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 1585267120374022144, 15199652500471808, (certNat% 55), (certNat% 56), (certNat% 57)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), 1585267120374022144, (certNat% 59), (certNat% 60), (certNat% 61), 9007199254740992]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 6192450024505344, (certNat% 63), (certNat% 64)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), 1585267086014283776, (certNat% 64), 15199652500471808, (certNat% 66)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), 1585267120374022144, (certNat% 68), (certNat% 69), 6192452171988992, (certNat% 66)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), 1315051125551923200, (certNat% 72), 5207289753501696, (certNat% 9), (certNat% 73)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c27 c20
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c28 c19
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c29 c18
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c30 c17
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c31 c14
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c32 c13
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c33 c12
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c34 c5
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c35 c4
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c36 c3
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c37 c2
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c38 c1
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c39 c0
  c40
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e90f49b31c2f07ce88f29ab1a2e87ae1b26a99a6998e6c5996558d62d876c3a4e8b8ae1ba1e4789e1783e3c4b91e725694e5554d52d475c362d2b51d2743dc8da338d5334cb31cf0b8acab46c9b0ef0761d4731e2749ca719d1725c570de0f43c8f13c2f07d948b06c171928a86a169911a459614a519515254551342d0758328c6344c9314c4b0ac1b"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b4da6d369b6db69b6db4d36d36d349249a4926924934924d36da4926db491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 52), (facetIndex 100)]))
 (.leaf ([(facetIndex 41), (facetIndex 59), (facetIndex 103)])))
 (.branch 3
 (.leaf ([(facetIndex 65), (facetIndex 79), (facetIndex 106)]))
 (.branch 4
 (.leaf ([(facetIndex 72), (facetIndex 94), (facetIndex 109)]))
 (.leaf ([(facetIndex 35), (facetIndex 74), (facetIndex 75)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 76), (facetIndex 99), (facetIndex 102)]))
 (.leaf ([(facetIndex 86), (facetIndex 105), (facetIndex 108)])))
 (.branch 8
 (.leaf ([(facetIndex 32), (facetIndex 34), (facetIndex 43), (facetIndex 44), (facetIndex 80), (facetIndex 84), (facetIndex 85), (facetIndex 87), (facetIndex 95), (facetIndex 96)]))
 (.branch 9
 (.leaf ([(facetIndex 42), (facetIndex 78), (facetIndex 88), (facetIndex 89), (facetIndex 91), (facetIndex 93), (facetIndex 97)]))
 (.leaf ([(facetIndex 46), (facetIndex 82), (facetIndex 92)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "360260150050877389808876770907280544030000002000001000000000000907781000004707z20;"⟩
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
def grouped3_0010 : List Nat := [5, 6]
def grouped3_0011 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [7, 8, 9]
def grouped3_0014 : List Nat := [8]
def grouped3_0015 : List Nat := [8, 9]
def grouped3_0016 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record011" 46

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record011" "{\"ridges\":[[27,524],[42,548],[46,770],[46,772],[52,770],[52,777],[59,770],[59,801],[64,524],[65,772],[65,777],[72,772],[72,801],[83,524],[85,270],[85,770],[85,772],[91,534],[91,772],[93,582],[96,770],[96,772],[97,646],[97,772],[100,792],[103,770],[103,928],[106,772],[106,792],[107,524],[109,928]],\"owners\":[[27,524,[34,65,80,84,85,106],[64,83,107]],[64,524,[80,84,85,106],[27,34,65,83,107]],[83,524,[65,106],[27,34,64,80,84,85,107]],[107,524,[34,65,80,85,106],[27,64,83,84]],[42,548,[27,107,109],[64,72,83,93,95,96]],[85,270,[33,79],[]],[46,770,[100,103],[52,59,85,91,96,97]],[52,770,[91,96,97,103],[46,59,85,100]],[59,770,[85,91,97,100],[46,52,96,103]],[85,770,[59,103],[46,52,91,96,97,100]],[96,770,[52,100],[46,59,85,91,97,103]],[103,770,[46,52,85,91,100],[59,96,97]],[46,772,[106,109],[65,72,85,91,96,97]],[65,772,[91,96,97,109],[46,72,85,106]],[72,772,[85,91,97,106],[46,65,96,109]],[85,772,[72,109],[46,65,91,96,97,106]],[91,772,[65,72,109],[46,85,96,97,106]],[96,772,[65,106],[46,72,85,91,97,109]],[97,772,[65,72,106],[46,85,91,96,109]],[106,772,[46,72,96,97,109],[65,85,91]],[52,777,[65],[]],[65,777,[52],[]],[59,801,[72],[]],[72,801,[59],[]],[91,534,[80],[]],[93,582,[84],[]],[97,646,[95],[]],[100,792,[106],[]],[106,792,[100],[]],[103,928,[109],[]],[109,928,[103],[]]],\"edges\":[[23,[27,34,42,46,64,65,72,80,83,84,85,91,93,95,96,97,106,107,109]],[44,[46,52,59,65,72,85,91,96,97,100,103,106,109]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,3,9,12,14,15,23],[-8,12,14,15,23],[-13,9,23],[-24,3,9,12,15,23],[-4,1,24,25],[-15,2,11],[-5,21,22],[-6,16,19,20,22],[-7,15,16,20,21],[-15,7,22],[-19,6,21],[-22,5,6,15,16,21],[-5,23,25],[-9,16,19,20,25],[-10,15,16,20,23],[-15,10,25],[-16,9,10,25],[-19,9,23],[-20,9,10,23],[-23,5,10,19,20,25],[-6,9],[-9,6],[-7,10],[-10,7],[-16,12],[-17,14],[-20,18],[-21,23],[-23,21],[-22,25],[-25,22],[-2,26],[-6,26],[-21,26],[-7,27],[-22,27],[-9,28],[-11,28],[-23,28],[-10,29],[-25,29],[-3,30],[-12,30],[-14,30],[-15,30],[-18,30],[-19,30],[-16,31],[-20,31],[-5,32],[-27,33],[-26,33],[-26,-27,34],[-29,35],[-35,36],[-28,36],[-28,-35,37],[-36,38],[-33,38],[-33,-36,39],[-33,-37,40],[-34,-36,40],[-32,41],[-31,41],[-41,42],[-30,42],[-30,-41,43],[-42,44],[-43,45],[-38,-45,46],[-39,-44,46],[-40,46],[-46],[1,3,4,5,8,9,10,12,13,14,15,16,17,18,19,20,23,24,25],[5,6,7,9,10,15,16,19,20,21,22,23,25]],\"atoms\":[{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":524,\"a\":27,\"owners\":[34,65,80,84,85,106]},{\"tag\":\"mate\",\"ridge\":524,\"a\":64,\"owners\":[80,84,85,106]},{\"tag\":\"mate\",\"ridge\":524,\"a\":83,\"owners\":[65,106]},{\"tag\":\"mate\",\"ridge\":524,\"a\":107,\"owners\":[34,65,80,85,106]},{\"tag\":\"mate\",\"ridge\":548,\"a\":42,\"owners\":[27,107,109]},{\"tag\":\"mate\",\"ridge\":270,\"a\":85,\"owners\":[33,79]},{\"tag\":\"mate\",\"ridge\":770,\"a\":46,\"owners\":[100,103]},{\"tag\":\"mate\",\"ridge\":770,\"a\":52,\"owners\":[91,96,97,103]},{\"tag\":\"mate\",\"ridge\":770,\"a\":59,\"owners\":[85,91,97,100]},{\"tag\":\"mate\",\"ridge\":770,\"a\":85,\"owners\":[59,103]},{\"tag\":\"mate\",\"ridge\":770,\"a\":96,\"owners\":[52,100]},{\"tag\":\"mate\",\"ridge\":770,\"a\":103,\"owners\":[46,52,85,91,100]},{\"tag\":\"mate\",\"ridge\":772,\"a\":46,\"owners\":[106,109]},{\"tag\":\"mate\",\"ridge\":772,\"a\":65,\"owners\":[91,96,97,109]},{\"tag\":\"mate\",\"ridge\":772,\"a\":72,\"owners\":[85,91,97,106]},{\"tag\":\"mate\",\"ridge\":772,\"a\":85,\"owners\":[72,109]},{\"tag\":\"mate\",\"ridge\":772,\"a\":91,\"owners\":[65,72,109]},{\"tag\":\"mate\",\"ridge\":772,\"a\":96,\"owners\":[65,106]},{\"tag\":\"mate\",\"ridge\":772,\"a\":97,\"owners\":[65,72,106]},{\"tag\":\"mate\",\"ridge\":772,\"a\":106,\"owners\":[46,72,96,97,109]},{\"tag\":\"mate\",\"ridge\":777,\"a\":52,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":777,\"a\":65,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":801,\"a\":59,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":801,\"a\":72,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":534,\"a\":91,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":582,\"a\":93,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":646,\"a\":97,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":792,\"a\":100,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":792,\"a\":106,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":928,\"a\":103,\"owners\":[109]},{\"tag\":\"mate\",\"ridge\":928,\"a\":109,\"owners\":[103]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":33,\"full_literals\":[-2,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":52,\"full_literals\":[-6,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":100,\"full_literals\":[-21,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":59,\"full_literals\":[-7,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":103,\"full_literals\":[-22,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-9,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":79,\"full_literals\":[-11,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":106,\"full_literals\":[-23,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-10,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":109,\"full_literals\":[-25,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":34,\"full_literals\":[-3,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":80,\"full_literals\":[-12,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-14,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":85,\"full_literals\":[-15,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":95,\"full_literals\":[-18,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":96,\"full_literals\":[-19,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":91,\"full_literals\":[-16,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":97,\"full_literals\":[-20,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":46,\"full_literals\":[-5,32]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-26,-27,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-28,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-33,-36,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-33,-37,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-34,-36,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-30,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-30,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-38,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[27,34,42,46,64,65,72,80,83,84,85,91,93,95,96,97,106,107,109]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[46,52,59,65,72,85,91,96,97,100,103,106,109]}]}"
  "76 -40 0 73 72 0\n77 38 0 58 59 55 56 51 52 54 37 38 39 35 36 32 33 34 40 41 17 18 6 13 19 75 0\n78 -45 0 77 73 70 0\n79 -43 0 78 69 0\n80 36 30 0 46 27 44 26 43 25 47 45 42 55 56 54 37 39 40 41 3 1 13 4 2 5 74 0\n81 30 39 0 43 45 46 47 25 27 80 60 51 52 35 36 33 34 24 31 22 7 29 75 0\n82 33 41 0 64 49 48 63 50 51 52 35 36 33 34 24 31 10 11 22 29 75 0\n83 39 0 79 81 67 63 64 50 48 49 82 60 55 56 54 37 39 40 41 18 21 28 16 23 30 75 0\n84 -44 0 83 73 71 0\n85 -42 0 84 68 0\n86 -41 0 85 65 0\n87 -30 0 85 66 0\n88 -32 0 86 63 0\n89 -31 0 86 64 0\n90 33 0 86 82 0\n91 -15 0 87 45 0\n92 -19 0 87 47 0\n93 36 0 87 80 0\n94 -5 0 88 50 0\n95 -16 0 89 48 0\n96 -20 0 89 49 0\n97 -37 0 90 76 61 0\n98 -34 0 93 76 62 0\n99 21 23 25 10 6 9 22 0 95 91 96 94 92 75 9 0\n100 23 25 0 92 96 91 95 30 8 14 28 15 99 0\n101 -23 25 0 97 94 92 96 20 39 40 57 54 0\n102 25 0 100 101 0\n103 22 0 102 31 0\n104 27 0 103 36 0\n105 -26 0 104 98 53 0\n106 -6 0 105 33 0\n107 -21 0 105 34 0\n108 0 106 107 94 91 95 103 12 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record016
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "6d0ec1f1b25cb8a6a8ea9687a698e6659362d876338ae1ba1e1783ecc5b15c789ca5a93a6598e479694e5655352d4cd8745d0f78368d6338d9394d534ccb31cf0ba2d8b92ccb4acab1ae1b16c3b61cc749ca719e1745c970de0f0bc1f1d0ac1b3121588e139a1c45311c4a91a4a5194550d48d1342dc0d8384d1314e0b22c4b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a4db6db6db6924d34936936926926924da49349249a49349a492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 57), (facetIndex 70), (facetIndex 81), (facetIndex 82), (facetIndex 83)]))
 (.leaf ([(facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 64)])))
 (.branch 3
 (.leaf ([(facetIndex 40), (facetIndex 69), (facetIndex 72), (facetIndex 73), (facetIndex 78)]))
 (.leaf ([(facetIndex 33), (facetIndex 42), (facetIndex 50), (facetIndex 68), (facetIndex 77), (facetIndex 89), (facetIndex 104)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 34), (facetIndex 46), (facetIndex 51), (facetIndex 54)]))
 (.leaf ([(facetIndex 32), (facetIndex 39), (facetIndex 45), (facetIndex 65), (facetIndex 66), (facetIndex 74), (facetIndex 85), (facetIndex 103)])))
 (.branch 7
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 58), (facetIndex 59), (facetIndex 60)]))
 (.leaf ([(facetIndex 35), (facetIndex 47), (facetIndex 48), (facetIndex 55), (facetIndex 63), (facetIndex 87), (facetIndex 88), (facetIndex 90)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "3a000000001dfe28000098152013169e06d80f098c7f282c2bb6f1dz18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 49), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 99), (facetIndex 100)])))
 (.branch 3
 (.leaf ([(facetIndex 44), (facetIndex 67), (facetIndex 75), (facetIndex 76)]))
 (.branch 4
 (.leaf ([(facetIndex 41), (facetIndex 56), (facetIndex 71)]))
 (.leaf ([(facetIndex 84), (facetIndex 86), (facetIndex 97)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 91), (facetIndex 92), (facetIndex 93)]))
 (.leaf ([(facetIndex 95), (facetIndex 102), (facetIndex 105)])))
 (.branch 8
 (.leaf ([(facetIndex 61), (facetIndex 62), (facetIndex 96)]))
 (.branch 9
 (.leaf ([(facetIndex 94), (facetIndex 101)]))
 (.leaf ([(facetIndex 98)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "60068119476855500004040000000220003000200007700003000000000002003z29;"⟩
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
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7]
def grouped2_0010 : List Nat := [7]
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record016" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record016" 71

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record016" "{\"ridges\":[[6,521],[8,273],[9,530],[23,273],[28,274],[34,521],[38,530],[46,522],[46,529],[51,522],[53,521],[54,521],[57,304],[59,530],[63,416],[70,304],[71,273],[75,568],[79,808],[81,273],[81,304],[82,304],[83,304],[105,404]],\"owners\":[[6,521,[67,75,76,79,80],[34,46,51,53,54]],[34,521,[75,76,79,80],[6,46,51,53,54,67]],[53,521,[67,75,76,79],[6,34,46,51,54,80]],[54,521,[67,75,76],[6,34,46,51,53,79,80]],[46,522,[100],[6,34,51,53,54,86,97]],[51,522,[86,100],[6,34,46,53,54,97]],[28,274,[8,37,57,58,60,92,93,101,102],[]],[46,529,[23,83],[9,38,59,67,75,76]],[9,530,[28,86,97],[38,46,59]],[38,530,[28,97],[9,46,59,86]],[59,530,[28,86],[9,38,46,97]],[57,304,[105],[22,70,81,82,83,92,101,102]],[70,304,[101,102],[22,57,81,82,83,92,105]],[81,304,[92,102,105],[22,57,70,82,83,101]],[82,304,[92,101],[22,57,70,81,83,102,105]],[83,304,[92,101,102,105],[22,57,70,81,82]],[63,416,[105],[24,73,78,82,95,99,102]],[105,404,[71,93],[]],[75,568,[],[]],[79,808,[],[]]],\"edges\":[[29,[6,34,46,51,53,54,67,75,76,79,80,86,97,100]],[34,[9,23,28,38,46,59,67,75,76,83,86,97]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record016" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record016\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-24,-17],[-29,-18],[-31,-24],[-36,-7],[-36,-11],[-36,-12],[-36,-16],[-36,-33],[-36,-34],[-36,-35],[-40,-7],[-40,-11],[-40,-12],[-40,-16],[-40,-33],[-40,-34],[-40,-35],[-41,-7],[-41,-11],[-41,-12],[-41,-16],[-41,-33],[-41,-34],[-41,-35],[-42,-8],[-42,-20],[-42,-23],[-42,-30],[-42,-36],[-42,-41],[-1,22,25,26,27,28],[-6,25,26,27,28],[-14,22,25,26,27],[-15,22,25,26],[-10,39],[-13,32,39],[-2,-24,-29],[-4,-24,-29],[-5,2,8,17,18,20,36,37,40,41],[-10,4,31],[-3,5,32,38],[-9,5,38],[-19,5,32],[-17,42],[-23,40,41],[-29,36,41,42],[-30,36,40],[-31,36,40,41,42],[-21,42],[-42,24,37],[-25],[-27],[-43,17,23,29,30,31],[-44,7,11,12,16,21,33,34,35],[-45,43],[-46,45],[-47,44],[-48,47],[-49,46],[-49,48],[49],[-28,50],[-39,51],[-22,52],[-26,52],[-24,53],[-32,54],[-38,54],[-36,55],[-37,55],[-41,56],[-42,56],[-40,57],[-51,58],[-50,58],[-54,59],[-53,59],[-53,-54,60],[-59,61],[-60,62],[-52,61],[-52,-59,62],[-61,63],[-62,64],[-58,63],[-56,65],[-55,65],[-55,-56,66],[-57,67],[-67,68],[-65,69],[-65,-68,70],[-66,70],[-63,-70,71],[-64,-69,71],[-71],[1,6,10,13,14,15,22,25,26,27,28,32,38,39],[3,4,5,9,10,19,22,25,26,31,32,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":71,\"b\":57},{\"tag\":\"incompatible\",\"a\":81,\"b\":58},{\"tag\":\"incompatible\",\"a\":83,\"b\":71},{\"tag\":\"incompatible\",\"a\":92,\"b\":35},{\"tag\":\"incompatible\",\"a\":92,\"b\":47},{\"tag\":\"incompatible\",\"a\":92,\"b\":48},{\"tag\":\"incompatible\",\"a\":92,\"b\":55},{\"tag\":\"incompatible\",\"a\":92,\"b\":87},{\"tag\":\"incompatible\",\"a\":92,\"b\":88},{\"tag\":\"incompatible\",\"a\":92,\"b\":90},{\"tag\":\"incompatible\",\"a\":101,\"b\":35},{\"tag\":\"incompatible\",\"a\":101,\"b\":47},{\"tag\":\"incompatible\",\"a\":101,\"b\":48},{\"tag\":\"incompatible\",\"a\":101,\"b\":55},{\"tag\":\"incompatible\",\"a\":101,\"b\":87},{\"tag\":\"incompatible\",\"a\":101,\"b\":88},{\"tag\":\"incompatible\",\"a\":101,\"b\":90},{\"tag\":\"incompatible\",\"a\":102,\"b\":35},{\"tag\":\"incompatible\",\"a\":102,\"b\":47},{\"tag\":\"incompatible\",\"a\":102,\"b\":48},{\"tag\":\"incompatible\",\"a\":102,\"b\":55},{\"tag\":\"incompatible\",\"a\":102,\"b\":87},{\"tag\":\"incompatible\",\"a\":102,\"b\":88},{\"tag\":\"incompatible\",\"a\":102,\"b\":90},{\"tag\":\"incompatible\",\"a\":105,\"b\":37},{\"tag\":\"incompatible\",\"a\":105,\"b\":60},{\"tag\":\"incompatible\",\"a\":105,\"b\":70},{\"tag\":\"incompatible\",\"a\":105,\"b\":82},{\"tag\":\"incompatible\",\"a\":105,\"b\":92},{\"tag\":\"incompatible\",\"a\":105,\"b\":102},{\"tag\":\"mate\",\"ridge\":521,\"a\":6,\"owners\":[67,75,76,79,80]},{\"tag\":\"mate\",\"ridge\":521,\"a\":34,\"owners\":[75,76,79,80]},{\"tag\":\"mate\",\"ridge\":521,\"a\":53,\"owners\":[67,75,76,79]},{\"tag\":\"mate\",\"ridge\":521,\"a\":54,\"owners\":[67,75,76]},{\"tag\":\"mate\",\"ridge\":522,\"a\":46,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":522,\"a\":51,\"owners\":[86,100]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[8,71,81]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[23,71,81]},{\"tag\":\"mate\",\"ridge\":274,\"a\":28,\"owners\":[8,37,57,58,60,92,93,101,102]},{\"tag\":\"mate\",\"ridge\":529,\"a\":46,\"owners\":[23,83]},{\"tag\":\"mate\",\"ridge\":530,\"a\":9,\"owners\":[28,86,97]},{\"tag\":\"mate\",\"ridge\":530,\"a\":38,\"owners\":[28,97]},{\"tag\":\"mate\",\"ridge\":530,\"a\":59,\"owners\":[28,86]},{\"tag\":\"mate\",\"ridge\":304,\"a\":57,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":304,\"a\":70,\"owners\":[101,102]},{\"tag\":\"mate\",\"ridge\":304,\"a\":81,\"owners\":[92,102,105]},{\"tag\":\"mate\",\"ridge\":304,\"a\":82,\"owners\":[92,101]},{\"tag\":\"mate\",\"ridge\":304,\"a\":83,\"owners\":[92,101,102,105]},{\"tag\":\"mate\",\"ridge\":416,\"a\":63,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":404,\"a\":105,\"owners\":[71,93]},{\"tag\":\"mate\",\"ridge\":568,\"a\":75,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":808,\"a\":79,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[57,70,81,82,83],\"full_literals\":[-43,17,23,29,30,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[35,47,48,55,63,87,88,90],\"full_literals\":[-44,7,11,12,16,21,33,34,35]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-46,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-49,46,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-49,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":80,\"full_literals\":[-28,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":100,\"full_literals\":[-39,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-22,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":76,\"full_literals\":[-26,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-24,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":86,\"full_literals\":[-32,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":97,\"full_literals\":[-38,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":92,\"full_literals\":[-36,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":93,\"full_literals\":[-37,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":102,\"full_literals\":[-41,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":105,\"full_literals\":[-42,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":101,\"full_literals\":[-40,57]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-54,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-59,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-56,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-68,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-63,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[6,34,46,51,53,54,67,75,76,79,80,86,97,100]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[9,23,28,38,46,59,67,75,76,83,86,97]}]}"
  "99 46 0 61 59 0\n100 48 0 61 60 0\n101 45 0 99 56 0\n102 47 0 100 58 0\n103 43 0 101 55 0\n104 44 0 102 57 0\n105 1 6 10 13 14 15 22 26 28 32 38 39 0 51 52 97 0\n106 3 4 5 9 10 19 22 26 31 32 38 0 51 98 0\n107 63 0 52 51 83 85 79 81 74 75 76 64 65 63 62 67 68 31 32 33 34 35 36 105 0\n108 -70 0 107 96 94 0\n109 -66 0 108 93 0\n110 40 65 0 103 86 72 71 87 69 46 44 45 48 47 53 0\n111 65 0 104 86 72 49 110 11 12 13 14 15 16 17 54 0\n112 -68 0 111 108 92 0\n113 -67 0 112 90 0\n114 -57 0 113 89 0\n115 -40 0 114 73 0\n116 36 41 42 0 115 103 45 44 46 48 47 53 0\n117 -36 21 0 104 4 5 6 7 8 9 10 54 0\n118 42 0 104 49 117 116 18 19 20 21 22 23 24 54 0\n119 -8 0 118 25 0\n120 -20 0 118 26 0\n121 -23 0 118 27 0\n122 -30 0 118 28 0\n123 -36 0 118 29 0\n124 -41 0 118 30 0\n125 56 0 118 72 0\n126 -55 0 125 109 88 0\n127 -37 0 126 70 0\n128 24 0 127 118 50 0\n129 -17 0 128 1 0\n130 -31 0 128 3 0\n131 53 0 128 66 0\n132 29 0 130 103 121 122 129 53 0\n133 59 0 131 77 0\n134 -18 0 132 2 0\n135 -2 0 132 128 37 0\n136 -4 0 132 128 38 0\n137 -5 0 135 115 129 119 120 134 123 127 124 39 0\n138 -10 0 136 130 40 0\n139 62 0 131 133 130 138 136 137 80 78 82 67 68 64 65 41 42 43 106 0\n140 69 0 111 91 0\n141 64 0 139 84 0\n142 0 141 140 96 95 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record020
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3e0bc1f3926c8f26a96a3a8da2e87a958b61db0e4b8ae1b89e1783ee47316c4f15a4e9364b91e725956352d70d4b4ad2745d0f78368d6338f13a4d9394cd34ccb31cf0b52ccb4acab1ac9b16c3bc1e4749ca719c970de0f43c8f0bc1f6a0741b18a85856139a12c471625292a46919615154351342dc0d8384c9314d0b22c4b81c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b4db4db6d34db4d36d249a4d24d26924da49269249249349b492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 65), (facetIndex 71), (facetIndex 72), (facetIndex 80)]))
 (.leaf ([(facetIndex 32), (facetIndex 38), (facetIndex 42), (facetIndex 57), (facetIndex 73), (facetIndex 93)])))
 (.branch 3
 (.leaf ([(facetIndex 35), (facetIndex 43), (facetIndex 52), (facetIndex 64)]))
 (.leaf ([(facetIndex 58), (facetIndex 60), (facetIndex 81)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 68), (facetIndex 69), (facetIndex 75), (facetIndex 76), (facetIndex 78), (facetIndex 79)]))
 (.leaf ([(facetIndex 33), (facetIndex 39), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 53), (facetIndex 54), (facetIndex 63), (facetIndex 87), (facetIndex 91), (facetIndex 99)])))
 (.branch 7
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 66), (facetIndex 85), (facetIndex 103)]))
 (.branch 8
 (.leaf ([(facetIndex 56), (facetIndex 59)]))
 (.leaf ([(facetIndex 34), (facetIndex 36), (facetIndex 50), (facetIndex 51)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "600050000010500050600030440440100044060250037317055288555660210051082851z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 70), (facetIndex 74)]))
 (.leaf ([(facetIndex 55), (facetIndex 82), (facetIndex 83)])))
 (.branch 3
 (.leaf ([(facetIndex 89), (facetIndex 90)]))
 (.branch 4
 (.leaf ([(facetIndex 101), (facetIndex 102)]))
 (.leaf ([(facetIndex 44), (facetIndex 67), (facetIndex 77)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 84), (facetIndex 86), (facetIndex 96)]))
 (.leaf ([(facetIndex 94), (facetIndex 104), (facetIndex 105)])))
 (.branch 8
 (.leaf ([(facetIndex 40), (facetIndex 61), (facetIndex 62), (facetIndex 95)]))
 (.branch 9
 (.leaf ([(facetIndex 88), (facetIndex 97), (facetIndex 98)]))
 (.leaf ([(facetIndex 92), (facetIndex 100)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "660339088576090228050511000040000000004000077000001000000000040007z28;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7, 8]
def grouped2_0010 : List Nat := [7]
def grouped2_0011 : List Nat := [7, 8]
def grouped2_0012 : List Nat := [8]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0015 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [2, 3, 4]
def grouped3_0020 : List Nat := [3]
def grouped3_0021 : List Nat := [3, 4]
def grouped3_0022 : List Nat := [4]
def grouped3_0023 : List Nat := [5]
def grouped3_0024 : List Nat := [5, 6]
def grouped3_0025 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0026 : List Nat := [6]
def grouped3_0027 : List Nat := [7]
def grouped3_0028 : List Nat := [7, 8, 9]
def grouped3_0029 : List Nat := [8]
def grouped3_0030 : List Nat := [8, 9]
def grouped3_0031 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record020" "{\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record020" 80

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record020" "{\"ridges\":[[2,7],[8,146],[10,259],[11,259],[11,770],[23,176],[34,7],[35,259],[38,146],[39,7],[43,7],[43,259],[43,770],[46,146],[51,259],[52,770],[54,176],[56,67],[56,131],[56,146],[58,146],[59,146],[60,770],[64,770],[67,156],[70,780],[71,176],[74,804],[76,176],[77,216],[80,176],[81,176],[82,816],[83,912],[90,780],[102,770],[102,912]],\"owners\":[[56,67,[2,4,39,42,47,51,62],[7,50,53,57,61]],[56,131,[5,10,34,40,48,63,64],[8,38,50,54,59,61]],[8,146,[86,92,95,96,100,101,102],[38,46,54,56,58,59]],[38,146,[95,96,100,101,102],[8,46,54,56,58,59,86,92]],[46,146,[92,100,101,102],[8,38,54,56,58,59,86,95,96]],[56,146,[86,92,95,101,102],[8,38,46,54,58,59,96,100]],[58,146,[86,92,95,96,100],[8,38,46,54,56,59,101,102]],[59,146,[86,92,95,96,100,101],[8,38,46,54,56,58,102]],[11,770,[90,102],[43,52,60,64]],[43,770,[102],[11,52,60,64,90]],[52,770,[102],[11,43,60,64,90]],[60,770,[90],[11,43,52,64,102]],[64,770,[90],[11,43,52,60,102]],[102,770,[11,43,52,90],[60,64]],[23,176,[92,95,100,101,104,105],[54,71,76,80,81]],[54,176,[104,105],[23,71,76,80,81,92,95,100,101]],[71,176,[95,100,101,105],[23,54,76,80,81,92,104]],[76,176,[92,100,101],[23,54,71,80,81,95,104,105]],[80,176,[92,95,101,104],[23,54,71,76,81,100,105]],[81,176,[92,95,100,104,105],[23,54,71,76,80,101]],[67,156,[86,104],[]],[70,780,[90],[]],[90,780,[70],[]],[74,804,[],[]],[77,216,[96,105],[]],[82,816,[],[]],[83,912,[102],[]],[102,912,[83],[]]],\"edges\":[[32,[8,23,38,46,54,56,58,59,67,71,76,77,80,81,83,86,92,95,96,100,101,102,104,105]],[44,[11,43,52,60,64,70,74,82,83,90,102]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record020" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record020\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-8,-2],[-9,-3],[-9,-8],[-15,-10],[-15,-14],[-17,-8],[-18,-9],[-20,-3],[-20,-8],[-20,-18],[-21,-8],[-21,-10],[-21,-20],[-23,-19],[-39,-28],[-47,-25],[-47,-26],[-47,-29],[-1,-8,-15],[-8,-12,-15],[-23,1,2,12,14,17,20,27],[-23,3,5,8,13,18,28,29],[-5,-6,-9],[-5,-15,-20],[-4,40,42,43,44,45,46,47],[-11,43,44,45,46,47],[-16,42,45,46,47],[-23,40,42,43,46,47],[-24,40,42,43,44,45],[-25,40,42,43,44,45,46],[-6,41,47],[-15,47],[-21,47],[-26,41],[-29,41],[-47,6,15,21,41],[-7,42,43,45,46,48,49],[-22,48,49],[-32,43,45,46,49],[-34,42,45,46],[-36,42,43,46,48],[-37,42,43,45,48,49],[-30,40,48],[-31,41],[-41,31],[-33],[-35,44,49],[-38],[-39,47],[-47,39],[-50,9,15,21,29],[-51,24,26,37],[-52,23,25],[-53,8,10,19,20],[-54,50,51],[-55,51],[-56,54],[-57,55],[-58,52],[-58,53],[-59,58],[-60,59],[-61,56],[-61,57,60],[61],[-31,62],[-39,63],[-41,64],[-46,65],[-47,65],[-40,66],[-44,66],[-48,67],[-49,67],[-13,68],[-27,68],[-43,68],[-42,69],[-45,69],[-63,70],[-62,70],[-65,71],[-71,72],[-64,72],[-64,-71,73],[-70,-72,74],[-70,-73,75],[-67,76],[-66,76],[-69,77],[-77,78],[-68,78],[-78,79],[-76,79],[-74,-79,80],[-75,80],[-80],[4,7,11,16,22,23,24,25,30,32,34,35,36,37,39,40,42,43,44,45,46,47,48,49],[6,15,21,26,29,31,33,38,39,41,47]],\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":34,\"b\":4},{\"tag\":\"incompatible\",\"a\":35,\"b\":5},{\"tag\":\"incompatible\",\"a\":35,\"b\":34},{\"tag\":\"incompatible\",\"a\":43,\"b\":36},{\"tag\":\"incompatible\",\"a\":43,\"b\":42},{\"tag\":\"incompatible\",\"a\":47,\"b\":34},{\"tag\":\"incompatible\",\"a\":48,\"b\":35},{\"tag\":\"incompatible\",\"a\":51,\"b\":5},{\"tag\":\"incompatible\",\"a\":51,\"b\":34},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":34},{\"tag\":\"incompatible\",\"a\":52,\"b\":36},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":56,\"b\":50},{\"tag\":\"incompatible\",\"a\":83,\"b\":63},{\"tag\":\"incompatible\",\"a\":102,\"b\":59},{\"tag\":\"incompatible\",\"a\":102,\"b\":60},{\"tag\":\"incompatible\",\"a\":102,\"b\":64},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[2,34,43]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[34,39,43]},{\"tag\":\"mate\",\"ridge\":67,\"a\":56,\"owners\":[2,4,39,42,47,51,62]},{\"tag\":\"mate\",\"ridge\":131,\"a\":56,\"owners\":[5,10,34,40,48,63,64]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[10,11,35]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[10,43,51]},{\"tag\":\"mate\",\"ridge\":146,\"a\":8,\"owners\":[86,92,95,96,100,101,102]},{\"tag\":\"mate\",\"ridge\":146,\"a\":38,\"owners\":[95,96,100,101,102]},{\"tag\":\"mate\",\"ridge\":146,\"a\":46,\"owners\":[92,100,101,102]},{\"tag\":\"mate\",\"ridge\":146,\"a\":56,\"owners\":[86,92,95,101,102]},{\"tag\":\"mate\",\"ridge\":146,\"a\":58,\"owners\":[86,92,95,96,100]},{\"tag\":\"mate\",\"ridge\":146,\"a\":59,\"owners\":[86,92,95,96,100,101]},{\"tag\":\"mate\",\"ridge\":770,\"a\":11,\"owners\":[90,102]},{\"tag\":\"mate\",\"ridge\":770,\"a\":43,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":770,\"a\":52,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":770,\"a\":60,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":770,\"a\":64,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":770,\"a\":102,\"owners\":[11,43,52,90]},{\"tag\":\"mate\",\"ridge\":176,\"a\":23,\"owners\":[92,95,100,101,104,105]},{\"tag\":\"mate\",\"ridge\":176,\"a\":54,\"owners\":[104,105]},{\"tag\":\"mate\",\"ridge\":176,\"a\":71,\"owners\":[95,100,101,105]},{\"tag\":\"mate\",\"ridge\":176,\"a\":76,\"owners\":[92,100,101]},{\"tag\":\"mate\",\"ridge\":176,\"a\":80,\"owners\":[92,95,101,104]},{\"tag\":\"mate\",\"ridge\":176,\"a\":81,\"owners\":[92,95,100,104,105]},{\"tag\":\"mate\",\"ridge\":156,\"a\":67,\"owners\":[86,104]},{\"tag\":\"mate\",\"ridge\":780,\"a\":70,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":780,\"a\":90,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":804,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":216,\"a\":77,\"owners\":[96,105]},{\"tag\":\"mate\",\"ridge\":816,\"a\":82,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":912,\"a\":83,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":912,\"a\":102,\"owners\":[83]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[35,43,52,64],\"full_literals\":[-50,9,15,21,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[58,60,81],\"full_literals\":[-51,24,26,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[56,59],\"full_literals\":[-52,23,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[34,36,50,51],\"full_literals\":[-53,8,10,19,20]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,50,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-60,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-61,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-61,57,60],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-31,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-39,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":90,\"full_literals\":[-41,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":101,\"full_literals\":[-46,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":102,\"full_literals\":[-47,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":86,\"full_literals\":[-40,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":96,\"full_literals\":[-44,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":104,\"full_literals\":[-48,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":105,\"full_literals\":[-49,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":40,\"full_literals\":[-13,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":62,\"full_literals\":[-27,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":95,\"full_literals\":[-43,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":92,\"full_literals\":[-42,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":100,\"full_literals\":[-45,69]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-71,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-70,-72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-70,-73,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-74,-79,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":32,\"owners\":[8,23,38,46,54,56,58,59,67,71,76,77,80,81,83,86,92,95,96,100,101,102,104,105]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[11,43,52,60,64,70,74,82,83,90,102]}]}"
  "100 56 0 65 63 0\n101 54 0 100 57 0\n102 -75 0 97 96 0\n103 6 15 21 26 29 31 39 41 47 0 46 48 99 0\n104 41 47 0 31 34 35 44 32 33 49 103 0\n105 72 0 83 84 82 68 70 104 0\n106 70 0 80 81 67 66 50 45 104 0\n107 74 0 106 105 86 0\n108 -73 0 106 102 87 0\n109 -79 0 107 97 95 0\n110 -78 0 109 93 0\n111 -76 0 109 94 0\n112 -77 0 110 91 0\n113 -68 0 110 92 0\n114 -67 0 111 88 0\n115 -66 0 111 89 0\n116 -69 0 112 90 0\n117 -13 0 113 75 0\n118 -27 0 113 76 0\n119 -43 0 113 77 0\n120 -48 0 114 73 0\n121 -49 0 114 74 0\n122 -40 0 115 71 0\n123 -44 0 115 72 0\n124 -42 0 116 78 0\n125 -45 0 116 79 0\n126 -22 0 120 121 38 0\n127 -30 0 122 120 43 0\n128 -35 0 123 121 47 0\n129 -24 0 124 122 119 123 125 29 0\n130 -37 0 125 119 124 120 121 42 0\n131 47 0 108 121 120 125 123 119 124 122 130 128 127 126 129 49 104 68 85 82 69 27 37 40 41 28 25 30 26 39 98 0\n132 -25 0 131 16 0\n133 -26 0 131 17 0\n134 -29 0 131 18 0\n135 39 0 131 50 0\n136 65 0 131 70 0\n137 -51 0 133 130 129 52 0\n138 -28 0 135 15 0\n139 71 0 136 82 0\n140 -55 0 137 56 0\n141 50 0 137 101 55 0\n142 -64 0 139 108 85 0\n143 -57 0 140 58 0\n144 -41 0 142 68 0\n145 60 0 143 65 64 0\n146 59 0 145 62 0\n147 58 0 146 61 0\n148 52 0 147 59 0\n149 53 0 147 60 0\n150 23 0 148 132 53 0\n151 -19 0 150 14 0\n152 -6 -9 0 150 117 138 134 23 2 3 7 22 0\n153 15 21 0 141 134 131 144 36 51 152 0\n154 8 18 -15 0 149 151 134 138 117 150 4 54 8 24 22 0\n155 -8 -15 0 150 118 5 1 6 9 19 20 21 0\n156 -15 0 149 151 4 155 54 154 10 0\n157 21 0 156 153 0\n158 -8 0 157 11 0\n159 -10 0 157 12 0\n160 -20 0 157 13 0\n161 0 160 158 151 159 149 54 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record026
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e4b8aa6a5a36a3a2e87a65956359362d876c398e338aee4789a6659366392e47965555355352d475c358d334ade0e9394d5334e334ccb3c2e8b62e4b32e2b2ae1b26c5b0ef0751cc749ca745c9715c3783d0f1b312648721a9861988e1382ec45911c469614652344d0b70360c6384d1324c530ce0b22c4b0ad0721c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "136db6936da6924db6da4db69a492492492492492492492492249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 76), (facetIndex 94)]))
 (.leaf ([(facetIndex 36), (facetIndex 66), (facetIndex 67), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 56), (facetIndex 64), (facetIndex 65), (facetIndex 83), (facetIndex 101)]))
 (.leaf ([(facetIndex 84), (facetIndex 85), (facetIndex 86)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 70), (facetIndex 75), (facetIndex 88), (facetIndex 93)]))
 (.leaf ([(facetIndex 37), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46)])))
 (.branch 7
 (.leaf ([(facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 57)]))
 (.leaf ([(facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 63)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "100000200040db400000800101252fffff2db6c0016db64929z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

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

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record026" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record026" 50

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record026" "{\"ridges\":[[8,521],[50,521],[52,521],[54,521],[57,521],[87,780],[98,600],[99,664],[100,904]],\"owners\":[[8,521,[69,78,80,81,82],[37,50,52,54,56,57]],[50,521,[69,82],[8,37,52,54,56,57,78,80,81]],[52,521,[69,80,81,82],[8,37,50,54,56,57,78]],[54,521,[69,78,81,82],[8,37,50,52,56,57,80]],[57,521,[78,80,81],[8,37,50,52,54,56,69,82]],[87,780,[69],[]],[98,600,[80],[]],[99,664,[81],[]],[100,904,[82],[]]],\"edges\":[[29,[8,37,50,52,54,56,57,69,78,80,81,82,87,96,98,99,100]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record026" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record026\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-8,-3],[-9,-3],[-10,-3],[-11,-3],[-11,-5],[-11,-6],[-12,-3],[-13,-8],[-13,-9],[-13,-10],[-13,-11],[-13,-12],[-14,-3],[-14,-13],[-15,-4],[-15,-5],[-15,-6],[-16,-4],[-16,-5],[-16,-6],[-17,-4],[-17,-5],[-17,-6],[-18,-4],[-18,-5],[-18,-6],[-19,-4],[-19,-5],[-19,-6],[-20,-4],[-20,-5],[-20,-6],[-21,-15],[-21,-16],[-21,-17],[-21,-18],[-21,-19],[-21,-20],[-26,-2],[-26,-23],[-26,-24],[-26,-25],[-28,-27],[-29,-5],[-29,-6],[-29,-27],[-30,-27],[-31,-22],[-32,-31],[-34,-28],[-34,-29],[-34,-30],[-35,-27],[-35,-34],[-39,-31],[-1,26,28,29,30,31],[-7,26,31],[-9,26,29,30,31],[-11,26,28,30,31],[-14,28,29,30],[-33,26],[-36,29],[-37,30],[-38,31],[-40,4,5,6,7,27,34],[-41,2,23,24,25],[-42,13,21,22,32,39],[-43,8,9,10,11,12,14],[-44,15,16,17,18,19,20],[-45,40],[-45,41],[-46,42],[-47,45],[-47,46],[-48,43],[-48,44],[-49,48],[-50,47],[-50,49],[50],[1,3,7,9,11,13,14,26,28,29,30,31,33,35,36,37,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":51,\"b\":37},{\"tag\":\"incompatible\",\"a\":52,\"b\":37},{\"tag\":\"incompatible\",\"a\":53,\"b\":37},{\"tag\":\"incompatible\",\"a\":54,\"b\":37},{\"tag\":\"incompatible\",\"a\":54,\"b\":48},{\"tag\":\"incompatible\",\"a\":54,\"b\":49},{\"tag\":\"incompatible\",\"a\":55,\"b\":37},{\"tag\":\"incompatible\",\"a\":56,\"b\":51},{\"tag\":\"incompatible\",\"a\":56,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":37},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":47},{\"tag\":\"incompatible\",\"a\":58,\"b\":48},{\"tag\":\"incompatible\",\"a\":58,\"b\":49},{\"tag\":\"incompatible\",\"a\":59,\"b\":47},{\"tag\":\"incompatible\",\"a\":59,\"b\":48},{\"tag\":\"incompatible\",\"a\":59,\"b\":49},{\"tag\":\"incompatible\",\"a\":60,\"b\":47},{\"tag\":\"incompatible\",\"a\":60,\"b\":48},{\"tag\":\"incompatible\",\"a\":60,\"b\":49},{\"tag\":\"incompatible\",\"a\":61,\"b\":47},{\"tag\":\"incompatible\",\"a\":61,\"b\":48},{\"tag\":\"incompatible\",\"a\":61,\"b\":49},{\"tag\":\"incompatible\",\"a\":62,\"b\":47},{\"tag\":\"incompatible\",\"a\":62,\"b\":48},{\"tag\":\"incompatible\",\"a\":62,\"b\":49},{\"tag\":\"incompatible\",\"a\":63,\"b\":47},{\"tag\":\"incompatible\",\"a\":63,\"b\":48},{\"tag\":\"incompatible\",\"a\":63,\"b\":49},{\"tag\":\"incompatible\",\"a\":64,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":59},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":69,\"b\":36},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":78,\"b\":76},{\"tag\":\"incompatible\",\"a\":80,\"b\":48},{\"tag\":\"incompatible\",\"a\":80,\"b\":49},{\"tag\":\"incompatible\",\"a\":80,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":76},{\"tag\":\"incompatible\",\"a\":82,\"b\":65},{\"tag\":\"incompatible\",\"a\":83,\"b\":82},{\"tag\":\"incompatible\",\"a\":94,\"b\":78},{\"tag\":\"incompatible\",\"a\":94,\"b\":80},{\"tag\":\"incompatible\",\"a\":94,\"b\":81},{\"tag\":\"incompatible\",\"a\":96,\"b\":76},{\"tag\":\"incompatible\",\"a\":96,\"b\":94},{\"tag\":\"incompatible\",\"a\":101,\"b\":82},{\"tag\":\"mate\",\"ridge\":521,\"a\":8,\"owners\":[69,78,80,81,82]},{\"tag\":\"mate\",\"ridge\":521,\"a\":50,\"owners\":[69,82]},{\"tag\":\"mate\",\"ridge\":521,\"a\":52,\"owners\":[69,80,81,82]},{\"tag\":\"mate\",\"ridge\":521,\"a\":54,\"owners\":[69,78,81,82]},{\"tag\":\"mate\",\"ridge\":521,\"a\":57,\"owners\":[78,80,81]},{\"tag\":\"mate\",\"ridge\":780,\"a\":87,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":600,\"a\":98,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":664,\"a\":99,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":904,\"a\":100,\"owners\":[82]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[47,48,49,50,76,94],\"full_literals\":[-40,4,5,6,7,27,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[36,66,67,68],\"full_literals\":[-41,2,23,24,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[56,64,65,83,101],\"full_literals\":[-42,13,21,22,32,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[51,52,53,54,55,57],\"full_literals\":[-43,8,9,10,11,12,14]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[58,59,60,61,62,63],\"full_literals\":[-44,15,16,17,18,19,20]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-47,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-50,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-50,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[8,37,50,52,54,56,57,69,78,80,81,82,87,96,98,99,100]}]}"
  "82 47 0 80 78 0\n83 49 0 80 79 0\n84 45 0 82 73 0\n85 46 0 82 74 0\n86 48 0 83 77 0\n87 40 0 84 70 0\n88 41 0 84 71 0\n89 42 0 85 72 0\n90 43 0 86 75 0\n91 44 0 86 76 0\n92 -13 0 90 8 9 10 11 12 14 68 0\n93 -21 0 91 33 34 35 36 37 38 69 0\n94 -3 0 90 1 2 3 4 7 13 68 0\n95 -29 4 7 0 87 44 45 46 51 65 0\n96 -11 31 30 4 26 7 0 87 5 6 59 43 50 65 0\n97 -27 11 38 37 31 30 29 33 26 14 7 0 92 94 58 62 43 53 56 81 0\n98 -34 11 38 37 31 30 29 33 26 14 7 0 92 94 58 62 50 54 56 81 0\n99 -5 0 91 16 19 22 25 28 31 69 0\n100 -27 31 30 29 7 26 11 0 64 63 61 43 97 60 0\n101 -34 31 30 29 7 26 11 0 64 63 61 50 98 60 0\n102 -6 0 91 17 20 23 26 29 32 69 0\n103 31 30 7 26 4 11 0 99 102 87 95 100 101 65 0\n104 -31 0 93 92 89 48 49 55 67 0\n105 7 26 11 4 0 87 102 99 104 103 47 52 65 0\n106 26 4 11 0 104 57 105 0\n107 -26 0 88 39 40 41 42 66 0\n108 -7 0 107 104 57 0\n109 -4 0 91 15 18 21 24 27 30 69 0\n110 11 0 109 107 106 0\n111 30 0 110 104 109 107 108 96 0\n112 -27 0 111 47 0\n113 -34 0 111 52 0\n114 0 113 112 87 102 108 99 109 65 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record026
