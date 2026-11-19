module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow30Part00049Data
public import GraphInputsRow30Part00049Frames
public import GraphInputsRow30Part00049Leaves
public import GraphInputsRow30Part00049Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00049.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨96, by decide⟩, ⟨99, by decide⟩, ⟨110, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 16492674416640, (certNat% 3), (certNat% 4), (certNat% 5)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), 7937099563008]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), 7937099563008, 549755813888]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 14), 24561844224, 5050881540096, 3435973836800]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨110, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), (certNat% 18), (certNat% 10)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 18), 7937099563008]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), 7937099563008, 549755813888]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 21), 24561844224, 5050881540096, 3435973836800]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨110, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), 16664473108480, 24645730304]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 4), 16733192585216, (certNat% 26)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), 15133048832, (certNat% 8)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 8), (certNat% 29), (certNat% 30), (certNat% 10)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c21 c19
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), 28017950720, (certNat% 8)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c20 c23
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), 1237621669888, 23689428992]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 30), 1237621669888, 23689428992, (certNat% 29)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c28 c26
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 30), 5738076307456, (certNat% 29), (certNat% 35), 33269219328]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c31 c25
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c32 c22
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c33 c18
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c34 c17
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c35 c16
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c36 c9
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c37 c2
  c38
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00049.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00049.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "cd2745d1ac3b19c8f13c1f3329c9726a8ea66a3a4e87ac9aa669a66598e6c5996959568d9361d98e33a2e4b8ae1ba1e4789e1783e6a4e966725a95a59956539715656555558d3362d4b4ad1b61d4749dc8ea368e6358ce3c4d9394d5362ccb8ad2b2ac6b86d1b26f07a1d8791d4731e2749ca719e1745c9715e0f43c8f13c2f07da42b06c171a22a86a1685961615454552344d0758384d1314c8b12c1b"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6936d36d26da6d36db6db6db6936d36db69b69249369249b4db49249b4924da6db6da4d3693449249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 25), (facetIndex 85), (facetIndex 89), (facetIndex 108), (facetIndex 117)]))
 (.branch 2
 (.leaf ([(facetIndex 50), (facetIndex 69), (facetIndex 112), (facetIndex 121)]))
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 59), (facetIndex 65), (facetIndex 66), (facetIndex 78)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55)]))
 (.leaf ([(facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 71), (facetIndex 72), (facetIndex 73), (facetIndex 74)])))
 (.branch 6
 (.leaf ([(facetIndex 51), (facetIndex 70), (facetIndex 113), (facetIndex 122)]))
 (.leaf ([(facetIndex 23), (facetIndex 26), (facetIndex 29), (facetIndex 31), (facetIndex 32), (facetIndex 40), (facetIndex 90), (facetIndex 105)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1480000290000300000000001800000000801249480949004006dba4049b606000006c30180cz11;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 27), (facetIndex 48), (facetIndex 81), (facetIndex 109)]))
 (.leaf ([(facetIndex 67), (facetIndex 87), (facetIndex 111), (facetIndex 118)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 91), (facetIndex 120)]))
 (.branch 4
 (.leaf ([(facetIndex 84), (facetIndex 110), (facetIndex 114), (facetIndex 115), (facetIndex 116)]))
 (.leaf ([(facetIndex 95), (facetIndex 119), (facetIndex 123), (facetIndex 124), (facetIndex 125)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 24), (facetIndex 49), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 60), (facetIndex 61), (facetIndex 83)]))
 (.branch 7
 (.leaf ([(facetIndex 33), (facetIndex 68), (facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 34), (facetIndex 37), (facetIndex 82)]))))
 (.branch 9
 (.leaf ([(facetIndex 28), (facetIndex 35), (facetIndex 38), (facetIndex 39), (facetIndex 41), (facetIndex 42), (facetIndex 86), (facetIndex 93), (facetIndex 94), (facetIndex 96)]))
 (.branch 10
 (.leaf ([(facetIndex 36), (facetIndex 88), (facetIndex 97), (facetIndex 98), (facetIndex 99), (facetIndex 100), (facetIndex 101), (facetIndex 102), (facetIndex 106)]))
 (.leaf ([(facetIndex 92), (facetIndex 103), (facetIndex 104), (facetIndex 107)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "444002410333001300a90aa9999998488a20091803570660666000000610000055055500000050000008808879876002080005z18;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1, 2]
def grouped2_0004 : List Nat := [3, 4]
def grouped2_0005 : List Nat := [3, 4, 5, 6]
def grouped2_0006 : List Nat := [5]
def grouped2_0007 : List Nat := [5, 6]
def grouped2_0008 : List Nat := [6]
def grouped3_0009 : List Nat := [3]
def grouped3_0010 : List Nat := [3, 4]
def grouped3_0011 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00049.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":123},{\"tag\":\"facet\",\"index\":124},{\"tag\":\"facet\",\"index\":125},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00049.record006" 61

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00049.record006" "{\"ridges\":[[5,530],[12,532],[32,532],[36,548],[49,546],[58,546],[60,546],[61,546],[64,532],[68,548],[72,532],[74,532],[77,548],[79,548],[80,548],[110,568],[115,624],[116,816]],\"owners\":[[5,530,[88,97,99,101,110,115,116],[32,45,53,55]],[12,532,[88,97,99,101,119,124,125],[32,64,72,74]],[32,532,[119,124,125],[12,64,72,74,88,97,99,101]],[64,532,[97,99,101,124,125],[12,32,72,74,88,119]],[72,532,[88,97,101,119,125],[12,32,64,74,99,124]],[74,532,[88,97,99,119,124],[12,32,64,72,101,125]],[49,546,[97,104,106,107,115,116],[36,58,60,61,92,110]],[58,546,[92,97,106,107,110,116],[36,49,60,61,104,115]],[60,546,[92,97,104,107,110,115,116],[36,49,58,61,106]],[61,546,[92,97,104,106,110,115],[36,49,58,60,107,116]],[36,548,[119,124,125],[68,77,79,80,92,97,104,106,107]],[68,548,[97,104,106,107,124,125],[36,77,79,80,92,119]],[77,548,[92,97,106,107,119,125],[36,68,79,80,104,124]],[79,548,[92,97,104,107,119,124,125],[36,68,77,80,106]],[80,548,[92,97,104,106,119,124],[36,68,77,79,107,125]],[110,568,[119],[]],[115,624,[124],[]],[116,816,[125],[]]],\"edges\":[[23,[12,28,32,36,39,41,42,64,68,72,74,77,79,80,88,92,97,99,101,104,106,107,119,124,125]],[34,[5,12,32,45,53,55,64,72,74,88,97,99,101,110,115,116,119,124,125]],[38,[36,49,58,60,61,68,77,79,80,92,97,104,106,107,110,115,116,119,124,125]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00049.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00049.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-4,-3],[-5,-4],[-7,-4],[-8,-4],[-9,-4],[-12,-4],[-15,-3],[-17,-3],[-18,-3],[-22,-3],[-24,-3],[-25,-3],[-30,-3],[-30,-5],[-30,-7],[-30,-8],[-30,-9],[-30,-12],[-31,-3],[-32,-3],[-32,-5],[-32,-7],[-32,-8],[-32,-9],[-32,-12],[-33,-4],[-33,-30],[-33,-32],[-34,-5],[-34,-7],[-34,-8],[-34,-12],[-34,-33],[-36,-3],[-36,-5],[-36,-7],[-36,-8],[-36,-12],[-36,-33],[-37,-3],[-38,-3],[-39,-5],[-39,-7],[-39,-8],[-39,-12],[-39,-33],[-40,-4],[-40,-6],[-40,-9],[-40,-10],[-40,-11],[-40,-13],[-40,-14],[-40,-30],[-40,-31],[-40,-32],[-40,-34],[-40,-36],[-40,-37],[-40,-38],[-40,-39],[-41,-5],[-41,-7],[-41,-8],[-41,-12],[-41,-33],[-41,-40],[-42,-3],[-42,-5],[-42,-7],[-42,-8],[-42,-12],[-42,-33],[-42,-40],[-43,-29],[-43,-35],[-45,-43],[-48,-29],[-48,-35],[-48,-45],[-49,-43],[-49,-48],[-50,-43],[-50,-48],[-51,-43],[-51,-48],[-52,-43],[-52,-48],[-1,31,36,37,38,44,46,47],[-2,31,36,37,38,49,51,52],[-9,49,51,52],[-22,36,37,38,51,52],[-24,31,36,38,49,52],[-25,31,36,37,49,51],[-16,36,39,41,42,46,47],[-19,34,36,41,42,44,47],[-20,34,36,39,42,44,46,47],[-21,34,36,39,41,44,46],[-10,49,51,52],[-23,36,39,41,42,51,52],[-26,34,36,41,42,49,52],[-27,34,36,39,42,49,51,52],[-28,34,36,39,41,49,51],[-44,49],[-46,51],[-47,52],[-53,4,30,32,43,48],[-54,3,5,7,8,9,12,33,40],[-55,53],[-56,54],[-57,56],[-58,55],[-58,57],[58],[-59,29,44,45,46,47],[-44,59],[-46,59],[-47,59],[-60,35,49,50,51,52],[-49,60],[-51,60],[-52,60],[-61,59,60],[-60,61],[-59,61],[2,6,9,10,11,13,14,22,23,24,25,26,27,28,31,34,36,37,38,39,41,42,49,51,52],[1,2,9,15,17,18,22,24,25,31,36,37,38,44,46,47,49,51,52],[10,16,19,20,21,23,26,27,28,34,36,39,41,42,44,46,47,49,51,52]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":123},{\"tag\":\"facet\",\"index\":124},{\"tag\":\"facet\",\"index\":125},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":25,\"b\":23},{\"tag\":\"incompatible\",\"a\":26,\"b\":25},{\"tag\":\"incompatible\",\"a\":29,\"b\":25},{\"tag\":\"incompatible\",\"a\":31,\"b\":25},{\"tag\":\"incompatible\",\"a\":32,\"b\":25},{\"tag\":\"incompatible\",\"a\":40,\"b\":25},{\"tag\":\"incompatible\",\"a\":45,\"b\":23},{\"tag\":\"incompatible\",\"a\":53,\"b\":23},{\"tag\":\"incompatible\",\"a\":55,\"b\":23},{\"tag\":\"incompatible\",\"a\":64,\"b\":23},{\"tag\":\"incompatible\",\"a\":72,\"b\":23},{\"tag\":\"incompatible\",\"a\":74,\"b\":23},{\"tag\":\"incompatible\",\"a\":85,\"b\":23},{\"tag\":\"incompatible\",\"a\":85,\"b\":26},{\"tag\":\"incompatible\",\"a\":85,\"b\":29},{\"tag\":\"incompatible\",\"a\":85,\"b\":31},{\"tag\":\"incompatible\",\"a\":85,\"b\":32},{\"tag\":\"incompatible\",\"a\":85,\"b\":40},{\"tag\":\"incompatible\",\"a\":88,\"b\":23},{\"tag\":\"incompatible\",\"a\":89,\"b\":23},{\"tag\":\"incompatible\",\"a\":89,\"b\":26},{\"tag\":\"incompatible\",\"a\":89,\"b\":29},{\"tag\":\"incompatible\",\"a\":89,\"b\":31},{\"tag\":\"incompatible\",\"a\":89,\"b\":32},{\"tag\":\"incompatible\",\"a\":89,\"b\":40},{\"tag\":\"incompatible\",\"a\":90,\"b\":25},{\"tag\":\"incompatible\",\"a\":90,\"b\":85},{\"tag\":\"incompatible\",\"a\":90,\"b\":89},{\"tag\":\"incompatible\",\"a\":92,\"b\":26},{\"tag\":\"incompatible\",\"a\":92,\"b\":29},{\"tag\":\"incompatible\",\"a\":92,\"b\":31},{\"tag\":\"incompatible\",\"a\":92,\"b\":40},{\"tag\":\"incompatible\",\"a\":92,\"b\":90},{\"tag\":\"incompatible\",\"a\":97,\"b\":23},{\"tag\":\"incompatible\",\"a\":97,\"b\":26},{\"tag\":\"incompatible\",\"a\":97,\"b\":29},{\"tag\":\"incompatible\",\"a\":97,\"b\":31},{\"tag\":\"incompatible\",\"a\":97,\"b\":40},{\"tag\":\"incompatible\",\"a\":97,\"b\":90},{\"tag\":\"incompatible\",\"a\":99,\"b\":23},{\"tag\":\"incompatible\",\"a\":101,\"b\":23},{\"tag\":\"incompatible\",\"a\":104,\"b\":26},{\"tag\":\"incompatible\",\"a\":104,\"b\":29},{\"tag\":\"incompatible\",\"a\":104,\"b\":31},{\"tag\":\"incompatible\",\"a\":104,\"b\":40},{\"tag\":\"incompatible\",\"a\":104,\"b\":90},{\"tag\":\"incompatible\",\"a\":105,\"b\":25},{\"tag\":\"incompatible\",\"a\":105,\"b\":28},{\"tag\":\"incompatible\",\"a\":105,\"b\":32},{\"tag\":\"incompatible\",\"a\":105,\"b\":36},{\"tag\":\"incompatible\",\"a\":105,\"b\":39},{\"tag\":\"incompatible\",\"a\":105,\"b\":41},{\"tag\":\"incompatible\",\"a\":105,\"b\":42},{\"tag\":\"incompatible\",\"a\":105,\"b\":85},{\"tag\":\"incompatible\",\"a\":105,\"b\":88},{\"tag\":\"incompatible\",\"a\":105,\"b\":89},{\"tag\":\"incompatible\",\"a\":105,\"b\":92},{\"tag\":\"incompatible\",\"a\":105,\"b\":97},{\"tag\":\"incompatible\",\"a\":105,\"b\":99},{\"tag\":\"incompatible\",\"a\":105,\"b\":101},{\"tag\":\"incompatible\",\"a\":105,\"b\":104},{\"tag\":\"incompatible\",\"a\":106,\"b\":26},{\"tag\":\"incompatible\",\"a\":106,\"b\":29},{\"tag\":\"incompatible\",\"a\":106,\"b\":31},{\"tag\":\"incompatible\",\"a\":106,\"b\":40},{\"tag\":\"incompatible\",\"a\":106,\"b\":90},{\"tag\":\"incompatible\",\"a\":106,\"b\":105},{\"tag\":\"incompatible\",\"a\":107,\"b\":23},{\"tag\":\"incompatible\",\"a\":107,\"b\":26},{\"tag\":\"incompatible\",\"a\":107,\"b\":29},{\"tag\":\"incompatible\",\"a\":107,\"b\":31},{\"tag\":\"incompatible\",\"a\":107,\"b\":40},{\"tag\":\"incompatible\",\"a\":107,\"b\":90},{\"tag\":\"incompatible\",\"a\":107,\"b\":105},{\"tag\":\"incompatible\",\"a\":108,\"b\":84},{\"tag\":\"incompatible\",\"a\":108,\"b\":95},{\"tag\":\"incompatible\",\"a\":114,\"b\":108},{\"tag\":\"incompatible\",\"a\":117,\"b\":84},{\"tag\":\"incompatible\",\"a\":117,\"b\":95},{\"tag\":\"incompatible\",\"a\":117,\"b\":114},{\"tag\":\"incompatible\",\"a\":119,\"b\":108},{\"tag\":\"incompatible\",\"a\":119,\"b\":117},{\"tag\":\"incompatible\",\"a\":123,\"b\":108},{\"tag\":\"incompatible\",\"a\":123,\"b\":117},{\"tag\":\"incompatible\",\"a\":124,\"b\":108},{\"tag\":\"incompatible\",\"a\":124,\"b\":117},{\"tag\":\"incompatible\",\"a\":125,\"b\":108},{\"tag\":\"incompatible\",\"a\":125,\"b\":117},{\"tag\":\"mate\",\"ridge\":530,\"a\":5,\"owners\":[88,97,99,101,110,115,116]},{\"tag\":\"mate\",\"ridge\":532,\"a\":12,\"owners\":[88,97,99,101,119,124,125]},{\"tag\":\"mate\",\"ridge\":532,\"a\":32,\"owners\":[119,124,125]},{\"tag\":\"mate\",\"ridge\":532,\"a\":64,\"owners\":[97,99,101,124,125]},{\"tag\":\"mate\",\"ridge\":532,\"a\":72,\"owners\":[88,97,101,119,125]},{\"tag\":\"mate\",\"ridge\":532,\"a\":74,\"owners\":[88,97,99,119,124]},{\"tag\":\"mate\",\"ridge\":546,\"a\":49,\"owners\":[97,104,106,107,115,116]},{\"tag\":\"mate\",\"ridge\":546,\"a\":58,\"owners\":[92,97,106,107,110,116]},{\"tag\":\"mate\",\"ridge\":546,\"a\":60,\"owners\":[92,97,104,107,110,115,116]},{\"tag\":\"mate\",\"ridge\":546,\"a\":61,\"owners\":[92,97,104,106,110,115]},{\"tag\":\"mate\",\"ridge\":548,\"a\":36,\"owners\":[119,124,125]},{\"tag\":\"mate\",\"ridge\":548,\"a\":68,\"owners\":[97,104,106,107,124,125]},{\"tag\":\"mate\",\"ridge\":548,\"a\":77,\"owners\":[92,97,106,107,119,125]},{\"tag\":\"mate\",\"ridge\":548,\"a\":79,\"owners\":[92,97,104,107,119,124,125]},{\"tag\":\"mate\",\"ridge\":548,\"a\":80,\"owners\":[92,97,104,106,119,124]},{\"tag\":\"mate\",\"ridge\":568,\"a\":110,\"owners\":[119]},{\"tag\":\"mate\",\"ridge\":624,\"a\":115,\"owners\":[124]},{\"tag\":\"mate\",\"ridge\":816,\"a\":116,\"owners\":[125]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[25,85,89,108,117],\"full_literals\":[-53,4,30,32,43,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[23,26,29,31,32,40,90,105],\"full_literals\":[-54,3,5,7,8,9,12,33,40]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-55,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0005\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-58,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-58,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[84,110,114,115,116],\"full_literals\":[-59,29,44,45,46,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":110,\"full_literals\":[-44,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":115,\"full_literals\":[-46,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":116,\"full_literals\":[-47,59]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[95,119,123,124,125],\"full_literals\":[-60,35,49,50,51,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":119,\"full_literals\":[-49,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":124,\"full_literals\":[-51,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":125,\"full_literals\":[-52,60]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"edge\",\"edge\":23,\"owners\":[12,28,32,36,39,41,42,64,68,72,74,77,79,80,88,92,97,99,101,104,106,107,119,124,125]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[5,12,32,45,53,55,64,72,74,88,97,99,101,110,115,116,119,124,125]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[36,49,58,60,61,68,77,79,80,92,97,104,106,107,110,115,116,119,124,125]}]}"
  "129 55 0 114 112 0\n130 57 0 114 113 0\n131 53 0 129 109 0\n132 56 0 130 111 0\n133 54 0 132 110 0\n134 34 36 39 41 42 61 0 124 122 121 100 125 118 117 95 120 99 116 96 97 98 101 102 103 128 0\n135 -42 9 0 133 68 69 70 71 72 73 74 108 0\n136 -3 61 0 124 122 121 120 91 125 118 117 116 7 8 9 10 11 12 19 34 40 41 89 90 127 0\n137 -5 61 0 124 122 121 120 91 135 29 35 42 62 134 0\n138 -7 61 0 124 122 121 120 91 135 30 36 43 63 134 0\n139 -8 61 0 124 122 121 120 91 135 31 37 44 64 134 0\n140 -12 61 0 124 122 121 120 91 135 32 38 45 65 134 0\n141 -33 61 0 124 122 121 120 91 135 33 39 46 66 134 0\n142 61 0 133 124 120 121 122 91 135 136 137 138 139 140 141 108 57 58 61 67 134 0\n143 49 51 52 -40 0 61 74 67 58 100 59 60 92 57 55 53 52 51 50 49 48 90 93 94 103 102 101 126 0\n144 -49 -40 0 131 56 54 47 81 82 107 0\n145 -51 -40 0 131 56 54 47 85 86 107 0\n146 -40 0 131 47 54 56 144 145 143 87 88 107 0\n147 -4 0 146 133 1 2 3 4 5 6 26 108 0\n148 -30 0 146 133 13 14 15 16 17 18 27 108 0\n149 -32 0 146 133 20 21 22 23 24 25 28 108 0\n150 -52 0 149 148 147 131 87 88 107 0\n151 -47 0 150 106 0\n152 -43 49 51 0 151 150 142 104 105 75 76 77 83 115 119 123 0\n153 49 51 0 149 148 147 131 151 150 142 105 104 152 107 78 79 80 84 115 119 123 0\n154 -49 0 149 148 147 131 81 82 107 0\n155 51 0 154 153 0\n156 -43 0 155 85 0\n157 -48 0 155 86 0\n158 0 157 156 131 147 148 149 107 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00049.record006
