module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00001Data
public import GraphInputsRow26Part00001Frames
public import GraphInputsRow26Part00001Leaves
public import GraphInputsRow26Part00001Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00001.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 7), 844429225099264, 17179869184]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c2 c3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), 72057628397666304]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), 34359738368]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 1729382256912367616, (certNat% 14), 4432406249472, (certNat% 15)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c2 c11
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c2 c12
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), (certNat% 4)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 4), (certNat% 19), (certNat% 20)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), (certNat% 23), 1008806316530991104, (certNat% 24)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), 4899916394662985728, (certNat% 14), (certNat% 26)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), (certNat% 29), (certNat% 26), 1008806316530991104, 1152921504606846976]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c22 c19
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c23 c10
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨20, by decide⟩ c24 c0
  c25
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00001.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00001.record039
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "358ae3546d34cc725c5729a968ba659562d86e17bc1e46b16c749aa719a66392e74569715655352d70d9354d1b61d4743db0dc3a4d932ce8b92cab1ae1b26c3b61d4729c6745c970dc1fe403c2c83a0d84e0b81ee0741925451342d28c4b0ac4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6da6d249369b6da6db6d24da6db4d24da6926d2249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 20), (facetIndex 63), (facetIndex 64)]))
 (.branch 2
 (.leaf ([(facetIndex 52), (facetIndex 58), (facetIndex 62)]))
 (.leaf ([(facetIndex 26), (facetIndex 43), (facetIndex 44), (facetIndex 45)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 31), (facetIndex 33)]))
 (.leaf ([(facetIndex 21), (facetIndex 28), (facetIndex 35), (facetIndex 65), (facetIndex 68)])))
 (.branch 6
 (.leaf ([(facetIndex 24), (facetIndex 25), (facetIndex 32)]))
 (.leaf ([(facetIndex 40), (facetIndex 61)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "402007004000100001240600081d6040ad02z10;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [1, 2]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [3]
def grouped2_0007 : List Nat := [3, 4]
def grouped2_0008 : List Nat := [3, 4, 5, 6]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00001.record039" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00001.record039" 36

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00001.record039" "{\"ridges\":[[9,577],[10,832],[33,577],[39,706],[40,28],[45,76],[45,584],[52,832],[58,832],[62,832],[63,28],[64,76],[69,594],[71,76],[72,596],[73,28],[74,780],[78,344]],\"owners\":[[9,577,[10,39,52,62],[33,45]],[33,577,[10,52,62],[9,39,45]],[45,584,[69,78],[9,33,58,72,74]],[10,832,[74,76,78],[52,58,62]],[52,832,[78],[10,58,62,74,76]],[58,832,[76],[10,52,62,74,78]],[62,832,[74,76,78],[10,52,58]],[39,706,[],[]],[74,780,[46,73],[]],[69,594,[],[]],[78,344,[71],[]],[72,596,[76],[]]],\"edges\":[[41,[9,10,33,39,45,52,58,62,69,72,74,76,78]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00001.record039" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00001.record039\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-8,-3],[-13,-4],[-14,-6],[-15,-3],[-16,-12],[-16,-15],[-18,-5],[-18,-8],[-18,-9],[-24,-17],[-25,-10],[-25,-14],[-25,-17],[-11,-18,-20],[-1,2,7,13,16],[-6,2,13,16],[-11,19,25],[-2,23,24,25],[-13,25],[-14,24],[-16,23,24,25],[-8,-17,-22],[-7],[-23,12,22],[-19],[-25,20],[-21,24],[-26,3,17,18],[-27,13,14,16],[-28,4,9,10,11],[-29,5,6],[-30,8,15],[-31,27],[-31,28],[-32,26],[-32,31],[-33,29],[-34,30],[-35,33],[-35,34],[-36,32],[-36,35],[36],[1,2,6,7,11,13,14,16,19,21,23,24,25]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":40,\"b\":20},{\"tag\":\"incompatible\",\"a\":52,\"b\":26},{\"tag\":\"incompatible\",\"a\":58,\"b\":33},{\"tag\":\"incompatible\",\"a\":61,\"b\":20},{\"tag\":\"incompatible\",\"a\":62,\"b\":46},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":31},{\"tag\":\"incompatible\",\"a\":64,\"b\":40},{\"tag\":\"incompatible\",\"a\":64,\"b\":43},{\"tag\":\"incompatible\",\"a\":76,\"b\":63},{\"tag\":\"incompatible\",\"a\":78,\"b\":44},{\"tag\":\"incompatible\",\"a\":78,\"b\":58},{\"tag\":\"incompatible\",\"a\":78,\"b\":63},{\"tag\":\"three\",\"ridge\":76,\"vertices\":[45,64,71]},{\"tag\":\"mate\",\"ridge\":577,\"a\":9,\"owners\":[10,39,52,62]},{\"tag\":\"mate\",\"ridge\":577,\"a\":33,\"owners\":[10,52,62]},{\"tag\":\"mate\",\"ridge\":584,\"a\":45,\"owners\":[69,78]},{\"tag\":\"mate\",\"ridge\":832,\"a\":10,\"owners\":[74,76,78]},{\"tag\":\"mate\",\"ridge\":832,\"a\":52,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":832,\"a\":58,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":832,\"a\":62,\"owners\":[74,76,78]},{\"tag\":\"three\",\"ridge\":28,\"vertices\":[40,63,73]},{\"tag\":\"mate\",\"ridge\":706,\"a\":39,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":780,\"a\":74,\"owners\":[46,73]},{\"tag\":\"mate\",\"ridge\":594,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":344,\"a\":78,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":596,\"a\":72,\"owners\":[76]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[20,63,64],\"full_literals\":[-26,3,17,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[52,58,62],\"full_literals\":[-27,13,14,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[26,43,44,45],\"full_literals\":[-28,4,9,10,11]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[31,33],\"full_literals\":[-29,5,6]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[40,61],\"full_literals\":[-30,8,15]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-31,27,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-31,false,28],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-32,26,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-32,false,31],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-33,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-34,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-35,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-36,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-36,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[9,10,33,39,45,52,58,62,69,72,74,76,78]}]}"
  "45 32 0 43 41 0\n46 35 0 43 42 0\n47 26 0 45 35 0\n48 31 0 45 36 0\n49 33 0 46 39 0\n50 34 0 46 40 0\n51 27 0 48 33 0\n52 28 0 48 34 0\n53 29 0 49 37 0\n54 30 0 50 38 0\n55 1 2 6 11 13 14 16 21 23 24 25 0 23 25 44 0\n56 23 25 24 0 23 25 18 21 20 27 19 17 15 16 55 0\n57 -22 -8 0 47 22 1 8 28 0\n58 24 25 0 51 54 19 20 56 29 5 6 24 32 57 0\n59 -8 17 0 47 1 8 28 0\n60 25 0 54 47 51 53 19 58 10 59 32 4 6 28 29 7 3 31 0\n61 -10 0 60 11 0\n62 -14 0 60 12 0\n63 -17 0 60 13 0\n64 20 0 60 26 0\n65 -8 0 63 59 0\n66 15 0 65 54 32 0\n67 -3 0 66 4 0\n68 -16 0 66 6 0\n69 18 0 67 47 63 28 0\n70 13 0 68 51 62 29 0\n71 -9 0 69 9 0\n72 -11 0 69 64 14 0\n73 -4 0 70 2 0\n74 0 73 71 52 61 72 30 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00001.record039
