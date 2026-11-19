module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00018Data
public import GraphInputsRow26Part00018Frames
public import GraphInputsRow26Part00018Leaves
public import GraphInputsRow26Part00018Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record031
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨30, by decide⟩, ⟨38, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 274877906944]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), 9007474166202368]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), (certNat% 13)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 12), (certNat% 16)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 12), (certNat% 18), (certNat% 19)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), (certNat% 9)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 15), (certNat% 12), (certNat% 24), 2882303761517117440]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), (certNat% 27), (certNat% 5), 12105675798371893248, (certNat% 28)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record031

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record044
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044
def vertexColumn : Fields := ⟨10, (certNat% 29)⟩
def kindColumn : Fields := ⟨3, (certNat% 30)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), 72198333673766912, 18023194602504192, 2252349569499136]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 21), (certNat% 34), 5066549599666176, 2252349569499136]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), 5066549599666176, (certNat% 36), (certNat% 37)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), 9147936743096320]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 16), 9147936776650752, 18014398643699712]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), 18014398643699712, (certNat% 42), 580542149951488, (certNat% 21)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), (certNat% 45), (certNat% 37), 6755399457832960, 9147938890579968]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record044

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e631c670bc1f1e2e4b5274b8ac6a9a669a659b1665956c398e2b86e8791e2785ee4751744f1a64b91e715655552d4752b46d8749d1743de0f4370ce3c4e9364e5354cd3a2e2b1ae1b26c5bc1d8751ca785d1725c5783c8f13c1f550aa518660b8a986499194550b41d28c6382c8b0ac4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6db6d369b49b6db6d26da6924926da6db6d24936d26da492249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 35), (facetIndex 36), (facetIndex 44)]))
 (.branch 2
 (.leaf ([(facetIndex 24), (facetIndex 29), (facetIndex 56), (facetIndex 74)]))
 (.leaf ([(facetIndex 21), (facetIndex 70), (facetIndex 77)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 22), (facetIndex 50), (facetIndex 53), (facetIndex 71)]))
 (.leaf ([(facetIndex 48), (facetIndex 51), (facetIndex 60), (facetIndex 61)])))
 (.branch 6
 (.leaf ([(facetIndex 20), (facetIndex 23), (facetIndex 33), (facetIndex 34), (facetIndex 37)]))
 (.leaf ([(facetIndex 49), (facetIndex 52), (facetIndex 54)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1004068000002400119e8f4000000028168008001ad5000000000000000"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record000" 46

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record000" "{\"ridges\":[[29,262],[29,322],[30,389],[41,386],[45,449],[47,386],[56,276],[56,336],[65,400],[72,396],[73,262],[73,780],[74,276],[74,322],[75,262],[75,276],[78,420],[83,386],[86,480],[90,276],[90,780],[90,784]],\"owners\":[[29,262,[68,72,73,75,76,78],[17,26,30,31,74,77]],[29,322,[83,84,86],[17,39,45,46,74,77]],[74,322,[45,46,86],[17,29,39,77,83,84]],[56,276,[68,75,76,89,90],[19,26,57,58,74]],[74,276,[57,58,89,90],[19,26,56,68,75,76]],[56,336,[83,84],[19,39,63,64,74]],[41,386,[72,78,82,86],[30,45,47,75,79,83,85]],[47,386,[72,75,78,79,83,86],[30,41,45,82,85]],[83,386,[30,47,72,78,82],[41,45,75,79,85,86]],[30,389,[57],[]],[65,400,[75,79,83,89],[41,57,63,85,91]],[90,784,[43,64,65,84,85],[58,76,81,91]],[45,449,[63],[]],[72,396,[89],[]],[73,780,[90],[]],[90,780,[73],[]],[78,420,[],[]],[86,480,[],[]]],\"edges\":[[42,[30,41,45,47,57,63,65,72,75,78,79,82,83,85,86,89,91]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-3],[-10,-2],[-12,-2],[-14,-2],[-15,-9],[-16,-1],[-16,-11],[-16,-13],[-17,-3],[-17,-8],[-17,-15],[-18,-3],[-18,-6],[-18,-15],[-18,-17],[-19,-18],[-20,-3],[-20,-15],[-20,-18],[-22,-16],[-26,-25],[-31,-21],[-31,-25],[-31,-26],[-31,-27],[-32,-21],[-32,-25],[-32,-26],[-32,-27],[-33,-25],[-33,-31],[-33,-32],[-35,-1],[-35,-11],[-35,-13],[-35,-22],[-36,-29],[-36,-30],[-37,-36],[-3,21,23,24,26,27,28],[-3,-24,-26],[-3,31,32,34],[-25,7,8,34],[-15,21,26,27,35,36],[-25,16,17,35,36],[-15,-26,-36],[-15,31,32],[-5,23,28,30,34],[-9,23,26,28,29,31,34],[-31,4,9,23,28,30],[-4,16],[-20,26,29,31,35],[-36,6,19,20,32,33],[-7,18],[-23,35],[-24,36],[-36,24],[-28],[-34],[-38,2,3,15,25],[-39,1,11,13,22],[-40,10,12,14],[-41,38],[-42,41],[-43,39],[-44,40],[-45,43],[-45,44],[-46,42],[-46,45],[46],[4,5,7,9,16,18,20,23,26,28,29,30,31,33,34,35,37]],\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":47,\"b\":29},{\"tag\":\"incompatible\",\"a\":49,\"b\":24},{\"tag\":\"incompatible\",\"a\":52,\"b\":24},{\"tag\":\"incompatible\",\"a\":54,\"b\":24},{\"tag\":\"incompatible\",\"a\":56,\"b\":47},{\"tag\":\"incompatible\",\"a\":57,\"b\":22},{\"tag\":\"incompatible\",\"a\":57,\"b\":50},{\"tag\":\"incompatible\",\"a\":57,\"b\":53},{\"tag\":\"incompatible\",\"a\":58,\"b\":29},{\"tag\":\"incompatible\",\"a\":58,\"b\":46},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":63,\"b\":29},{\"tag\":\"incompatible\",\"a\":63,\"b\":43},{\"tag\":\"incompatible\",\"a\":63,\"b\":56},{\"tag\":\"incompatible\",\"a\":63,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":65,\"b\":29},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":65,\"b\":63},{\"tag\":\"incompatible\",\"a\":71,\"b\":57},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":83,\"b\":68},{\"tag\":\"incompatible\",\"a\":83,\"b\":74},{\"tag\":\"incompatible\",\"a\":83,\"b\":75},{\"tag\":\"incompatible\",\"a\":83,\"b\":76},{\"tag\":\"incompatible\",\"a\":84,\"b\":68},{\"tag\":\"incompatible\",\"a\":84,\"b\":74},{\"tag\":\"incompatible\",\"a\":84,\"b\":75},{\"tag\":\"incompatible\",\"a\":84,\"b\":76},{\"tag\":\"incompatible\",\"a\":85,\"b\":74},{\"tag\":\"incompatible\",\"a\":85,\"b\":83},{\"tag\":\"incompatible\",\"a\":85,\"b\":84},{\"tag\":\"incompatible\",\"a\":89,\"b\":22},{\"tag\":\"incompatible\",\"a\":89,\"b\":50},{\"tag\":\"incompatible\",\"a\":89,\"b\":53},{\"tag\":\"incompatible\",\"a\":89,\"b\":71},{\"tag\":\"incompatible\",\"a\":90,\"b\":79},{\"tag\":\"incompatible\",\"a\":90,\"b\":82},{\"tag\":\"incompatible\",\"a\":91,\"b\":90},{\"tag\":\"mate\",\"ridge\":262,\"a\":29,\"owners\":[68,72,73,75,76,78]},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[29,73,75]},{\"tag\":\"mate\",\"ridge\":322,\"a\":29,\"owners\":[83,84,86]},{\"tag\":\"mate\",\"ridge\":322,\"a\":74,\"owners\":[45,46,86]},{\"tag\":\"mate\",\"ridge\":276,\"a\":56,\"owners\":[68,75,76,89,90]},{\"tag\":\"mate\",\"ridge\":276,\"a\":74,\"owners\":[57,58,89,90]},{\"tag\":\"three\",\"ridge\":276,\"vertices\":[56,75,90]},{\"tag\":\"mate\",\"ridge\":336,\"a\":56,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":386,\"a\":41,\"owners\":[72,78,82,86]},{\"tag\":\"mate\",\"ridge\":386,\"a\":47,\"owners\":[72,75,78,79,83,86]},{\"tag\":\"mate\",\"ridge\":386,\"a\":83,\"owners\":[30,47,72,78,82]},{\"tag\":\"mate\",\"ridge\":389,\"a\":30,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":400,\"a\":65,\"owners\":[75,79,83,89]},{\"tag\":\"mate\",\"ridge\":784,\"a\":90,\"owners\":[43,64,65,84,85]},{\"tag\":\"mate\",\"ridge\":449,\"a\":45,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":396,\"a\":72,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":780,\"a\":73,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":780,\"a\":90,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":420,\"a\":78,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":480,\"a\":86,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[24,29,56,74],\"full_literals\":[-38,2,3,15,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[22,50,53,71],\"full_literals\":[-39,1,11,13,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[49,52,54],\"full_literals\":[-40,10,12,14]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-42,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-45,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-46,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-46,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[30,41,45,47,57,63,65,72,75,78,79,82,83,85,86,89,91]}]}"
  "73 42 0 71 69 0\n74 45 0 71 70 0\n75 41 0 73 64 0\n76 43 0 74 67 0\n77 44 0 74 68 0\n78 38 0 75 63 0\n79 39 0 76 65 0\n80 40 0 77 66 0\n81 4 5 7 9 16 18 20 23 26 29 30 31 33 35 37 0 58 59 72 0\n82 -16 0 79 6 7 8 20 61 0\n83 -4 0 82 51 0\n84 -2 0 80 2 3 4 62 0\n85 21 26 25 35 27 36 0 58 84 78 55 56 40 44 60 0\n86 31 25 32 0 59 84 78 47 42 60 0\n87 35 17 27 32 36 0 82 45 86 22 24 85 0\n88 -35 0 79 33 34 35 36 61 0\n89 -23 0 88 55 0\n90 32 17 36 0 82 88 45 87 86 25 0\n91 17 36 0 88 82 45 90 28 29 85 26 0\n92 -17 7 0 59 84 78 9 10 11 43 60 0\n93 9 20 5 37 7 18 26 30 29 33 0 83 89 58 82 88 81 50 0\n94 -3 18 33 0 58 89 59 54 92 91 38 48 57 39 37 1 17 41 93 0\n95 -15 18 33 0 58 89 59 54 92 91 38 48 39 37 5 18 46 93 0\n96 18 33 0 84 78 88 59 58 89 54 92 91 37 38 39 48 94 95 60 21 23 52 49 93 0\n97 33 0 84 78 96 12 13 14 15 16 19 60 91 53 27 0\n98 -25 0 97 30 0\n99 -31 0 97 31 0\n100 -32 0 97 32 0\n101 0 99 100 98 86 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record015
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f07c789d23cb8a6a99a2eb462d876c3a2e2ba1e2783e785d13c7896a569665592e479d14b51d70d5362d2b46d8749d1743de0f4370da358ce364d5334cb31cf0ba2d8b8ad2b2ae1b46c9b0ef0791d4789ca785c970de0f43c8f0bc1f19856c25892a499194558342d0770360d4328c6324c5381c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6da6db6db6934d36d269249249249249269b4da69249249b489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 44), (facetIndex 64), (facetIndex 74)]))
 (.leaf ([(facetIndex 27), (facetIndex 45), (facetIndex 46), (facetIndex 56), (facetIndex 65), (facetIndex 69), (facetIndex 84)])))
 (.branch 3
 (.leaf ([(facetIndex 57), (facetIndex 59), (facetIndex 60), (facetIndex 62)]))
 (.leaf ([(facetIndex 26), (facetIndex 29), (facetIndex 31), (facetIndex 33), (facetIndex 34)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 32), (facetIndex 48), (facetIndex 51), (facetIndex 53), (facetIndex 54), (facetIndex 55)]))
 (.leaf ([(facetIndex 58), (facetIndex 61), (facetIndex 71), (facetIndex 73)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 36), (facetIndex 47), (facetIndex 49), (facetIndex 52)]))
 (.branch 8
 (.leaf ([(facetIndex 23), (facetIndex 30), (facetIndex 39), (facetIndex 50)]))
 (.leaf ([(facetIndex 22), (facetIndex 42)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "100000000005050100010025225214446476461100800700603343736130078z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 25), (facetIndex 63), (facetIndex 67)]))
 (.leaf ([(facetIndex 83), (facetIndex 86)])))
 (.branch 3
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 77)]))
 (.branch 4
 (.leaf ([(facetIndex 91), (facetIndex 92), (facetIndex 93)]))
 (.leaf ([(facetIndex 68), (facetIndex 70), (facetIndex 72)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 35), (facetIndex 66), (facetIndex 94)]))
 (.leaf ([(facetIndex 24), (facetIndex 78), (facetIndex 85)])))
 (.branch 8
 (.leaf ([(facetIndex 79), (facetIndex 87), (facetIndex 95)]))
 (.branch 9
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 40), (facetIndex 41), (facetIndex 43), (facetIndex 81)]))
 (.leaf ([(facetIndex 80), (facetIndex 82), (facetIndex 88), (facetIndex 89), (facetIndex 90)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "753339997160198976222004040405z16;80880880500000000006z18;"⟩
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
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1]
def grouped3_0019 : List Nat := [1]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record015" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record015" 89

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record015" "{\"ridges\":[[3,518],[8,259],[9,259],[10,259],[10,770],[13,524],[14,69],[18,385],[19,769],[19,776],[25,259],[26,524],[28,146],[29,19],[29,517],[29,518],[31,518],[33,518],[34,518],[34,770],[35,19],[36,19],[41,554],[42,392],[44,776],[45,81],[48,19],[48,259],[49,259],[49,386],[51,259],[51,322],[52,35],[52,259],[53,322],[54,770],[55,385],[55,386],[55,769],[55,770],[59,524],[60,69],[62,517],[62,524],[63,332],[64,524],[64,776],[67,69],[67,321],[67,517],[67,769],[67,836],[70,344],[71,385],[71,392],[72,360],[73,385],[74,776],[76,321],[76,385],[76,464],[77,321],[77,385],[77,480],[82,518],[83,270],[83,770],[86,322],[86,518],[86,770],[86,836],[88,282],[88,386],[89,386],[92,322],[92,386],[92,464],[93,386],[93,480]],\"owners\":[[52,35,[1,6,23,27,31,35,41,45],[7,39,40,46,51]],[3,518,[80,82,83,86],[26,29,31,33,34]],[29,518,[82,83,86],[3,26,31,33,34,80]],[31,518,[80,83,86],[3,26,29,33,34,82]],[33,518,[80,82,83],[3,26,29,31,34,86]],[34,518,[80,82],[3,26,29,31,33,83,86]],[45,81,[14,57,70,76],[4,47,48,65,68,75]],[28,146,[87,88,91,92],[5,36,46,47,49,79,85]],[67,321,[8,48,51,53,70,72,76,77],[32,54,63]],[76,321,[8,32,51,54,63,67,72],[48,53,70,77]],[77,321,[8,32,48,54,63,67,70],[51,53,72,76]],[53,322,[86],[8,32,48,51,54,92,93]],[18,385,[9,49,52,53,55,76,77],[71,73,74]],[49,386,[89,90,93],[9,42,52,53,55,88,92]],[88,386,[9,52,53,55,93],[42,49,89,90,92]],[92,386,[9,42,52,55,89,90],[49,53,88,93]],[93,386,[9,42,49,55,88,90],[52,53,89,92]],[10,770,[83,86,90],[34,44,54,55]],[34,770,[90],[10,44,54,55,83,86]],[54,770,[83,90],[10,34,44,55,86]],[55,770,[83,86],[10,34,44,54,90]],[83,770,[10,54,55],[34,44,86,90]],[86,770,[10,44,55,90],[34,54,83]],[13,524,[80,82,83],[26,59,62,64]],[26,524,[],[13,59,62,64,80,82,83]],[59,524,[82,83],[13,26,62,64,80]],[62,524,[80,83],[13,26,59,64,82]],[64,524,[80,82],[13,26,59,62,83]],[42,392,[],[18,71,73,74,88,89,90]],[71,392,[89,90],[18,42,73,74,88]],[19,776,[83,90],[44,64,74]],[44,776,[],[19,64,74,83,90]],[64,776,[90],[19,44,74,83]],[74,776,[83],[19,44,64,90]],[83,270,[25],[]],[88,282,[37],[]],[41,554,[82],[]],[63,332,[],[]],[67,836,[86],[]],[86,836,[67],[]],[70,344,[],[]],[72,360,[],[]],[76,464,[92],[]],[92,464,[76],[]],[77,480,[93],[]],[93,480,[77],[]]],\"edges\":[[23,[3,13,26,29,31,33,34,59,62,64,67,80,82,83,86]],[28,[18,19,25,37,40,42,44,63,64,70,71,72,73,74,83,88,89,90]],[29,[13,19,26,38,41,43,44,59,62,64,74,80,82,83,90]],[40,[8,32,48,51,53,54,63,67,70,72,76,77,86,92,93]],[42,[9,18,42,49,52,53,55,71,73,74,76,77,88,89,90,92,93]],[44,[10,19,34,44,54,55,64,67,74,83,86,90]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record015" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record015\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-17,-1],[-17,-11],[-17,-12],[-17,-15],[-17,-16],[-19,-11],[-19,-12],[-19,-18],[-26,-11],[-27,-24],[-29,-11],[-31,-11],[-34,-17],[-35,-3],[-35,-16],[-35,-34],[-36,-35],[-37,-35],[-38,-18],[-38,-37],[-39,-27],[-39,-38],[-40,-6],[-40,-25],[-40,-34],[-40,-36],[-40,-39],[-41,-13],[-42,-4],[-42,-13],[-42,-25],[-42,-28],[-42,-38],[-42,-40],[-43,-17],[-44,-11],[-44,-17],[-46,-11],[-53,-38],[-57,-11],[-58,-11],[-59,-20],[-60,-13],[-60,-20],[-60,-21],[-60,-22],[-60,-41],[-60,-48],[-60,-59],[-62,-59],[-63,-38],[-63,-59],[-64,-11],[-64,-12],[-64,-24],[-64,-27],[-64,-42],[-64,-57],[-64,-58],[-64,-59],[-64,-61],[-65,-40],[-66,-25],[-66,-35],[-66,-40],[-66,-51],[-66,-62],[-67,-28],[-67,-38],[-67,-40],[-67,-53],[-67,-63],[-17,-23,-35],[-17,-24,-35],[-39,1,3,12,15,19,23,29,33],[-8,-45,-49],[-17,-46,-49],[-2,57,58,59,60],[-17,58,59,60],[-19,57,59,60],[-21,57,58,59],[-22,57,58],[-17,-58,-60],[-33,8,43,50,55],[-16,61,62,65,66],[-4,-6,-13],[-5,-6,-13],[-5,-6,-38],[-6,-13,-35],[-6,-13,-36],[-6,-13,-38],[-6,-13,-39],[-49,4,35,38,40,50,52,55,56],[-55,4,20,38,41,47,49,52],[-56,4,20,35,41,47,49,50],[-40,60],[-38,-60,-66],[-9,5,36,39,40,42,55,56],[-9,-42,-55],[-9,-42,-56],[-42,-51,-56],[-42,-53,-55],[-36,63,64,67],[-62,5,39,40,42,67],[-66,5,30,39,42,63,64],[-67,5,30,36,42,62,64],[-42,-62,-67],[-42,-63,-66],[-10,-42,-49],[-6,59,60,64],[-22,64],[-41,59,64],[-42,59,60],[-59,6,41,42],[-60,6,32,42,64],[-7,57,58,59],[-14],[-44,58,59],[-46,57,59],[-48,57,58],[-30],[-51,63,64],[-10,59,64],[-32],[-48,64],[-54,59],[-59,13],[-62,25],[-29,58],[-47],[-49,60],[-60,49],[-50],[-52],[-55,66],[-66,55],[-56,67],[-67,56],[-68,32,48,54],[-69,43,44,45,46],[-70,14,17,19,21,22],[-71,20,35,38,40,41,42],[-72,16,24,34,36,39],[-73,12,18,27,37],[-74,11,30],[-75,68],[-76,69],[-76,70],[-77,75,76],[-78,75],[-79,71],[-80,73,74],[-81,74],[-82,72,81],[-82,80],[-83,81],[-84,79,83],[-85,79],[-84,82],[-85,83],[-86,77,85],[-86,78,84],[86],[-87,13,47,49],[-13,87],[-49,87],[-88,59,60],[-59,88],[-89,87],[-87,-88,89],[2,7,14,17,19,21,22,44,46,48,49,57,58,59,60],[9,10,13,25,28,30,32,47,48,50,51,52,53,54,59,62,63,64],[7,10,14,26,29,31,32,44,46,48,54,57,58,59,64],[4,20,35,38,40,41,47,49,50,52,55,56,60,66,67],[5,9,30,36,39,40,42,51,53,54,55,56,62,63,64,66,67],[6,10,22,32,41,42,48,49,54,59,60,64]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":29,\"b\":1},{\"tag\":\"incompatible\",\"a\":29,\"b\":22},{\"tag\":\"incompatible\",\"a\":29,\"b\":23},{\"tag\":\"incompatible\",\"a\":29,\"b\":27},{\"tag\":\"incompatible\",\"a\":29,\"b\":28},{\"tag\":\"incompatible\",\"a\":31,\"b\":22},{\"tag\":\"incompatible\",\"a\":31,\"b\":23},{\"tag\":\"incompatible\",\"a\":31,\"b\":30},{\"tag\":\"incompatible\",\"a\":38,\"b\":22},{\"tag\":\"incompatible\",\"a\":39,\"b\":36},{\"tag\":\"incompatible\",\"a\":41,\"b\":22},{\"tag\":\"incompatible\",\"a\":43,\"b\":22},{\"tag\":\"incompatible\",\"a\":47,\"b\":29},{\"tag\":\"incompatible\",\"a\":48,\"b\":6},{\"tag\":\"incompatible\",\"a\":48,\"b\":28},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":30},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":39},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":10},{\"tag\":\"incompatible\",\"a\":53,\"b\":37},{\"tag\":\"incompatible\",\"a\":53,\"b\":47},{\"tag\":\"incompatible\",\"a\":53,\"b\":49},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":25},{\"tag\":\"incompatible\",\"a\":55,\"b\":8},{\"tag\":\"incompatible\",\"a\":55,\"b\":25},{\"tag\":\"incompatible\",\"a\":55,\"b\":37},{\"tag\":\"incompatible\",\"a\":55,\"b\":40},{\"tag\":\"incompatible\",\"a\":55,\"b\":51},{\"tag\":\"incompatible\",\"a\":55,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":29},{\"tag\":\"incompatible\",\"a\":59,\"b\":22},{\"tag\":\"incompatible\",\"a\":59,\"b\":29},{\"tag\":\"incompatible\",\"a\":62,\"b\":22},{\"tag\":\"incompatible\",\"a\":73,\"b\":51},{\"tag\":\"incompatible\",\"a\":80,\"b\":22},{\"tag\":\"incompatible\",\"a\":82,\"b\":22},{\"tag\":\"incompatible\",\"a\":83,\"b\":32},{\"tag\":\"incompatible\",\"a\":86,\"b\":25},{\"tag\":\"incompatible\",\"a\":86,\"b\":32},{\"tag\":\"incompatible\",\"a\":86,\"b\":33},{\"tag\":\"incompatible\",\"a\":86,\"b\":34},{\"tag\":\"incompatible\",\"a\":86,\"b\":54},{\"tag\":\"incompatible\",\"a\":86,\"b\":64},{\"tag\":\"incompatible\",\"a\":86,\"b\":83},{\"tag\":\"incompatible\",\"a\":88,\"b\":83},{\"tag\":\"incompatible\",\"a\":89,\"b\":51},{\"tag\":\"incompatible\",\"a\":89,\"b\":83},{\"tag\":\"incompatible\",\"a\":90,\"b\":22},{\"tag\":\"incompatible\",\"a\":90,\"b\":23},{\"tag\":\"incompatible\",\"a\":90,\"b\":36},{\"tag\":\"incompatible\",\"a\":90,\"b\":39},{\"tag\":\"incompatible\",\"a\":90,\"b\":55},{\"tag\":\"incompatible\",\"a\":90,\"b\":80},{\"tag\":\"incompatible\",\"a\":90,\"b\":82},{\"tag\":\"incompatible\",\"a\":90,\"b\":83},{\"tag\":\"incompatible\",\"a\":90,\"b\":87},{\"tag\":\"incompatible\",\"a\":91,\"b\":53},{\"tag\":\"incompatible\",\"a\":92,\"b\":37},{\"tag\":\"incompatible\",\"a\":92,\"b\":48},{\"tag\":\"incompatible\",\"a\":92,\"b\":53},{\"tag\":\"incompatible\",\"a\":92,\"b\":71},{\"tag\":\"incompatible\",\"a\":92,\"b\":88},{\"tag\":\"incompatible\",\"a\":93,\"b\":40},{\"tag\":\"incompatible\",\"a\":93,\"b\":51},{\"tag\":\"incompatible\",\"a\":93,\"b\":53},{\"tag\":\"incompatible\",\"a\":93,\"b\":73},{\"tag\":\"incompatible\",\"a\":93,\"b\":89},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[29,35,48]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[29,36,48]},{\"tag\":\"mate\",\"ridge\":35,\"a\":52,\"owners\":[1,6,23,27,31,35,41,45]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[14,60,67]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[29,62,67]},{\"tag\":\"mate\",\"ridge\":518,\"a\":3,\"owners\":[80,82,83,86]},{\"tag\":\"mate\",\"ridge\":518,\"a\":29,\"owners\":[82,83,86]},{\"tag\":\"mate\",\"ridge\":518,\"a\":31,\"owners\":[80,83,86]},{\"tag\":\"mate\",\"ridge\":518,\"a\":33,\"owners\":[80,82,83]},{\"tag\":\"mate\",\"ridge\":518,\"a\":34,\"owners\":[80,82]},{\"tag\":\"three\",\"ridge\":518,\"vertices\":[29,82,86]},{\"tag\":\"mate\",\"ridge\":81,\"a\":45,\"owners\":[14,57,70,76]},{\"tag\":\"mate\",\"ridge\":146,\"a\":28,\"owners\":[87,88,91,92]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[8,10,25]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[9,10,25]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[9,10,51]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[10,25,48]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[10,25,49]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[10,25,51]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[10,25,52]},{\"tag\":\"mate\",\"ridge\":321,\"a\":67,\"owners\":[8,48,51,53,70,72,76,77]},{\"tag\":\"mate\",\"ridge\":321,\"a\":76,\"owners\":[8,32,51,54,63,67,72]},{\"tag\":\"mate\",\"ridge\":321,\"a\":77,\"owners\":[8,32,48,54,63,67,70]},{\"tag\":\"mate\",\"ridge\":322,\"a\":53,\"owners\":[86]},{\"tag\":\"three\",\"ridge\":322,\"vertices\":[51,86,92]},{\"tag\":\"mate\",\"ridge\":385,\"a\":18,\"owners\":[9,49,52,53,55,76,77]},{\"tag\":\"three\",\"ridge\":385,\"vertices\":[18,55,76]},{\"tag\":\"three\",\"ridge\":385,\"vertices\":[18,55,77]},{\"tag\":\"three\",\"ridge\":385,\"vertices\":[55,71,77]},{\"tag\":\"three\",\"ridge\":385,\"vertices\":[55,73,76]},{\"tag\":\"mate\",\"ridge\":386,\"a\":49,\"owners\":[89,90,93]},{\"tag\":\"mate\",\"ridge\":386,\"a\":88,\"owners\":[9,52,53,55,93]},{\"tag\":\"mate\",\"ridge\":386,\"a\":92,\"owners\":[9,42,52,55,89,90]},{\"tag\":\"mate\",\"ridge\":386,\"a\":93,\"owners\":[9,42,49,55,88,90]},{\"tag\":\"three\",\"ridge\":386,\"vertices\":[55,88,93]},{\"tag\":\"three\",\"ridge\":386,\"vertices\":[55,89,92]},{\"tag\":\"three\",\"ridge\":769,\"vertices\":[19,55,67]},{\"tag\":\"mate\",\"ridge\":770,\"a\":10,\"owners\":[83,86,90]},{\"tag\":\"mate\",\"ridge\":770,\"a\":34,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":770,\"a\":54,\"owners\":[83,90]},{\"tag\":\"mate\",\"ridge\":770,\"a\":55,\"owners\":[83,86]},{\"tag\":\"mate\",\"ridge\":770,\"a\":83,\"owners\":[10,54,55]},{\"tag\":\"mate\",\"ridge\":770,\"a\":86,\"owners\":[10,44,55,90]},{\"tag\":\"mate\",\"ridge\":524,\"a\":13,\"owners\":[80,82,83]},{\"tag\":\"mate\",\"ridge\":524,\"a\":26,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":524,\"a\":59,\"owners\":[82,83]},{\"tag\":\"mate\",\"ridge\":524,\"a\":62,\"owners\":[80,83]},{\"tag\":\"mate\",\"ridge\":524,\"a\":64,\"owners\":[80,82]},{\"tag\":\"mate\",\"ridge\":392,\"a\":42,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":392,\"a\":71,\"owners\":[89,90]},{\"tag\":\"mate\",\"ridge\":776,\"a\":19,\"owners\":[83,90]},{\"tag\":\"mate\",\"ridge\":776,\"a\":44,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":776,\"a\":64,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":776,\"a\":74,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":270,\"a\":83,\"owners\":[25]},{\"tag\":\"mate\",\"ridge\":282,\"a\":88,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":554,\"a\":41,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":332,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":836,\"a\":67,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":836,\"a\":86,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":344,\"a\":70,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":360,\"a\":72,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":464,\"a\":76,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":464,\"a\":92,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":480,\"a\":77,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":480,\"a\":93,\"owners\":[77]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[44,64,74],\"full_literals\":[-68,32,48,54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[57,59,60,62],\"full_literals\":[-69,43,44,45,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[26,29,31,33,34],\"full_literals\":[-70,14,17,19,21,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[32,48,51,53,54,55],\"full_literals\":[-71,20,35,38,40,41,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[28,36,47,49,52],\"full_literals\":[-72,16,24,34,36,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[23,30,39,50],\"full_literals\":[-73,12,18,27,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[22,42],\"full_literals\":[-74,11,30]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-75,68,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-76,69,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-76,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-77,75,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-78,75,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-79,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,73,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-81,false,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-82,72,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-82,false,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-83,false,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-84,79,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-85,79,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-84,false,82],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-85,false,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-86,77,85],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-86,78,84],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[25,63,67],\"full_literals\":[-87,13,47,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":25,\"full_literals\":[-13,87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":67,\"full_literals\":[-49,87]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[83,86],\"full_literals\":[-88,59,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-59,88]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-89,87,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-87,-88,89],\"grouped\":true,\"kind\":3},{\"tag\":\"edge\",\"edge\":23,\"owners\":[3,13,26,29,31,33,34,59,62,64,67,80,82,83,86]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[18,19,25,37,40,42,44,63,64,70,71,72,73,74,83,88,89,90]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[13,19,26,38,41,43,44,59,62,64,74,80,82,83,90]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[8,32,48,51,53,54,63,67,70,72,76,77,86,92,93]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[9,18,42,49,52,53,55,71,73,74,76,77,88,89,90,92,93]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[10,19,34,44,54,55,64,67,74,83,86,90]}]}"
  "177 -68 48 54 0 124 139 0\n178 -70 17 19 21 22 0 117 141 0\n179 -74 11 0 121 145 0\n180 -87 13 49 0 130 164 0\n181 2 7 17 19 21 22 44 46 48 49 57 58 59 60 0 117 171 0\n182 9 10 13 25 28 48 51 53 54 59 62 63 64 0 121 124 130 133 134 172 0\n183 7 10 26 29 31 44 46 48 54 57 58 59 64 0 117 124 173 0\n184 4 20 35 38 40 41 49 55 56 60 66 67 0 130 133 134 174 0\n185 5 9 36 39 40 42 51 53 54 55 56 62 63 64 66 67 0 121 175 0\n186 6 10 22 41 42 48 49 54 59 60 64 0 124 176 0\n187 -88 89 0 170 165 166 127 132 167 0\n188 60 -88 0 121 133 134 130 187 169 96 131 167 180 42 50 52 60 28 30 114 86 87 89 90 91 92 106 105 95 94 184 0\n189 79 -60 0 163 48 49 126 177 146 150 162 46 45 158 157 161 156 149 153 148 179 2 6 178 0\n190 -11 -70 -60 0 46 45 2 6 178 0\n191 35 38 40 55 56 -60 0 134 133 189 151 132 47 44 93 142 29 0\n192 19 -76 -35 55 -60 0 163 133 48 49 126 177 146 150 162 159 148 190 179 153 154 147 17 14 132 46 45 178 1 3 4 5 13 35 37 77 83 140 129 76 84 73 74 75 143 0\n193 -76 -35 55 -60 0 163 16 15 18 17 48 49 126 177 146 150 162 159 155 148 190 179 153 152 154 192 7 8 144 10 21 143 0\n194 -11 -60 0 49 126 48 9 11 12 36 38 40 41 53 116 123 183 0\n195 64 40 66 67 -60 0 163 124 137 135 48 49 126 177 146 194 179 153 156 160 161 149 193 191 51 39 33 22 115 122 103 88 98 104 185 0\n196 40 66 67 -60 0 163 135 48 49 126 177 146 194 179 153 156 160 161 149 193 137 150 162 159 155 152 191 19 20 195 54 56 144 0\n197 66 67 -60 0 163 124 48 49 126 177 146 150 162 159 194 179 153 154 196 23 24 25 26 27 34 62 115 128 55 61 143 85 0\n198 -66 -60 0 189 151 49 126 132 48 47 44 43 63 64 65 66 67 136 97 142 32 57 99 102 108 109 182 0\n199 -60 0 163 43 44 47 48 49 132 126 177 146 189 151 194 179 153 156 160 161 149 198 135 197 193 68 69 70 71 72 138 142 31 57 100 101 107 109 182 0\n200 -49 0 199 131 0\n201 -88 0 199 188 0\n202 -59 0 201 168 0\n203 -54 0 202 126 0\n204 -42 0 202 199 113 0\n205 64 0 199 202 203 200 204 111 125 112 123 110 186 0\n206 -57 0 205 58 0\n207 -58 0 205 59 0\n208 -21 0 206 207 202 81 0\n209 -22 0 206 207 82 0\n210 -7 0 206 207 202 116 0\n211 -46 0 206 202 119 0\n212 -2 0 206 207 202 199 78 0\n213 -19 0 206 202 199 80 0\n214 -17 0 207 202 199 79 0\n215 -44 0 207 202 118 0\n216 -48 0 207 206 120 0\n217 0 210 214 216 213 208 209 212 215 211 200 206 207 202 199 181 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record015
