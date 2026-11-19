module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow25Part00000Data
public import GraphInputsRow25Part00000Frames
public import GraphInputsRow25Part00000Leaves
public import GraphInputsRow25Part00000Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00000.record057
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 387309567953862656, (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10), (certNat% 11), (certNat% 12), (certNat% 13)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 3), (certNat% 6), (certNat% 15), (certNat% 16), 90071996842377216, (certNat% 17)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 20), (certNat% 21), 37383395344384, (certNat% 22)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), (certNat% 6), (certNat% 25), 270215983010938880, (certNat% 13), 2199023255552]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 8), (certNat% 27), (certNat% 28), (certNat% 29), (certNat% 30)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), (certNat% 33), (certNat% 34), (certNat% 35), (certNat% 27), 90071996842377216]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), (certNat% 37), (certNat% 38), (certNat% 39), (certNat% 40), (certNat% 24), 281509336449024, 450359967032016896]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00000.record057

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00000.record050
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2b8d325cf0b92d2a9a968ba699962d94e1b85ef0791ac749aa699966392e74569715656552d70d9354d1b61d17783d0ec370da3c4e9364e53c2e8b92d4b2ac6b86c9b16d8749ca719d1725c5743c3c2c83a518361382e07b81d06912c64986439514351342d0758350ca324c3312c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db69b49249269249b6d349249349a4db492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 67), (facetIndex 69)]))
 (.leaf ([(facetIndex 48), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 84), (facetIndex 85)]))
 (.leaf ([(facetIndex 88), (facetIndex 94)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 64), (facetIndex 66), (facetIndex 68)]))
 (.leaf ([(facetIndex 92), (facetIndex 93)])))
 (.branch 7
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 53), (facetIndex 56)]))
 (.leaf ([(facetIndex 87), (facetIndex 89), (facetIndex 90), (facetIndex 91)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "edffbe120000002000041040000060301b1z24;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00000.record050" "{\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00000.record050" 54

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00000.record050" "{\"ridges\":[[19,529],[19,536],[20,584],[22,656],[23,832],[24,641],[24,896],[43,536],[47,584],[48,650],[49,778],[52,656],[53,786],[56,706],[57,832],[58,896],[60,529],[60,536],[63,584],[68,788],[70,832],[72,529],[72,536],[73,536],[74,536],[74,656],[75,680],[76,584],[76,832],[77,656],[78,656],[78,896],[79,896],[87,594],[88,650],[89,778],[90,786],[91,706],[94,680]],\"owners\":[[19,529,[22,50,52,53,66,68,77,78],[43,60,72,73]],[60,529,[22,50,52,53,77,78],[19,43,66,68,72,73]],[72,529,[22,50,52,53,66,68,78],[19,43,60,73,77]],[19,536,[87,88,92,94],[43,60,72,73,74]],[43,536,[92,94],[19,60,72,73,74,87,88]],[60,536,[87,88,94],[19,43,72,73,74,92]],[72,536,[87,88,92],[19,43,60,73,74,94]],[73,536,[88,94],[19,43,60,72,74,87,92]],[74,536,[87,92],[19,43,60,72,73,88,94]],[20,584,[87,89,92,93],[47,63,73,76]],[47,584,[92,93],[20,63,73,76,87,89]],[63,584,[87,89],[20,47,73,76,92,93]],[76,584,[87,92],[20,47,63,73,89,93]],[24,641,[22,48,52,56,74,75,77],[58,79]],[22,656,[88,90,94],[52,74,77,78]],[52,656,[94],[22,74,77,78,88,90]],[74,656,[90],[22,52,77,78,88,94]],[77,656,[88,90],[22,52,74,78,94]],[78,656,[88,94],[22,52,74,77,90]],[23,832,[89,91,93],[57,70,76,79]],[57,832,[93],[23,70,76,79,89,91]],[70,832,[89,91],[23,57,76,79,93]],[76,832,[91],[23,57,70,79,89,93]],[24,896,[90,91],[58,78,79]],[58,896,[],[24,78,79,90,91]],[78,896,[91],[24,58,79,90]],[79,896,[90],[24,58,78,91]],[48,650,[88],[]],[88,650,[48],[]],[49,778,[89],[]],[89,778,[49],[]],[87,594,[50],[]],[53,786,[90],[]],[90,786,[53],[]],[56,706,[91],[]],[91,706,[56],[]],[68,788,[],[]],[75,680,[94],[]],[94,680,[75],[]]],\"edges\":[[29,[19,20,43,47,48,49,60,63,64,72,73,74,75,76,87,88,89,92,93,94]],[34,[19,22,43,50,52,53,60,66,68,72,73,74,77,78,87,88,90,92,94]],[43,[22,24,48,52,56,58,74,75,77,78,79,88,90,91,94]],[44,[23,24,49,53,57,58,64,68,70,76,78,79,89,90,91,93]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00000.record050" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00000.record050\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-10],[-33,-9],[-33,-30],[-33,-32],[-34,-10],[-1,3,10,11,12,19,20,27,28],[-16,3,10,11,12,27,28],[-22,3,10,11,12,19,20,28],[-1,30,31,35,37],[-6,35,37],[-16,30,31,37],[-22,30,31,35],[-23,31,37],[-24,30,35],[-2,30,32,35,36],[-7,35,36],[-17,30,32],[-26,30,35],[-5,3,8,11,13,24,25,27],[-3,31,33,37],[-11,37],[-24,33],[-27,31,33],[-28,31,37],[-4,32,34,36],[-14,36],[-21,32,34],[-26,34],[-5,33,34],[-15],[-28,34],[-29,33],[-8,31],[-31,8],[-9,32],[-32,9],[-30,10],[-12,33],[-33,12],[-13,34],[-34,13],[-20],[-25,37],[-37,25],[-8,38],[-25,38],[-31,39],[-37,39],[-18,40],[-19,40],[-35,41],[-36,41],[-9,42],[-12,42],[-13,42],[-43,30,32,33,34],[-32,43],[-33,43],[-34,43],[-38,44],[-39,45],[-45,46],[-44,46],[-44,-45,47],[-41,48],[-40,48],[-43,49],[-42,-43,50],[-49,51],[-50,52],[-48,51],[-48,-50,53],[-53,54],[-46,-52,54],[-47,-51,54],[-54],[1,2,6,7,8,9,16,17,18,22,23,24,25,26,30,31,32,35,36,37],[1,3,6,10,11,12,16,19,20,22,23,24,27,28,30,31,33,35,37],[3,5,8,11,13,15,24,25,27,28,29,31,33,34,37],[4,5,9,12,14,15,18,20,21,26,28,29,32,33,34,36]],\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":56,\"b\":50},{\"tag\":\"incompatible\",\"a\":90,\"b\":49},{\"tag\":\"incompatible\",\"a\":90,\"b\":87},{\"tag\":\"incompatible\",\"a\":90,\"b\":89},{\"tag\":\"incompatible\",\"a\":91,\"b\":50},{\"tag\":\"mate\",\"ridge\":529,\"a\":19,\"owners\":[22,50,52,53,66,68,77,78]},{\"tag\":\"mate\",\"ridge\":529,\"a\":60,\"owners\":[22,50,52,53,77,78]},{\"tag\":\"mate\",\"ridge\":529,\"a\":72,\"owners\":[22,50,52,53,66,68,78]},{\"tag\":\"mate\",\"ridge\":536,\"a\":19,\"owners\":[87,88,92,94]},{\"tag\":\"mate\",\"ridge\":536,\"a\":43,\"owners\":[92,94]},{\"tag\":\"mate\",\"ridge\":536,\"a\":60,\"owners\":[87,88,94]},{\"tag\":\"mate\",\"ridge\":536,\"a\":72,\"owners\":[87,88,92]},{\"tag\":\"mate\",\"ridge\":536,\"a\":73,\"owners\":[88,94]},{\"tag\":\"mate\",\"ridge\":536,\"a\":74,\"owners\":[87,92]},{\"tag\":\"mate\",\"ridge\":584,\"a\":20,\"owners\":[87,89,92,93]},{\"tag\":\"mate\",\"ridge\":584,\"a\":47,\"owners\":[92,93]},{\"tag\":\"mate\",\"ridge\":584,\"a\":63,\"owners\":[87,89]},{\"tag\":\"mate\",\"ridge\":584,\"a\":76,\"owners\":[87,92]},{\"tag\":\"mate\",\"ridge\":641,\"a\":24,\"owners\":[22,48,52,56,74,75,77]},{\"tag\":\"mate\",\"ridge\":656,\"a\":22,\"owners\":[88,90,94]},{\"tag\":\"mate\",\"ridge\":656,\"a\":52,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":656,\"a\":74,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":656,\"a\":77,\"owners\":[88,90]},{\"tag\":\"mate\",\"ridge\":656,\"a\":78,\"owners\":[88,94]},{\"tag\":\"mate\",\"ridge\":832,\"a\":23,\"owners\":[89,91,93]},{\"tag\":\"mate\",\"ridge\":832,\"a\":57,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":832,\"a\":70,\"owners\":[89,91]},{\"tag\":\"mate\",\"ridge\":832,\"a\":76,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":896,\"a\":24,\"owners\":[90,91]},{\"tag\":\"mate\",\"ridge\":896,\"a\":58,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":896,\"a\":78,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":896,\"a\":79,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":650,\"a\":48,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":650,\"a\":88,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":778,\"a\":49,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":778,\"a\":89,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":594,\"a\":87,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":786,\"a\":53,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":786,\"a\":90,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":706,\"a\":56,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":706,\"a\":91,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":788,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":680,\"a\":75,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":680,\"a\":94,\"owners\":[75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":48,\"full_literals\":[-8,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":75,\"full_literals\":[-25,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":88,\"full_literals\":[-31,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":94,\"full_literals\":[-37,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":64,\"full_literals\":[-18,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":66,\"full_literals\":[-19,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":92,\"full_literals\":[-35,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":93,\"full_literals\":[-36,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":49,\"full_literals\":[-9,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":53,\"full_literals\":[-12,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":56,\"full_literals\":[-13,42]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[87,89,90,91],\"full_literals\":[-43,30,32,33,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":89,\"full_literals\":[-32,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":90,\"full_literals\":[-33,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":91,\"full_literals\":[-34,43]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-45,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-43,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-50,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-48,-50,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-53,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-46,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-51,54],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[19,20,43,47,48,49,60,63,64,72,73,74,75,76,87,88,89,92,93,94]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[19,22,43,50,52,53,60,66,68,72,73,74,77,78,87,88,90,92,94]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[22,24,48,52,56,58,74,75,77,78,79,88,90,91,94]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[23,24,49,53,57,58,64,68,70,76,78,79,89,90,91,93]}]}"
  "81 -53 0 76 73 0\n82 1 3 6 10 11 12 16 19 22 23 24 27 28 30 31 33 35 37 0 42 78 0\n83 3 5 8 11 13 24 25 27 28 29 31 33 34 37 0 30 79 0\n84 4 5 9 12 14 18 21 26 28 29 32 33 34 36 0 30 42 80 0\n85 -10 33 46 0 62 61 47 48 20 23 32 22 21 24 63 60 46 45 1 5 19 83 0\n86 1 10 37 6 11 12 3 19 16 23 24 27 28 30 31 33 35 0 42 82 8 0\n87 33 48 46 0 42 62 61 48 65 51 10 66 50 21 47 24 13 22 38 23 20 85 37 7 6 86 0\n88 48 46 0 62 61 48 47 13 63 60 46 45 65 66 51 52 49 10 16 87 2 3 4 11 12 9 14 18 17 15 77 0\n89 -33 50 0 39 58 54 68 0\n90 -43 46 0 81 88 72 89 85 37 68 53 55 36 41 56 0\n91 46 0 81 62 63 61 60 47 48 45 46 24 21 88 72 89 22 32 23 20 90 59 40 29 83 0\n92 -52 0 91 76 74 0\n93 -50 0 92 70 0\n94 -33 0 93 89 0\n95 -24 0 94 22 0\n96 -29 0 94 32 0\n97 -12 0 94 38 0\n98 37 31 34 0 95 94 96 23 33 29 40 31 21 43 20 83 0\n99 -37 47 0 44 48 46 61 60 64 0\n100 47 34 0 99 98 34 47 45 61 60 64 0\n101 43 0 76 94 96 97 57 59 35 28 31 27 29 100 75 71 65 66 52 49 26 25 84 0\n102 49 0 101 67 0\n103 -42 0 101 93 68 0\n104 51 0 102 69 0\n105 -13 0 103 55 0\n106 -47 0 104 76 75 0\n107 -34 0 105 41 0\n108 0 106 107 100 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050 Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00000.record050
