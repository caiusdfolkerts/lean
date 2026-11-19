module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00080Data
public import GraphInputsRow26Part00080Frames
public import GraphInputsRow26Part00080Leaves
public import GraphInputsRow26Part00080Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00080.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record022
def vertexColumn : Fields := ⟨10, hexnat% "ae0f83d0ec3723c2f07cccab26caaa9a8eaa6a3a2e96639a364d8b633a2e2b86e8791e2783ecc6b16c4f1a64d9594e5356354d4b51d4cd8751d2745dc8ea368e6358ce3c4e9364e334ccb3a2e4b86d1b26d4731e2749ca719e1745c970de0f43c8f07d34388ca49866138c9864994544d074c382c8b12d0711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6da6da4d34da6db6db49b6d369249b6da6db6d24d24d34d3692449249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨44, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11a800425c103baa780000", 9232379236109516800, hexnat% "1000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a800425c1033aa780000", hexnat% "101000000000000000000", 9232379270469255168, hexnat% "1000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [167776891618983936, hexnat% "181000000000000000000", 13846317062940524544, hexnat% "20000000000800000000", hexnat% "1008000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "108800404c101280380000", 171802886144, 9236882835736887296, hexnat% "101000000000108000000", hexnat% "20000200000022000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1088000040100080200000", hexnat% "20000200000022000000", hexnat% "101000000000108000000", 9240260535457939456, 4611686164457324544, 103083409408]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c7 c4
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00080.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00080.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record024
def vertexColumn : Fields := ⟨10, hexnat% "37332ac9b2caa6a5ab1a368d68d9362d8ce8b92e1ba1e4789e17b31ac5b1ca6695a719364d58d5352d4cd8b52d1b61d4749d17723a8da398d6338f13a4d9334e334ccb3c2e4b52ccb8ad2b1ae1b46c9b16cc789d2729c6785d1725c570de0f43c8f13c2f07ce438a1a468c6298662584e078e186519314a5194951341d"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6da69b49b4924db6da69b49b4924db6d36db6db6db69369b49b4db6d3449249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨21, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨53, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4c9804c1800000488000000", 9223372037930614784, 9007611572125696, hexnat% "100600000000000000000000", hexnat% "1006000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4c980449800000440200000", hexnat% "80000000088000000", 9007611572125696, hexnat% "100600000000000000000000", hexnat% "1006000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44800008000000440200000", hexnat% "8000080000000088000000", 9007611572125696, hexnat% "1007800000000000000", hexnat% "100780000000000000000000", hexnat% "440000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record024_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00080.record024

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00080.record015
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "338ad0f49b0ec8f1b23c96a3a93a358ce8791ecc6b16c4f1ca6695a4e9c66394e6a5994e5a54d58d4b51d64d3362d2b46d8751d0f5a358ce364cd34ccb31cd4b32d2b2ac6b86d1b0ee1745c5783d0f23c1f31896138e18c5312c6294a469316152560d134c344c9342c4b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db6d26d249249a4da4926926936da49269269a692492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 31), (facetIndex 33), (facetIndex 47), (facetIndex 48), (facetIndex 65)]))
 (.branch 2
 (.leaf ([(facetIndex 35), (facetIndex 39), (facetIndex 45), (facetIndex 46), (facetIndex 78)]))
 (.leaf ([(facetIndex 51), (facetIndex 55), (facetIndex 61), (facetIndex 62), (facetIndex 83)]))))
 (.branch 4
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 88)]))
 (.branch 5
 (.leaf ([(facetIndex 79), (facetIndex 80), (facetIndex 81), (facetIndex 82)]))
 (.leaf ([(facetIndex 84), (facetIndex 85), (facetIndex 86), (facetIndex 87)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "3b6d5248406c00000000900004004000480002002z1a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4, 5]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00080.record015" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00080.record015" 61

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00080.record015" "{\"ridges\":[[5,11],[5,266],[7,274],[10,521],[10,524],[12,532],[15,41],[15,296],[16,41],[16,552],[18,304],[19,560],[26,266],[27,11],[27,524],[29,274],[30,532],[31,11],[31,41],[32,266],[32,274],[33,538],[36,266],[36,296],[38,266],[41,274],[41,304],[43,274],[45,354],[46,418],[48,284],[52,524],[52,552],[54,524],[57,532],[57,560],[59,532],[61,612],[62,676],[63,296],[63,304],[65,792],[67,296],[68,552],[69,296],[69,552],[71,304],[72,560],[73,304],[73,560],[74,284],[75,538],[78,58],[78,266],[78,296],[84,172],[85,552],[85,612],[86,116],[87,676],[88,792]],\"owners\":[[5,266,[74,78,80],[26,32,36,38]],[26,266,[78,80],[5,32,36,38,74]],[32,266,[80],[5,26,36,38,74,78]],[36,266,[74],[5,26,32,38,78,80]],[38,266,[74,78],[5,26,32,36,80]],[78,266,[5,26,38],[32,36,74,80]],[7,274,[74,78,82],[29,32,41,43]],[29,274,[78,82],[7,32,41,43,74]],[32,274,[82],[7,29,41,43,74,78]],[41,274,[74],[7,29,32,43,78,82]],[43,274,[74,78],[7,29,32,41,82]],[10,521,[16,33,64,65,68,69],[27,49,54]],[10,524,[75,83,85],[27,49,52,54]],[27,524,[83,85],[10,49,52,54,75]],[52,524,[75],[10,27,49,54,83,85]],[54,524,[75,83],[10,27,49,52,85]],[12,532,[75,83,87],[30,49,57,59]],[30,532,[83,87],[12,49,57,59,75]],[57,532,[75],[12,30,49,59,83,87]],[59,532,[75,83],[12,30,49,57,87]],[15,296,[78,80,88],[36,63,67,69]],[36,296,[88],[15,63,67,69,78,80]],[63,296,[80],[15,36,67,69,78,88]],[67,296,[78,88],[15,36,63,69,80]],[69,296,[78,80],[15,36,63,67,88]],[78,296,[15,67,69],[36,63,80,88]],[16,552,[83,85,88],[52,64,68,69]],[52,552,[88],[16,64,68,69,83,85]],[68,552,[83,88],[16,52,64,69,85]],[69,552,[83,85],[16,52,64,68,88]],[85,552,[16,64,69,88],[52,68,83]],[18,304,[78,82,88],[41,63,71,73]],[41,304,[88],[18,63,71,73,78,82]],[63,304,[82],[18,41,71,73,78,88]],[71,304,[78,88],[18,41,63,73,82]],[73,304,[78,82],[18,41,63,71,88]],[19,560,[83,87,88],[57,64,72,73]],[57,560,[88],[19,64,72,73,83,87]],[72,560,[83,88],[19,57,64,73,87]],[73,560,[83,87],[19,57,64,72,88]],[78,58,[31],[]],[33,538,[75],[]],[75,538,[33],[]],[45,354,[80],[]],[46,418,[82],[]],[48,284,[74],[]],[74,284,[48],[]],[84,172,[51],[]],[86,116,[55],[]],[61,612,[85],[]],[85,612,[61],[]],[62,676,[87],[]],[87,676,[62],[]],[65,792,[88],[]],[88,792,[65],[]]],\"edges\":[[8,[10,12,16,19,27,30,33,49,52,54,57,59,61,62,64,65,68,69,72,73]],[15,[5,7,26,29,32,36,38,41,43,45,46,74,78,80,82]],[23,[10,12,27,30,49,52,54,57,59,61,62,75,83,85,87]],[28,[5,15,26,32,36,38,48,63,65,67,69,74,78,80,88]],[29,[10,16,27,33,49,52,54,64,65,68,69,75,83,85,88]],[33,[7,18,29,32,41,43,48,63,65,71,73,74,78,82,88]],[37,[15,18,36,41,45,46,63,67,69,71,73,78,80,82,88]],[38,[16,19,52,57,61,62,64,68,69,72,73,83,85,87,88]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00080.record015" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00080.record015\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-9],[-15,-9],[-17,-13],[-22,-10],[-22,-12],[-35,-13],[-37,-13],[-41,-23],[-41,-32],[-41,-33],[-42,-14],[-42,-22],[-42,-32],[-42,-33],[-42,-41],[-43,-23],[-43,-33],[-43,-41],[-43,-42],[-45,-44],[-46,-41],[-46,-42],[-46,-43],[-51,-14],[-51,-23],[-51,-41],[-51,-42],[-51,-43],[-51,-46],[-1,-10,-13],[-1,41,43,44],[-9,43,44],[-14,44],[-16,41],[-17,41,43],[-43,1,9,17],[-2,41,43,45],[-11,43,45],[-14,45],[-18,41],[-19,41,43],[-3,6,15,33,34,36,37],[-3,42,46,48],[-10,46,48],[-25,42],[-26,42,46],[-4,42,46,50],[-12,46,50],[-28,42],[-29,42,46],[-5,-6,-13],[-5,43,44,51],[-16,51],[-32,44],[-35,43,51],[-37,43,44],[-43,5,35,37],[-6,46,48,51],[-25,51],[-36,46,51],[-37,46,48],[-48,6,33,37,51],[-7,43,45,51],[-18,51],[-32,45],[-38,43,51],[-40,43,45],[-8,46,50,51],[-28,51],[-39,46,51],[-40,46,50],[-43,13],[-15,42],[-42,15],[-20,44],[-21,45],[-22,41],[-41,22],[-47,24],[-49,27],[-30,48],[-48,30],[-31,50],[-50,31],[-34,51],[-51,34],[-15,52],[-22,52],[-34,52],[-24,53],[-27,53],[-30,53],[-31,53],[-54,41,42,51],[-41,54],[-42,54],[-51,54],[-44,55],[-45,55],[-56,47,48,49,50],[-48,56],[-50,56],[-53,57],[-52,-57,58],[-59,56],[-55,-56,59],[-60,54],[-60,59],[-54,-59,60],[-58,-60,61],[-61],[3,4,6,8,10,12,15,23,25,26,28,29,30,31,33,34,36,37,39,40],[1,2,9,11,14,16,17,18,19,20,21,41,43,44,45],[3,4,10,12,23,25,26,28,29,30,31,42,46,48,50],[1,5,9,14,16,17,22,32,34,35,37,41,43,44,51],[3,6,10,15,23,25,26,33,34,36,37,42,46,48,51],[2,7,11,14,18,19,22,32,34,38,40,41,43,45,51],[5,7,16,18,20,21,32,35,37,38,40,43,44,45,51],[6,8,25,28,30,31,33,36,37,39,40,46,48,50,51]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":31,\"b\":26},{\"tag\":\"incompatible\",\"a\":33,\"b\":26},{\"tag\":\"incompatible\",\"a\":38,\"b\":31},{\"tag\":\"incompatible\",\"a\":48,\"b\":27},{\"tag\":\"incompatible\",\"a\":48,\"b\":30},{\"tag\":\"incompatible\",\"a\":67,\"b\":31},{\"tag\":\"incompatible\",\"a\":69,\"b\":31},{\"tag\":\"incompatible\",\"a\":74,\"b\":49},{\"tag\":\"incompatible\",\"a\":74,\"b\":63},{\"tag\":\"incompatible\",\"a\":74,\"b\":64},{\"tag\":\"incompatible\",\"a\":75,\"b\":32},{\"tag\":\"incompatible\",\"a\":75,\"b\":48},{\"tag\":\"incompatible\",\"a\":75,\"b\":63},{\"tag\":\"incompatible\",\"a\":75,\"b\":64},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":78,\"b\":49},{\"tag\":\"incompatible\",\"a\":78,\"b\":64},{\"tag\":\"incompatible\",\"a\":78,\"b\":74},{\"tag\":\"incompatible\",\"a\":78,\"b\":75},{\"tag\":\"incompatible\",\"a\":82,\"b\":80},{\"tag\":\"incompatible\",\"a\":83,\"b\":74},{\"tag\":\"incompatible\",\"a\":83,\"b\":75},{\"tag\":\"incompatible\",\"a\":83,\"b\":78},{\"tag\":\"incompatible\",\"a\":88,\"b\":32},{\"tag\":\"incompatible\",\"a\":88,\"b\":49},{\"tag\":\"incompatible\",\"a\":88,\"b\":74},{\"tag\":\"incompatible\",\"a\":88,\"b\":75},{\"tag\":\"incompatible\",\"a\":88,\"b\":78},{\"tag\":\"incompatible\",\"a\":88,\"b\":83},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[5,27,31]},{\"tag\":\"mate\",\"ridge\":266,\"a\":5,\"owners\":[74,78,80]},{\"tag\":\"mate\",\"ridge\":266,\"a\":26,\"owners\":[78,80]},{\"tag\":\"mate\",\"ridge\":266,\"a\":32,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":266,\"a\":36,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":266,\"a\":38,\"owners\":[74,78]},{\"tag\":\"mate\",\"ridge\":266,\"a\":78,\"owners\":[5,26,38]},{\"tag\":\"mate\",\"ridge\":274,\"a\":7,\"owners\":[74,78,82]},{\"tag\":\"mate\",\"ridge\":274,\"a\":29,\"owners\":[78,82]},{\"tag\":\"mate\",\"ridge\":274,\"a\":32,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":274,\"a\":41,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":274,\"a\":43,\"owners\":[74,78]},{\"tag\":\"mate\",\"ridge\":521,\"a\":10,\"owners\":[16,33,64,65,68,69]},{\"tag\":\"mate\",\"ridge\":524,\"a\":10,\"owners\":[75,83,85]},{\"tag\":\"mate\",\"ridge\":524,\"a\":27,\"owners\":[83,85]},{\"tag\":\"mate\",\"ridge\":524,\"a\":52,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":524,\"a\":54,\"owners\":[75,83]},{\"tag\":\"mate\",\"ridge\":532,\"a\":12,\"owners\":[75,83,87]},{\"tag\":\"mate\",\"ridge\":532,\"a\":30,\"owners\":[83,87]},{\"tag\":\"mate\",\"ridge\":532,\"a\":57,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":532,\"a\":59,\"owners\":[75,83]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[15,16,31]},{\"tag\":\"mate\",\"ridge\":296,\"a\":15,\"owners\":[78,80,88]},{\"tag\":\"mate\",\"ridge\":296,\"a\":36,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":296,\"a\":63,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":296,\"a\":67,\"owners\":[78,88]},{\"tag\":\"mate\",\"ridge\":296,\"a\":69,\"owners\":[78,80]},{\"tag\":\"mate\",\"ridge\":296,\"a\":78,\"owners\":[15,67,69]},{\"tag\":\"mate\",\"ridge\":552,\"a\":16,\"owners\":[83,85,88]},{\"tag\":\"mate\",\"ridge\":552,\"a\":52,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":552,\"a\":68,\"owners\":[83,88]},{\"tag\":\"mate\",\"ridge\":552,\"a\":69,\"owners\":[83,85]},{\"tag\":\"mate\",\"ridge\":552,\"a\":85,\"owners\":[16,64,69,88]},{\"tag\":\"mate\",\"ridge\":304,\"a\":18,\"owners\":[78,82,88]},{\"tag\":\"mate\",\"ridge\":304,\"a\":41,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":304,\"a\":63,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":304,\"a\":71,\"owners\":[78,88]},{\"tag\":\"mate\",\"ridge\":304,\"a\":73,\"owners\":[78,82]},{\"tag\":\"mate\",\"ridge\":560,\"a\":19,\"owners\":[83,87,88]},{\"tag\":\"mate\",\"ridge\":560,\"a\":57,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":560,\"a\":72,\"owners\":[83,88]},{\"tag\":\"mate\",\"ridge\":560,\"a\":73,\"owners\":[83,87]},{\"tag\":\"mate\",\"ridge\":58,\"a\":78,\"owners\":[31]},{\"tag\":\"mate\",\"ridge\":538,\"a\":33,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":538,\"a\":75,\"owners\":[33]},{\"tag\":\"mate\",\"ridge\":354,\"a\":45,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":418,\"a\":46,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":284,\"a\":48,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":284,\"a\":74,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":172,\"a\":84,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":116,\"a\":86,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":612,\"a\":61,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":612,\"a\":85,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":676,\"a\":62,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":676,\"a\":87,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":792,\"a\":65,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":792,\"a\":88,\"owners\":[65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":33,\"full_literals\":[-15,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":48,\"full_literals\":[-22,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":65,\"full_literals\":[-34,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":51,\"full_literals\":[-24,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":55,\"full_literals\":[-27,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":61,\"full_literals\":[-30,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":62,\"full_literals\":[-31,53]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[74,75,88],\"full_literals\":[-54,41,42,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":74,\"full_literals\":[-41,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":75,\"full_literals\":[-42,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":88,\"full_literals\":[-51,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-44,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":82,\"full_literals\":[-45,55]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[84,85,86,87],\"full_literals\":[-56,47,48,49,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-48,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-50,56]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-56,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-60,54,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-54,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-58,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":8,\"owners\":[10,12,16,19,27,30,33,49,52,54,57,59,61,62,64,65,68,69,72,73]},{\"tag\":\"edge\",\"edge\":15,\"owners\":[5,7,26,29,32,36,38,41,43,45,46,74,78,80,82]},{\"tag\":\"edge\",\"edge\":23,\"owners\":[10,12,27,30,49,52,54,57,59,61,62,75,83,85,87]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[5,15,26,32,36,38,48,63,65,67,69,74,78,80,88]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[10,16,27,33,49,52,54,64,65,68,69,75,83,85,88]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[7,18,29,32,41,43,48,63,65,71,73,74,78,82,88]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[15,18,36,41,45,46,63,67,69,71,73,78,80,82,88]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[16,19,52,57,61,62,64,68,69,72,73,83,85,87,88]}]}"
  "p cnf 61 119\n-13 -9 0\n-15 -9 0\n-17 -13 0\n-22 -10 0\n-22 -12 0\n-35 -13 0\n-37 -13 0\n-41 -23 0\n-41 -32 0\n-41 -33 0\n-42 -14 0\n-42 -22 0\n-42 -32 0\n-42 -33 0\n-42 -41 0\n-43 -23 0\n-43 -33 0\n-43 -41 0\n-43 -42 0\n-45 -44 0\n-46 -41 0\n-46 -42 0\n-46 -43 0\n-51 -14 0\n-51 -23 0\n-51 -41 0\n-51 -42 0\n-51 -43 0\n-51 -46 0\n-1 -10 -13 0\n-1 41 43 44 0\n-9 43 44 0\n-14 44 0\n-16 41 0\n-17 41 43 0\n-43 1 9 17 0\n-2 41 43 45 0\n-11 43 45 0\n-14 45 0\n-18 41 0\n-19 41 43 0\n-3 6 15 33 34 36 37 0\n-3 42 46 48 0\n-10 46 48 0\n-25 42 0\n-26 42 46 0\n-4 42 46 50 0\n-12 46 50 0\n-28 42 0\n-29 42 46 0\n-5 -6 -13 0\n-5 43 44 51 0\n-16 51 0\n-32 44 0\n-35 43 51 0\n-37 43 44 0\n-43 5 35 37 0\n-6 46 48 51 0\n-25 51 0\n-36 46 51 0\n-37 46 48 0\n-48 6 33 37 51 0\n-7 43 45 51 0\n-18 51 0\n-32 45 0\n-38 43 51 0\n-40 43 45 0\n-8 46 50 51 0\n-28 51 0\n-39 46 51 0\n-40 46 50 0\n-43 13 0\n-15 42 0\n-42 15 0\n-20 44 0\n-21 45 0\n-22 41 0\n-41 22 0\n-47 24 0\n-49 27 0\n-30 48 0\n-48 30 0\n-31 50 0\n-50 31 0\n-34 51 0\n-51 34 0\n-15 52 0\n-22 52 0\n-34 52 0\n-24 53 0\n-27 53 0\n-30 53 0\n-31 53 0\n-54 41 42 51 0\n-41 54 0\n-42 54 0\n-51 54 0\n-44 55 0\n-45 55 0\n-56 47 48 49 50 0\n-48 56 0\n-50 56 0\n-53 57 0\n-52 -57 58 0\n-59 56 0\n-55 -56 59 0\n-60 54 0\n-60 59 0\n-54 -59 60 0\n-58 -60 61 0\n-61 0\n3 4 6 8 10 12 15 23 25 26 28 29 30 31 33 34 36 37 39 40 0\n1 2 9 11 14 16 17 18 19 20 21 41 43 44 45 0\n3 4 10 12 23 25 26 28 29 30 31 42 46 48 50 0\n1 5 9 14 16 17 22 32 34 35 37 41 43 44 51 0\n3 6 10 15 23 25 26 33 34 36 37 42 46 48 51 0\n2 7 11 14 18 19 22 32 34 38 40 41 43 45 51 0\n5 7 16 18 20 21 32 35 37 38 40 43 44 45 51 0\n6 8 25 28 30 31 33 36 37 39 40 46 48 50 51 0\n"
  "120 52 -54 0 87 88 89 74 78 86 94 0\n121 -60 0 111 107 108 110 105 120 104 103 90 91 92 93 79 80 82 84 100 0\n122 55 -41 51 0 18 66 55 9 64 53 98 99 75 56 52 76 67 63 118 0\n123 42 51 -54 0 121 85 69 59 109 73 94 8 10 21 78 60 70 46 50 4 5 122 106 101 102 81 58 43 61 83 68 47 71 112 0\n124 56 46 33 51 0 70 60 69 59 101 102 81 58 61 83 68 71 119 0\n125 51 -54 0 121 109 53 85 123 11 12 13 14 15 19 22 74 35 55 2 124 106 98 56 31 52 115 0\n126 55 -51 0 28 26 41 40 35 34 24 98 99 75 32 31 76 38 37 113 0\n127 -54 0 121 109 125 25 27 29 45 49 46 50 126 106 101 102 81 43 44 83 47 48 114 0\n128 -41 0 127 95 0\n129 -42 0 127 96 0\n130 -51 0 127 97 0\n131 -16 0 128 34 0\n132 -18 0 128 40 0\n133 -22 0 128 77 0\n134 -25 0 129 45 0\n135 -15 0 129 73 0\n136 -34 0 130 85 0\n137 -43 0 130 129 136 134 135 16 17 23 72 60 46 1 3 6 7 36 57 30 51 42 62 116 0\n138 -35 0 137 130 55 0\n139 -38 0 137 130 66 0\n140 -17 0 137 128 35 0\n141 -19 0 137 128 41 0\n142 44 0 130 137 128 138 136 133 140 131 33 54 56 32 31 52 115 0\n143 -45 0 142 20 0\n144 -14 0 143 39 0\n145 -32 0 143 65 0\n146 -40 0 143 137 67 0\n147 -11 0 143 137 38 0\n148 -2 0 143 137 128 37 0\n149 -7 0 143 137 130 63 0\n150 0 149 143 147 144 132 141 148 145 133 136 146 128 137 139 130 117 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00080.record015
