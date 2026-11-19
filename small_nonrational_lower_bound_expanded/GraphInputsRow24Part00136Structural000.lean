module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00136Data
public import GraphInputsRow24Part00136Frames
public import GraphInputsRow24Part00136Leaves
public import GraphInputsRow24Part00136Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6), 69805794224242688]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 6), 71916856549572608, (certNat% 9)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), (certNat% 13), (certNat% 14), 36046389205008384, 34762159623766016]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record000_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record004
def vertexColumn : Fields := ⟨10, (certNat% 15)⟩
def kindColumn : Fields := ⟨3, (certNat% 16)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 23925373020405760, (certNat% 18), 2305845208236949504, (certNat% 19)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 26177447711997952, 12105675798371893248, (certNat% 21), (certNat% 22), 144036023238656, (certNat% 23)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 23925373020405760, (certNat% 25), (certNat% 26), (certNat% 27)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), 26177447711997952, (certNat% 29), (certNat% 30), (certNat% 31), 144036023238656, (certNat% 32)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 26177447711997952, 148434069749760, (certNat% 31), (certNat% 22), 216172782113783808]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c6 c9
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c6 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c11 c8
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record004_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "a725c8f0bc5c96a968da2e87a959564d8b69394e4b8ae8789e1783e5c569a6659366392e479d1695955558d5352d68d9354d8b52d2b61d2745d0f56394d5334d332cc7392d4b32d2b2ac6b86c9b16c3b61e4751ca785d1715e0f43c4f07d26258362382e9464949615254358348d0b54348c9314c3322c4b0ad0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6d26d269a6da6db6934924d249349249249249a493492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 72), (facetIndex 78), (facetIndex 79)]))
 (.leaf ([(facetIndex 92), (facetIndex 96), (facetIndex 97)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 56), (facetIndex 62), (facetIndex 68), (facetIndex 71)]))
 (.leaf ([(facetIndex 41), (facetIndex 73), (facetIndex 74), (facetIndex 75), (facetIndex 77), (facetIndex 81)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 83), (facetIndex 93), (facetIndex 94), (facetIndex 99), (facetIndex 100), (facetIndex 101)]))
 (.leaf ([(facetIndex 95), (facetIndex 98)])))
 (.branch 7
 (.leaf ([(facetIndex 86), (facetIndex 87), (facetIndex 90)]))
 (.leaf ([(facetIndex 91)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "24949b21f80d808180186d8402000080002000000000018002z1b;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record006" 52

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record006" "{\"ridges\":[[12,321],[12,322],[18,532],[21,592],[33,532],[35,322],[41,538],[46,321],[46,322],[52,321],[52,322],[53,592],[54,321],[54,322],[58,532],[62,332],[67,532],[68,340],[69,592],[70,532],[71,836],[74,568],[76,592],[77,664],[78,360],[79,368],[86,332],[87,582],[90,340],[91,582],[96,360],[97,368]],\"owners\":[[12,321,[62,68,71,78,79],[35,46,52,54]],[46,321,[68,71,79],[12,35,52,54,62,78]],[52,321,[62,71,78],[12,35,46,54,68,79]],[54,321,[62,68,71],[12,35,46,52,78,79]],[12,322,[86,90,96,97],[35,46,52,54]],[35,322,[96,97],[12,46,52,54,86,90]],[46,322,[90,97],[12,35,52,54,86,96]],[52,322,[86,96],[12,35,46,54,90,97]],[54,322,[86,90],[12,35,46,52,96,97]],[18,532,[83,91,99,100,101],[33,58,67,69,70]],[33,532,[99,100,101],[18,58,67,69,70,83,91]],[58,532,[91],[18,33,67,69,70,83,99,100,101]],[67,532,[83,91,100,101],[18,33,58,69,70,99]],[70,532,[83,91,99,100],[18,33,58,67,69,101]],[21,592,[91,95,100],[53,69,76]],[53,592,[100],[21,69,76,91,95]],[69,592,[95],[21,53,76,91,100]],[76,592,[91],[21,53,69,95,100]],[87,582,[36,91],[]],[91,582,[36,87],[]],[41,538,[83,95],[]],[62,332,[86],[]],[86,332,[62],[]],[68,340,[90],[]],[90,340,[68],[]],[71,836,[],[]],[74,568,[99],[]],[77,664,[101],[]],[78,360,[96],[]],[96,360,[78],[]],[79,368,[97],[]],[97,368,[79],[]]],\"edges\":[[34,[18,21,33,41,53,58,67,69,70,74,76,77,83,91,95,99,100,101]],[40,[12,35,46,52,54,62,68,71,78,79,86,90,96,97]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-28,-13],[-28,-15],[-28,-25],[-28,-27],[-1,13,15,18,22,23],[-8,15,18,23],[-9,13,18,22],[-11,13,15,18],[-1,25,27,30,31],[-5,30,31],[-8,27,31],[-9,25,30],[-11,25,27],[-2,24,28,32,33,34],[-4,32,33,34],[-12,28],[-14,24,28,33,34],[-17,24,28,32,33],[-3,28,29,33],[-10,33],[-16,29],[-20,28],[-26,6,28],[-28,6,26],[-7,24,29],[-13,25],[-25,13],[-15,27],[-27,15],[-18],[-19,32],[-21,34],[-22,30],[-30,22],[-23,31],[-31,23],[-22,35],[-23,35],[-30,36],[-31,36],[-6,37],[-13,37],[-15,37],[-24,38],[-32,38],[-33,38],[-34,38],[-29,39],[-40,25,26,27],[-25,40],[-26,40],[-27,40],[-41,28],[-28,41],[-36,42],[-35,42],[-35,-36,43],[-37,44],[-44,45],[-42,45],[-42,-44,46],[-43,46],[-39,47],[-38,47],[-48,40,41],[-41,48],[-40,48],[-40,-41,49],[-48,50],[-49,51],[-47,50],[-47,-48,51],[-45,-51,52],[-46,-50,52],[-52],[2,3,4,7,10,12,14,16,17,19,20,21,24,28,29,32,33,34],[1,5,8,9,11,13,15,18,22,23,25,27,30,31]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":91,\"b\":62},{\"tag\":\"incompatible\",\"a\":91,\"b\":68},{\"tag\":\"incompatible\",\"a\":91,\"b\":86},{\"tag\":\"incompatible\",\"a\":91,\"b\":90},{\"tag\":\"mate\",\"ridge\":321,\"a\":12,\"owners\":[62,68,71,78,79]},{\"tag\":\"mate\",\"ridge\":321,\"a\":46,\"owners\":[68,71,79]},{\"tag\":\"mate\",\"ridge\":321,\"a\":52,\"owners\":[62,71,78]},{\"tag\":\"mate\",\"ridge\":321,\"a\":54,\"owners\":[62,68,71]},{\"tag\":\"mate\",\"ridge\":322,\"a\":12,\"owners\":[86,90,96,97]},{\"tag\":\"mate\",\"ridge\":322,\"a\":35,\"owners\":[96,97]},{\"tag\":\"mate\",\"ridge\":322,\"a\":46,\"owners\":[90,97]},{\"tag\":\"mate\",\"ridge\":322,\"a\":52,\"owners\":[86,96]},{\"tag\":\"mate\",\"ridge\":322,\"a\":54,\"owners\":[86,90]},{\"tag\":\"mate\",\"ridge\":532,\"a\":18,\"owners\":[83,91,99,100,101]},{\"tag\":\"mate\",\"ridge\":532,\"a\":33,\"owners\":[99,100,101]},{\"tag\":\"mate\",\"ridge\":532,\"a\":58,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":532,\"a\":67,\"owners\":[83,91,100,101]},{\"tag\":\"mate\",\"ridge\":532,\"a\":70,\"owners\":[83,91,99,100]},{\"tag\":\"mate\",\"ridge\":592,\"a\":21,\"owners\":[91,95,100]},{\"tag\":\"mate\",\"ridge\":592,\"a\":53,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":592,\"a\":69,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":592,\"a\":76,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":582,\"a\":87,\"owners\":[36,91]},{\"tag\":\"mate\",\"ridge\":582,\"a\":91,\"owners\":[36,87]},{\"tag\":\"mate\",\"ridge\":538,\"a\":41,\"owners\":[83,95]},{\"tag\":\"mate\",\"ridge\":332,\"a\":62,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":332,\"a\":86,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":340,\"a\":68,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":340,\"a\":90,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":836,\"a\":71,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":568,\"a\":74,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":664,\"a\":77,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":360,\"a\":78,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":360,\"a\":96,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":368,\"a\":79,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":368,\"a\":97,\"owners\":[79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":78,\"full_literals\":[-22,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":79,\"full_literals\":[-23,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":96,\"full_literals\":[-30,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":97,\"full_literals\":[-31,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":36,\"full_literals\":[-6,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":62,\"full_literals\":[-13,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":68,\"full_literals\":[-15,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":83,\"full_literals\":[-24,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":99,\"full_literals\":[-32,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":100,\"full_literals\":[-33,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":101,\"full_literals\":[-34,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":95,\"full_literals\":[-29,39]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[86,87,90],\"full_literals\":[-40,25,26,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-25,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-26,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":90,\"full_literals\":[-27,40]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[91],\"full_literals\":[-41,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":91,\"full_literals\":[-28,41]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-35,-36,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,40,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-41,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-48,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-45,-51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-50,52],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[18,21,33,41,53,58,67,69,70,74,76,77,83,91,95,99,100,101]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[12,35,46,52,54,62,68,71,78,79,86,90,96,97]}]}"
  "78 1 5 8 9 11 13 15 22 23 25 27 30 31 0 30 77 0\n79 45 0 30 59 60 58 55 56 42 43 39 40 37 38 5 7 8 27 29 10 11 78 0\n80 -51 0 79 75 73 0\n81 -49 0 80 70 0\n82 -41 6 0 81 53 68 24 51 0\n83 37 -48 0 41 42 43 27 29 82 54 65 23 49 0\n84 28 47 0 64 47 32 46 20 45 31 15 44 63 48 25 21 16 19 22 14 18 17 76 0\n85 -48 46 0 80 30 72 83 58 61 55 56 39 40 37 38 10 84 1 2 3 4 8 5 7 6 78 0\n86 9 31 5 8 11 13 15 22 23 25 27 30 0 78 9 0\n87 30 31 40 0 52 11 35 28 50 26 13 10 33 12 86 0\n88 -30 43 0 34 39 37 57 0\n89 46 0 62 85 67 88 87 36 40 38 57 0\n90 -50 0 89 75 74 0\n91 -48 0 90 69 0\n92 -47 0 90 71 0\n93 -41 0 91 66 0\n94 28 0 92 84 0\n95 0 94 93 54 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "29c9723c2f172968ba59a56358b61da4e4b8ae8789e1783e5c699966392e74559695954d58d4b51d68d9362d4b4ad8749d1743d58e5354cd34ccb31ce4b4acab86c5b61e4731ca719e1725c570de0f43c4f07c9a0e9464988e0ba51864990e645515258348d0b54348c9314c3322c2b06d0721c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6da4db6d269a6924934db6924926924924d2492493492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 31), (facetIndex 37), (facetIndex 41), (facetIndex 53), (facetIndex 69), (facetIndex 87)]))
 (.leaf ([(facetIndex 40), (facetIndex 61), (facetIndex 67), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 29), (facetIndex 43), (facetIndex 54), (facetIndex 56), (facetIndex 57), (facetIndex 71), (facetIndex 72), (facetIndex 74)]))
 (.leaf ([(facetIndex 42), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 52), (facetIndex 73)]))
 (.leaf ([(facetIndex 44), (facetIndex 76), (facetIndex 78), (facetIndex 80), (facetIndex 88)])))
 (.branch 7
 (.leaf ([(facetIndex 32), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 62)]))
 (.branch 8
 (.leaf ([(facetIndex 30), (facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 38), (facetIndex 39)]))
 (.leaf ([(facetIndex 45), (facetIndex 81)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "500000085050502422100100006166622020433333085230177007776072z1d;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 63), (facetIndex 75)]))
 (.leaf ([(facetIndex 83), (facetIndex 90)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 46), (facetIndex 55)]))
 (.leaf ([(facetIndex 77), (facetIndex 79), (facetIndex 82)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 86), (facetIndex 89), (facetIndex 93)]))
 (.leaf ([(facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 68)])))
 (.branch 7
 (.leaf ([(facetIndex 84), (facetIndex 85), (facetIndex 92), (facetIndex 94)]))
 (.leaf ([(facetIndex 91)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a6e601362c061800000516d000000400000080000002z1b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
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
def grouped3_0019 : List Nat := [0, 1, 2, 3]
def grouped3_0021 : List Nat := [1]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [2, 3]
def grouped3_0024 : List Nat := [3]
def grouped3_0025 : List Nat := [4]
def grouped3_0026 : List Nat := [4, 5]
def grouped3_0027 : List Nat := [4, 5, 6, 7]
def grouped3_0028 : List Nat := [5]
def grouped3_0029 : List Nat := [6]
def grouped3_0030 : List Nat := [6, 7]
def grouped3_0031 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record007" 107

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record007" "{\"ridges\":[[8,50],[9,81],[15,524],[18,580],[19,49],[19,56],[21,536],[22,592],[26,70],[27,26],[27,42],[32,524],[34,82],[39,70],[40,580],[42,82],[43,536],[44,42],[45,42],[47,50],[47,81],[48,50],[49,50],[50,81],[51,81],[52,82],[52,592],[57,536],[60,524],[61,524],[61,580],[62,524],[64,180],[65,564],[66,212],[67,580],[67,592],[68,660],[70,577],[70,580],[71,56],[72,49],[72,56],[72,536],[73,536],[73,592],[74,536],[77,92],[78,26],[80,42],[81,42],[81,262],[85,212],[86,70],[86,534],[89,26],[89,586],[93,92]],\"owners\":[[81,262,[4,26,41],[25,31]],[19,49,[8,33,47,48,49,63,64,65,75],[54,71,72]],[72,49,[8,33,47,48,49,63,64,75],[19,54,65,71]],[8,50,[27,76,83,84,88,90],[33,47,48,49]],[47,50,[27,76,84,88],[8,33,48,49,83,90]],[48,50,[27,76,83,90],[8,33,47,49,84,88]],[49,50,[27,76,83,84,88],[8,33,47,48,90]],[9,81,[22,55,63,66,67,73,75],[34,42,47,50,51]],[47,81,[22,55,66,67,73],[9,34,42,50,51,63,75]],[50,81,[22,55,63,67,73,75],[9,34,42,47,51,66]],[51,81,[22,55,63,66,67,73],[9,34,42,47,50,75]],[34,82,[89,90],[9,42,47,50,51,52,77,83,85,86]],[42,82,[83,85,86,90],[9,34,47,50,51,52,77,89]],[52,82,[77,83,85,90],[9,34,42,47,50,51,86,89]],[15,524,[79,82,92,93,94],[32,57,60,61,62]],[32,524,[92,93,94],[15,57,60,61,62,79,82]],[60,524,[79,82,93,94],[15,32,57,61,62,92]],[61,524,[79,92,94],[15,32,57,60,62,82,93]],[62,524,[79,82,92,93],[15,32,57,60,61,94]],[70,577,[22,46,52,73],[18,40,61]],[18,580,[82,86,93],[40,61,67,70]],[40,580,[93],[18,61,67,70,82,86]],[61,580,[86],[18,40,67,70,82,93]],[67,580,[82],[18,40,61,70,86,93]],[70,580,[82,86,93],[18,40,61,67]],[19,56,[27,76,88,91,92],[54,71,72]],[71,56,[27,76,92],[19,54,72,88,91]],[72,56,[27,76,88,91],[19,54,71,92]],[21,536,[79,89,92,93,94],[43,57,72,73,74]],[43,536,[92,93,94],[21,57,72,73,74,79,89]],[57,536,[89],[21,43,72,73,74,79,92,93,94]],[72,536,[79,89,93,94],[21,43,57,73,74,92]],[73,536,[79,92,94],[21,43,57,72,74,89,93]],[74,536,[79,89,92,93],[21,43,57,72,73,94]],[22,592,[86,89,93],[52,67,73]],[52,592,[93],[22,67,73,86,89]],[67,592,[89],[22,52,73,86,93]],[73,592,[86],[22,52,67,89,93]],[86,534,[36,79],[]],[89,586,[46,82],[]],[77,92,[55,93],[]],[93,92,[55,77],[]],[64,180,[84,91],[]],[65,564,[92],[]],[66,212,[85],[]],[85,212,[66],[]],[68,660,[94],[]]],\"edges\":[[29,[15,21,32,43,46,57,60,61,62,72,73,74,79,82,89,92,93,94]],[30,[8,19,27,33,47,48,49,54,63,64,65,71,72,75,76,83,84,88,90,91,92]],[31,[9,22,34,42,47,50,51,52,55,63,66,67,73,75,77,83,85,86,89,90,93]],[41,[18,22,40,46,52,61,67,70,73,82,86,89,93]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-19,-1],[-19,-17],[-21,-19],[-24,-12],[-24,-14],[-24,-18],[-25,-2],[-25,-14],[-25,-24],[-27,-25],[-28,-24],[-29,-18],[-29,-24],[-29,-25],[-32,-20],[-32,-27],[-32,-28],[-32,-30],[-32,-31],[-33,-24],[-33,-25],[-34,-20],[-46,-19],[-46,-34],[-47,-24],[-49,-36],[-49,-47],[-49,-48],[-50,-49],[-52,-25],[-54,-14],[-54,-33],[-56,-12],[-56,-18],[-56,-28],[-56,-47],[-56,-55],[-57,-52],[-57,-56],[-62,-11],[-62,-14],[-62,-16],[-62,-26],[-62,-33],[-62,-35],[-62,-52],[-62,-54],[-62,-58],[-63,-18],[-63,-53],[-63,-55],[-64,-63],[-68,-12],[-68,-14],[-68,-15],[-68,-16],[-68,-22],[-68,-38],[-68,-44],[-68,-49],[-68,-54],[-9,-19,-62],[-57,1,9,21],[-10,-54,-64],[-10,-24,-57],[-10,-25,-56],[-6,2,14,27,28,29,40,41,42,51],[-48,2,14,27,28,29,40,41,51],[-2,10,52,59,60,63,65],[-27,10,52,60,63],[-28,10,52,59,65],[-29,10,52,59,60,63],[-3,8,34,40,43,44,49,51],[-27,8,34,43,44,49],[-30,8,34,40,44,49,51],[-31,8,34,40,43,44,49],[-15,64,65],[-22,59,61,62,65],[-32,53,59,61,65],[-4,55,58,67,68,69],[-13,67,68,69],[-37,55,58,68,69],[-38,55,67,69],[-39,55,58,67,68],[-46,8,26,32,49],[-5,58,62,68],[-20,68],[-38,62],[-44,58],[-46,58,62,68],[-6,10,52,63,66,67],[-47,10,52,67],[-48,10,52,63,66],[-7,55,64,67,68,69],[-23,67,68,69],[-36,64],[-48,55,64,68,69],[-49,55,67,69],[-50,55,64,67,68],[-8,62,64,68],[-32,68],[-44,64],[-49,62],[-62,17,55],[-64,26,58],[-53,34,68],[-68,34,53],[-41,60,66],[-42,67],[-43,61],[-61,43],[-45,69],[-70,20,38,44,46],[-71,11,23,33,35,36,47,48,50],[-72,22,27,28,29,30,31],[-73,32,49],[-49,73],[-74,24,52,54,56,63],[-75,12,14,15,16,18,19],[-76,25,57],[-77,70],[-78,71],[-78,72],[-79,77],[-79,78],[-80,73,74],[-81,73],[-81,74],[-82,75,76],[-83,75],[-83,76],[-84,82],[-85,83],[-86,80],[-86,81,85],[-87,81],[-86,84],[-87,85],[-88,79,87],[-88,86],[88],[-40,89],[-51,89],[-59,90],[-65,90],[-17,91],[-26,91],[-34,91],[-53,92],[-55,92],[-58,92],[-93,62,64,68],[-62,93],[-64,93],[-68,93],[-94,41,42,43,45],[-43,94],[-60,95],[-61,95],[-67,95],[-69,95],[-66,96],[-90,97],[-89,97],[-92,98],[-91,98],[-91,-92,99],[-98,100],[-97,-98,101],[-97,-99,102],[-103,93,94],[-94,103],[-93,103],[-96,104],[-95,104],[-103,105],[-103,-104,106],[-100,-106,107],[-101,-105,107],[-102,107],[-107],[4,7,13,23,26,36,37,38,39,48,49,50,55,58,64,67,68,69],[2,6,10,14,27,28,29,33,40,41,42,47,48,51,52,59,60,63,65,66,67],[3,8,15,22,27,30,31,32,34,40,43,44,49,51,53,59,61,62,64,65,68],[5,8,20,26,32,38,44,46,49,58,62,64,68]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":39,\"b\":4},{\"tag\":\"incompatible\",\"a\":39,\"b\":36},{\"tag\":\"incompatible\",\"a\":41,\"b\":39},{\"tag\":\"incompatible\",\"a\":44,\"b\":30},{\"tag\":\"incompatible\",\"a\":44,\"b\":33},{\"tag\":\"incompatible\",\"a\":44,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":8},{\"tag\":\"incompatible\",\"a\":45,\"b\":33},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":45},{\"tag\":\"incompatible\",\"a\":48,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":38},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":52,\"b\":40},{\"tag\":\"incompatible\",\"a\":52,\"b\":47},{\"tag\":\"incompatible\",\"a\":52,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":44},{\"tag\":\"incompatible\",\"a\":54,\"b\":45},{\"tag\":\"incompatible\",\"a\":55,\"b\":40},{\"tag\":\"incompatible\",\"a\":70,\"b\":39},{\"tag\":\"incompatible\",\"a\":70,\"b\":55},{\"tag\":\"incompatible\",\"a\":71,\"b\":44},{\"tag\":\"incompatible\",\"a\":73,\"b\":57},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":76,\"b\":45},{\"tag\":\"incompatible\",\"a\":78,\"b\":33},{\"tag\":\"incompatible\",\"a\":78,\"b\":54},{\"tag\":\"incompatible\",\"a\":80,\"b\":30},{\"tag\":\"incompatible\",\"a\":80,\"b\":38},{\"tag\":\"incompatible\",\"a\":80,\"b\":48},{\"tag\":\"incompatible\",\"a\":80,\"b\":71},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"incompatible\",\"a\":81,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":86,\"b\":29},{\"tag\":\"incompatible\",\"a\":86,\"b\":33},{\"tag\":\"incompatible\",\"a\":86,\"b\":35},{\"tag\":\"incompatible\",\"a\":86,\"b\":46},{\"tag\":\"incompatible\",\"a\":86,\"b\":54},{\"tag\":\"incompatible\",\"a\":86,\"b\":56},{\"tag\":\"incompatible\",\"a\":86,\"b\":76},{\"tag\":\"incompatible\",\"a\":86,\"b\":78},{\"tag\":\"incompatible\",\"a\":86,\"b\":82},{\"tag\":\"incompatible\",\"a\":88,\"b\":38},{\"tag\":\"incompatible\",\"a\":88,\"b\":77},{\"tag\":\"incompatible\",\"a\":88,\"b\":79},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":93,\"b\":30},{\"tag\":\"incompatible\",\"a\":93,\"b\":33},{\"tag\":\"incompatible\",\"a\":93,\"b\":34},{\"tag\":\"incompatible\",\"a\":93,\"b\":35},{\"tag\":\"incompatible\",\"a\":93,\"b\":42},{\"tag\":\"incompatible\",\"a\":93,\"b\":61},{\"tag\":\"incompatible\",\"a\":93,\"b\":67},{\"tag\":\"incompatible\",\"a\":93,\"b\":73},{\"tag\":\"incompatible\",\"a\":93,\"b\":78},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[26,39,86]},{\"tag\":\"mate\",\"ridge\":262,\"a\":81,\"owners\":[4,26,41]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[27,78,89]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[27,44,81]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[27,45,80]},{\"tag\":\"mate\",\"ridge\":49,\"a\":19,\"owners\":[8,33,47,48,49,63,64,65,75]},{\"tag\":\"mate\",\"ridge\":49,\"a\":72,\"owners\":[8,33,47,48,49,63,64,75]},{\"tag\":\"mate\",\"ridge\":50,\"a\":8,\"owners\":[27,76,83,84,88,90]},{\"tag\":\"mate\",\"ridge\":50,\"a\":47,\"owners\":[27,76,84,88]},{\"tag\":\"mate\",\"ridge\":50,\"a\":48,\"owners\":[27,76,83,90]},{\"tag\":\"mate\",\"ridge\":50,\"a\":49,\"owners\":[27,76,83,84,88]},{\"tag\":\"mate\",\"ridge\":81,\"a\":9,\"owners\":[22,55,63,66,67,73,75]},{\"tag\":\"mate\",\"ridge\":81,\"a\":47,\"owners\":[22,55,66,67,73]},{\"tag\":\"mate\",\"ridge\":81,\"a\":50,\"owners\":[22,55,63,67,73,75]},{\"tag\":\"mate\",\"ridge\":81,\"a\":51,\"owners\":[22,55,63,66,67,73]},{\"tag\":\"mate\",\"ridge\":82,\"a\":34,\"owners\":[89,90]},{\"tag\":\"mate\",\"ridge\":82,\"a\":42,\"owners\":[83,85,86,90]},{\"tag\":\"mate\",\"ridge\":82,\"a\":52,\"owners\":[77,83,85,90]},{\"tag\":\"mate\",\"ridge\":524,\"a\":15,\"owners\":[79,82,92,93,94]},{\"tag\":\"mate\",\"ridge\":524,\"a\":32,\"owners\":[92,93,94]},{\"tag\":\"mate\",\"ridge\":524,\"a\":60,\"owners\":[79,82,93,94]},{\"tag\":\"mate\",\"ridge\":524,\"a\":61,\"owners\":[79,92,94]},{\"tag\":\"mate\",\"ridge\":524,\"a\":62,\"owners\":[79,82,92,93]},{\"tag\":\"mate\",\"ridge\":577,\"a\":70,\"owners\":[22,46,52,73]},{\"tag\":\"mate\",\"ridge\":580,\"a\":18,\"owners\":[82,86,93]},{\"tag\":\"mate\",\"ridge\":580,\"a\":40,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":580,\"a\":61,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":580,\"a\":67,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":580,\"a\":70,\"owners\":[82,86,93]},{\"tag\":\"mate\",\"ridge\":56,\"a\":19,\"owners\":[27,76,88,91,92]},{\"tag\":\"mate\",\"ridge\":56,\"a\":71,\"owners\":[27,76,92]},{\"tag\":\"mate\",\"ridge\":56,\"a\":72,\"owners\":[27,76,88,91]},{\"tag\":\"mate\",\"ridge\":536,\"a\":21,\"owners\":[79,89,92,93,94]},{\"tag\":\"mate\",\"ridge\":536,\"a\":43,\"owners\":[92,93,94]},{\"tag\":\"mate\",\"ridge\":536,\"a\":57,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":536,\"a\":72,\"owners\":[79,89,93,94]},{\"tag\":\"mate\",\"ridge\":536,\"a\":73,\"owners\":[79,92,94]},{\"tag\":\"mate\",\"ridge\":536,\"a\":74,\"owners\":[79,89,92,93]},{\"tag\":\"mate\",\"ridge\":592,\"a\":22,\"owners\":[86,89,93]},{\"tag\":\"mate\",\"ridge\":592,\"a\":52,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":592,\"a\":67,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":592,\"a\":73,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":534,\"a\":86,\"owners\":[36,79]},{\"tag\":\"mate\",\"ridge\":586,\"a\":89,\"owners\":[46,82]},{\"tag\":\"mate\",\"ridge\":92,\"a\":77,\"owners\":[55,93]},{\"tag\":\"mate\",\"ridge\":92,\"a\":93,\"owners\":[55,77]},{\"tag\":\"mate\",\"ridge\":180,\"a\":64,\"owners\":[84,91]},{\"tag\":\"mate\",\"ridge\":564,\"a\":65,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":212,\"a\":66,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":212,\"a\":85,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":660,\"a\":68,\"owners\":[94]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[40,61,67,70],\"full_literals\":[-70,20,38,44,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[29,43,54,56,57,71,72,74],\"full_literals\":[-71,11,23,33,35,36,47,48,50]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[42,47,48,49,50,51],\"full_literals\":[-72,22,27,28,29,30,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[52,73],\"full_literals\":[-73,32,49]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":73,\"full_literals\":[-49,73]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[44,76,78,80,88],\"full_literals\":[-74,24,52,54,56,63]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[30,33,34,35,38,39],\"full_literals\":[-75,12,14,15,16,18,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[45,81],\"full_literals\":[-76,25,57]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-78,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-79,77,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-79,false,78],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,73,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-81,73,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-81,false,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-82,75,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-83,75,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-83,false,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-84,false,82],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-85,false,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-86,80,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-86,81,85],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-87,81,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,false,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-87,false,85],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-88,79,87],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-88,false,86],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-40,89]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":75,\"full_literals\":[-51,89]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-59,90]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":90,\"full_literals\":[-65,90]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":36,\"full_literals\":[-17,91]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":46,\"full_literals\":[-26,91]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":55,\"full_literals\":[-34,91]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":77,\"full_literals\":[-53,92]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":79,\"full_literals\":[-55,92]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-58,92]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[86,89,93],\"full_literals\":[-93,62,64,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":86,\"full_literals\":[-62,93]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":89,\"full_literals\":[-64,93]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":93,\"full_literals\":[-68,93]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[64,65,66,68],\"full_literals\":[-94,41,42,43,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":66,\"full_literals\":[-43,94]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-60,95]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":85,\"full_literals\":[-61,95]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":92,\"full_literals\":[-67,95]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":94,\"full_literals\":[-69,95]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":91,\"full_literals\":[-66,96]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-90,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-89,false,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-92,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-91,false,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-91,-92,99],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-98,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-97,-98,101],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-97,-99,102],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-103,93,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-94,103],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-93,false,103],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-96,104],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-95,false,104],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-103,false,105],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-103,-104,106],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-100,-106,107],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-101,-105,107],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-102,false,107],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[15,21,32,43,46,57,60,61,62,72,73,74,79,82,89,92,93,94]},{\"tag\":\"edge\",\"edge\":30,\"owners\":[8,19,27,33,47,48,49,54,63,64,65,71,72,75,76,83,84,88,90,91,92]},{\"tag\":\"edge\",\"edge\":31,\"owners\":[9,22,34,42,47,50,51,52,55,63,66,67,73,75,77,83,85,86,89,90,93]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[18,22,40,46,52,61,67,70,73,82,86,89,93]}]}"
  "186 86 0 141 140 0\n187 80 0 186 134 0\n188 84 0 186 137 0\n189 82 0 188 132 0\n190 -102 0 181 180 0\n191 98 0 165 166 149 150 151 146 147 148 107 104 86 89 90 105 87 101 88 100 103 185 0\n192 100 0 191 168 0\n193 -106 0 192 181 178 0\n194 103 97 0 141 164 143 142 163 145 144 172 173 157 153 154 155 111 88 100 103 77 102 87 101 78 116 127 136 139 124 121 113 24 106 73 76 75 74 184 0\n195 -18 -62 -74 0 47 46 6 34 49 118 0\n196 -24 18 -62 15 -83 0 42 41 131 130 4 9 119 120 1 3 62 63 0\n197 -56 18 -62 15 -75 0 42 41 33 37 119 104 2 0\n198 64 68 73 -83 97 0 187 193 194 177 175 161 160 95 81 126 117 130 112 159 110 109 158 174 162 108 156 171 163 145 77 96 152 43 46 47 48 195 196 197 118 51 84 99 80 94 82 97 83 182 0\n199 -52 -76 0 30 38 120 0\n200 -24 63 -76 97 0 193 199 194 177 175 160 109 158 174 162 108 164 143 142 163 145 144 5 9 11 13 20 25 120 65 69 70 91 93 183 0\n201 -54 63 52 97 0 193 194 177 175 161 112 159 110 160 109 158 174 162 108 156 171 164 143 142 163 145 144 31 32 47 61 152 64 69 70 71 72 91 92 93 183 0\n202 63 -74 -76 97 0 193 199 194 177 175 160 109 158 174 162 108 164 143 142 163 145 144 200 201 118 35 36 39 120 7 8 10 14 21 66 67 68 183 0\n203 73 -83 -70 97 0 193 187 131 194 177 175 161 160 126 202 50 51 52 83 102 198 107 22 24 113 0\n204 -68 -73 -75 -79 0 125 123 124 121 53 54 55 56 57 58 59 60 116 15 16 17 18 19 113 115 23 12 119 0\n205 -83 -79 97 0 193 125 122 124 121 194 177 175 161 160 130 203 204 101 95 116 26 27 28 29 103 40 44 45 114 0\n206 68 -73 -71 95 0 161 160 101 95 116 26 27 28 29 103 40 44 45 114 0\n207 -79 97 0 193 186 189 194 177 175 159 163 145 144 125 122 205 133 135 127 128 206 60 204 116 129 79 202 50 0\n208 97 0 193 141 163 144 145 194 177 175 159 160 161 207 139 136 138 127 128 133 131 202 50 51 79 98 116 0\n209 101 0 208 191 169 0\n210 -99 0 208 190 170 0\n211 -105 0 209 181 179 0\n212 -103 0 211 176 0\n213 -93 0 212 173 0\n214 -62 0 213 153 0\n215 -64 0 213 154 0\n216 -68 0 213 155 0\n217 -38 0 214 88 0\n218 -49 0 214 103 0\n219 -8 0 214 215 216 100 0\n220 -44 0 215 102 0\n221 -20 0 216 87 0\n222 -32 0 216 101 0\n223 -73 0 222 218 116 0\n224 -81 0 223 127 0\n225 -87 0 224 136 0\n226 79 0 225 141 139 0\n227 77 0 226 124 0\n228 70 0 227 121 0\n229 46 0 228 220 217 221 113 0\n230 26 0 229 219 222 218 85 0\n231 58 0 229 214 216 90 0\n232 91 0 230 147 0\n233 92 0 231 151 0\n234 0 232 233 210 167 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "d534c9b16cc70bc9aa9a2ea66959562da4e53a2e2b86e4789e0f969664b959655554b59354d4b4ad1b61d2743d38e5354cb392d4b1ae1b46c3b91d4729e1745c9715c3783d0f23c4f8711c2aa1a26a4619a168382e078a946499514654550d0b41d28c6324c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db4da49369a4924d24d36924924da6d2492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 60)]))
 (.branch 2
 (.leaf ([(facetIndex 75)]))
 (.leaf ([(facetIndex 82)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 87)]))
 (.leaf ([(facetIndex 62), (facetIndex 76)])))
 (.branch 6
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 66), (facetIndex 81), (facetIndex 86)]))
 (.leaf ([(facetIndex 59), (facetIndex 73), (facetIndex 84), (facetIndex 85)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "7760a8004230000140100c000000d8b4z22;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [3]
def grouped3_0003 : List Nat := [3, 4]
def grouped3_0004 : List Nat := [3, 4, 5, 6]
def grouped3_0005 : List Nat := [4]
def grouped3_0006 : List Nat := [5]
def grouped3_0007 : List Nat := [5, 6]
def grouped3_0008 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0003\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record008" 39

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record008" "{\"ridges\":[[8,67],[14,97],[15,321],[15,324],[23,70],[24,70],[24,578],[40,321],[41,578],[46,330],[47,67],[47,578],[49,67],[49,338],[51,67],[58,324],[59,585],[61,321],[63,97],[63,321],[63,324],[66,360],[73,330],[74,578],[74,580],[76,70],[76,338],[77,578],[78,578],[81,616],[84,360],[85,616],[86,840],[87,848]],\"owners\":[[14,97,[8,45,51,66],[55,63]],[63,97,[8,45,51],[14,55,66]],[15,321,[46,49,66],[40,58,61,63]],[40,321,[66],[15,46,49,58,61,63]],[61,321,[46,66],[15,40,49,58,63]],[63,321,[46,49],[15,40,58,61,66]],[15,324,[73,76,84,86,87],[40,58,61,63]],[58,324,[76,87],[15,40,61,63,73,84,86]],[63,324,[73,76,86,87],[15,40,58,61,84]],[24,578,[47,50,81],[41,74,77,78]],[41,578,[81],[24,47,50,74,77,78]],[47,578,[24,77,78],[41,50,74,81]],[74,578,[50],[24,41,47,77,78,81]],[77,578,[47,81],[24,41,50,74,78]],[78,578,[47,50],[24,41,74,77,81]],[74,580,[62,87],[24,41,59,77,78,85,86]],[46,330,[73],[]],[73,330,[46],[]],[59,585,[47],[]],[49,338,[76],[]],[76,338,[49],[]],[66,360,[84],[]],[84,360,[66],[]],[81,616,[85],[]],[85,616,[81],[]],[86,840,[],[]],[87,848,[],[]]],\"edges\":[[35,[8,14,23,45,51,55,63,66,70,78,81,84,85]],[40,[15,40,46,49,58,61,63,66,73,76,84,86,87]],[41,[24,41,47,50,59,62,74,77,78,81,85,86,87]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-8],[-10,-9],[-14,-10],[-20,-10],[-21,-10],[-22,-10],[-24,-12],[-24,-18],[-25,-24],[-26,-24],[-27,-9],[-27,-20],[-27,-22],[-28,-27],[-1,-10,-11],[-10,-11,-13],[-4,-5,-24],[-2,1,8,13,20],[-19,1,8,13],[-3,9,11,20],[-6,20],[-17,9,20],[-19,9,11],[-3,22,24,28,30,31],[-15,24,31],[-19,22,24,30,31],[-5,10,12,27],[-7,27],[-10,5,25,26],[-23,12],[-25,10,27],[-26,10,12],[-23,18,31],[-9,22],[-22,9],[-16,10],[-11,24],[-24,11],[-20,28],[-28,20],[-27,29],[-29,27],[-30],[-31],[-11,32],[-12,32],[-18,33],[-24,33],[-9,34],[-20,34],[-27,34],[-22,35],[-28,35],[-29,35],[-33,36],[-32,36],[-34,-35,37],[-36,-37,38],[-38,39],[-39],[1,2,4,8,13,14,19,20,21,26,27,28,29],[3,6,9,11,15,17,19,20,22,24,28,30,31],[5,7,10,12,16,18,23,25,26,27,29,30,31]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":47,\"b\":45},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":55,\"b\":47},{\"tag\":\"incompatible\",\"a\":66,\"b\":47},{\"tag\":\"incompatible\",\"a\":70,\"b\":47},{\"tag\":\"incompatible\",\"a\":73,\"b\":47},{\"tag\":\"incompatible\",\"a\":76,\"b\":50},{\"tag\":\"incompatible\",\"a\":76,\"b\":62},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":78,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":46},{\"tag\":\"incompatible\",\"a\":81,\"b\":66},{\"tag\":\"incompatible\",\"a\":81,\"b\":73},{\"tag\":\"incompatible\",\"a\":84,\"b\":81},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[8,47,49]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[47,49,51]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[23,24,76]},{\"tag\":\"mate\",\"ridge\":97,\"a\":14,\"owners\":[8,45,51,66]},{\"tag\":\"mate\",\"ridge\":97,\"a\":63,\"owners\":[8,45,51]},{\"tag\":\"mate\",\"ridge\":321,\"a\":15,\"owners\":[46,49,66]},{\"tag\":\"mate\",\"ridge\":321,\"a\":40,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":321,\"a\":61,\"owners\":[46,66]},{\"tag\":\"mate\",\"ridge\":321,\"a\":63,\"owners\":[46,49]},{\"tag\":\"mate\",\"ridge\":324,\"a\":15,\"owners\":[73,76,84,86,87]},{\"tag\":\"mate\",\"ridge\":324,\"a\":58,\"owners\":[76,87]},{\"tag\":\"mate\",\"ridge\":324,\"a\":63,\"owners\":[73,76,86,87]},{\"tag\":\"mate\",\"ridge\":578,\"a\":24,\"owners\":[47,50,81]},{\"tag\":\"mate\",\"ridge\":578,\"a\":41,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":578,\"a\":47,\"owners\":[24,77,78]},{\"tag\":\"mate\",\"ridge\":578,\"a\":74,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":578,\"a\":77,\"owners\":[47,81]},{\"tag\":\"mate\",\"ridge\":578,\"a\":78,\"owners\":[47,50]},{\"tag\":\"mate\",\"ridge\":580,\"a\":74,\"owners\":[62,87]},{\"tag\":\"mate\",\"ridge\":330,\"a\":46,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":330,\"a\":73,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":585,\"a\":59,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":338,\"a\":49,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":338,\"a\":76,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":360,\"a\":66,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":360,\"a\":84,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":616,\"a\":81,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":616,\"a\":85,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":840,\"a\":86,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":848,\"a\":87,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":49,\"full_literals\":[-11,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":50,\"full_literals\":[-12,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":62,\"full_literals\":[-18,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-24,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":46,\"full_literals\":[-9,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":66,\"full_literals\":[-20,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-27,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":73,\"full_literals\":[-22,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-28,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":85,\"full_literals\":[-29,35]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0003\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-34,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-36,-37,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":35,\"owners\":[8,14,23,45,51,55,63,66,70,78,81,84,85]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[15,40,46,49,58,61,63,66,73,76,84,86,87]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[24,41,47,50,59,62,74,77,78,81,85,86,87]}]}"
  "64 -38 0 60 59 0\n65 3 6 9 11 15 17 19 20 22 24 28 0 43 44 62 0\n66 5 7 10 12 16 18 23 25 26 27 29 0 43 44 63 0\n67 10 27 36 0 44 42 28 55 47 33 56 46 36 32 27 31 66 0\n68 20 -10 36 0 44 56 45 2 23 6 55 48 25 21 40 20 22 65 0\n69 -10 36 0 68 4 0\n70 36 0 44 55 56 48 45 25 69 67 11 12 13 14 23 20 22 21 65 0\n71 -37 0 70 64 58 0\n72 -27 0 71 41 51 54 57 0\n73 -7 0 72 28 0\n74 -29 0 72 42 0\n75 24 9 20 0 44 43 22 35 40 21 25 37 26 24 65 0\n76 -24 10 0 74 72 73 31 36 7 8 10 30 27 66 0\n77 -9 0 71 34 49 52 57 0\n78 -20 0 71 39 50 53 57 0\n79 -28 0 78 40 0\n80 24 0 78 77 75 0\n81 -25 0 80 9 0\n82 -26 0 80 10 0\n83 11 0 80 38 0\n84 10 0 80 76 0\n85 5 0 81 84 82 29 0\n86 -8 0 84 1 0\n87 -14 0 84 3 0\n88 -21 0 84 5 0\n89 -1 0 84 83 15 0\n90 -13 0 84 83 16 0\n91 -4 0 85 80 17 0\n92 -19 0 89 86 90 19 0\n93 -2 0 89 86 90 78 18 0\n94 0 90 89 82 93 91 87 86 92 88 78 72 79 74 61 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record008
