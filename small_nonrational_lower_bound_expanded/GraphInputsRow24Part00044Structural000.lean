module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00044Data
public import GraphInputsRow24Part00044Frames
public import GraphInputsRow24Part00044Leaves
public import GraphInputsRow24Part00044Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 291959919593127936, 860187528827764736, 42803644071936]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record002_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record005
def vertexColumn : Fields := ⟨10, (certNat% 6)⟩
def kindColumn : Fields := ⟨3, (certNat% 7)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 10), 6756498952683520, 1035828154813382656, 1261853145227591680, 1396386746597376]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record005_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3c2aaa9a2e9a6658b69394e1b85ef06a9a64b9695952d64d5346d17783d0ec370ea368e9364e8b52e2b2ac6b86c9b16d8791d2729c6745c9715e0f43c3c2ca4a0e9460d84e0b81e2c6490e5450d44d0b41da0d8390d4328c930ce0b12c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36d369249b69b492492492492492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 63), (facetIndex 66)]))
 (.leaf ([(facetIndex 74), (facetIndex 77)])))
 (.branch 3
 (.leaf ([(facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62)]))
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 72), (facetIndex 73)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58)]))
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 37), (facetIndex 38), (facetIndex 40), (facetIndex 41)])))
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 50)]))
 (.branch 8
 (.leaf ([(facetIndex 36), (facetIndex 39), (facetIndex 42), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 49)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "100133330000000222244447777686666667557557555z21;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 69)]))
 (.branch 2
 (.leaf ([(facetIndex 80)]))
 (.leaf ([(facetIndex 64), (facetIndex 65)]))))
 (.branch 4
 (.leaf ([(facetIndex 67), (facetIndex 68)]))
 (.branch 5
 (.leaf ([(facetIndex 75), (facetIndex 76)]))
 (.leaf ([(facetIndex 78), (facetIndex 79)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b44800003612z30;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
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
def grouped3_0012 : List Nat := [0, 1, 2]
def grouped3_0014 : List Nat := [1]
def grouped3_0015 : List Nat := [1, 2]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [3]
def grouped3_0018 : List Nat := [3, 4, 5]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record001" 50

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record001" "{\"ridges\":[[4,261],[14,385],[15,641],[20,321],[28,322],[37,261],[40,261],[42,385],[49,321],[49,322],[50,641],[51,385],[52,641],[53,385],[54,641],[55,385],[56,641],[58,385],[58,641],[67,664],[68,680],[69,321],[69,960],[75,404],[76,420],[78,664],[79,680],[80,322],[80,960]],\"owners\":[[4,261,[20,61,64,65],[33,37,40,42]],[37,261,[20,61,65],[4,33,40,42,64]],[40,261,[20,61,64],[4,33,37,42,65]],[14,385,[64,65,69],[42,51,53,55,58]],[42,385,[69],[14,51,53,55,58,64,65]],[51,385,[65,69],[14,42,53,55,58,64]],[53,385,[64,69],[14,42,51,55,58,65]],[55,385,[64,65],[14,42,51,53,58,69]],[58,385,[64,65],[14,42,51,53,55,69]],[15,641,[67,68,69],[50,52,54,56,58]],[50,641,[69],[15,52,54,56,58,67,68]],[52,641,[68,69],[15,50,54,56,58,67]],[54,641,[67,69],[15,50,52,56,58,68]],[56,641,[67,68],[15,50,52,54,58,69]],[58,641,[67,68],[15,50,52,54,56,69]],[75,404,[64],[]],[76,420,[65],[]],[67,664,[78],[]],[78,664,[67],[]],[68,680,[79],[]],[79,680,[68],[]],[69,960,[80],[]],[80,960,[69],[]]],\"edges\":[[22,[4,20,28,33,37,40,42,61,64,65,72,75,76]],[42,[14,42,51,53,55,58,64,65,69,75,76,80]],[43,[15,50,52,54,56,58,67,68,69,78,79,80]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-6],[-10,-9],[-20,-10],[-25,-16],[-25,-18],[-26,-10],[-1,4,20,21,22],[-7,4,20,22],[-8,4,20,21],[-4,-10,-25],[-5,-10,-31],[-2,21,22,25],[-9,25],[-12,22,25],[-14,21,25],[-16,21,22],[-19,21,22],[-3,23,24,25],[-11,25],[-13,24,25],[-15,23,25],[-17,23,24],[-19,23,24],[-27,21],[-28,22],[-23,29],[-29,23],[-24,30],[-30,24],[-25,31],[-31,25],[-32,16,17,18,19],[-33,10],[-34,32],[-35,33],[-36,35],[-37,34,36],[-38,37],[38],[-25,39],[-31,40],[-21,41],[-22,41],[-42,23,24],[-23,42],[-24,42],[-29,43],[-30,43],[-41,44],[-40,44],[-40,-41,45],[-44,46],[-39,46],[-39,-45,47],[-43,48],[-42,-48,49],[-46,-49,50],[-47,50],[-50],[1,4,5,6,7,8,9,20,21,22,26,27,28],[2,9,12,14,16,19,21,22,25,27,28,31],[3,11,13,15,17,19,23,24,25,29,30,31]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":49,\"b\":33},{\"tag\":\"incompatible\",\"a\":49,\"b\":42},{\"tag\":\"incompatible\",\"a\":61,\"b\":49},{\"tag\":\"incompatible\",\"a\":69,\"b\":55},{\"tag\":\"incompatible\",\"a\":69,\"b\":57},{\"tag\":\"incompatible\",\"a\":72,\"b\":49},{\"tag\":\"mate\",\"ridge\":261,\"a\":4,\"owners\":[20,61,64,65]},{\"tag\":\"mate\",\"ridge\":261,\"a\":37,\"owners\":[20,61,65]},{\"tag\":\"mate\",\"ridge\":261,\"a\":40,\"owners\":[20,61,64]},{\"tag\":\"three\",\"ridge\":321,\"vertices\":[20,49,69]},{\"tag\":\"three\",\"ridge\":322,\"vertices\":[28,49,80]},{\"tag\":\"mate\",\"ridge\":385,\"a\":14,\"owners\":[64,65,69]},{\"tag\":\"mate\",\"ridge\":385,\"a\":42,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":385,\"a\":51,\"owners\":[65,69]},{\"tag\":\"mate\",\"ridge\":385,\"a\":53,\"owners\":[64,69]},{\"tag\":\"mate\",\"ridge\":385,\"a\":55,\"owners\":[64,65]},{\"tag\":\"mate\",\"ridge\":385,\"a\":58,\"owners\":[64,65]},{\"tag\":\"mate\",\"ridge\":641,\"a\":15,\"owners\":[67,68,69]},{\"tag\":\"mate\",\"ridge\":641,\"a\":50,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":641,\"a\":52,\"owners\":[68,69]},{\"tag\":\"mate\",\"ridge\":641,\"a\":54,\"owners\":[67,69]},{\"tag\":\"mate\",\"ridge\":641,\"a\":56,\"owners\":[67,68]},{\"tag\":\"mate\",\"ridge\":641,\"a\":58,\"owners\":[67,68]},{\"tag\":\"mate\",\"ridge\":404,\"a\":75,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":420,\"a\":76,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":664,\"a\":67,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":664,\"a\":78,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":680,\"a\":68,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":680,\"a\":79,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":960,\"a\":69,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":960,\"a\":80,\"owners\":[69]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[55,56,57,58],\"full_literals\":[-32,16,17,18,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[49],\"full_literals\":[-33,10]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-34,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-35,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-36,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-37,34,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-38,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":69,\"full_literals\":[-25,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-31,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":64,\"full_literals\":[-21,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-22,41]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[67,68],\"full_literals\":[-42,23,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-23,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":68,\"full_literals\":[-24,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-29,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-30,43]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-41,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-39,-45,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-46,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[4,20,28,33,37,40,42,61,64,65,72,75,76]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[14,42,51,53,55,58,64,65,69,75,76,80]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[15,50,52,54,56,58,67,68,69,78,79,80]}]}"
  "63 37 0 39 38 0\n64 -47 0 59 58 0\n65 46 0 52 53 49 50 40 42 43 41 13 12 15 16 24 14 25 17 61 0\n66 -49 0 65 59 57 0\n67 42 25 0 31 19 45 46 22 27 18 21 29 23 20 62 0\n68 -42 0 66 56 55 47 48 26 28 44 0\n69 -23 0 68 45 0\n70 -24 0 68 46 0\n71 25 0 68 67 0\n72 -17 0 69 70 22 0\n73 -19 0 70 69 23 0\n74 -16 0 71 4 0\n75 -18 0 71 5 0\n76 31 0 71 30 0\n77 39 0 71 40 0\n78 -32 0 74 72 75 73 32 0\n79 40 0 76 41 0\n80 -45 0 77 64 54 0\n81 -34 0 78 34 0\n82 -41 0 79 80 51 0\n83 36 0 81 63 37 0\n84 -21 0 82 42 0\n85 -22 0 82 43 0\n86 35 0 83 36 0\n87 -27 0 84 24 0\n88 -28 0 85 25 0\n89 33 0 86 35 0\n90 10 0 89 33 0\n91 -6 0 90 1 0\n92 -9 0 90 2 0\n93 -20 0 90 3 0\n94 -26 0 90 6 0\n95 -4 0 90 71 10 0\n96 -5 0 90 76 11 0\n97 -8 0 93 95 84 9 0\n98 -7 0 93 95 85 8 0\n99 -1 0 95 93 84 85 7 0\n100 0 96 99 94 95 91 98 97 93 92 85 84 87 88 60 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ab25c2e9a655876a398e938ae17bc1aa6592e785d16a56965555475a358d9362d2b61d176c370da354cb31ce8b62e4b26c5ba1d8791d2729c6745e0f43c8f13c3c2a83a518560d82e07a892a43991545154358342d0758350ca314c3322c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b4d26da4d34d36924d249349249349a492492449249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 44), (facetIndex 68)]))
 (.leaf ([(facetIndex 52), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 73), (facetIndex 80)]))
 (.branch 4
 (.leaf ([(facetIndex 41), (facetIndex 58), (facetIndex 63), (facetIndex 64), (facetIndex 66)]))
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 78), (facetIndex 81)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "221009100400c36000c0001000000018z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [2]
def grouped3_0005 : List Nat := [2, 3, 4]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record006" 28

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record006" "{\"ridges\":[[19,577],[22,648],[39,577],[44,586],[46,648],[52,706],[57,580],[59,648],[62,577],[65,577],[66,900],[68,600],[69,648],[70,960],[73,586],[80,600]],\"owners\":[[19,577,[44,52,68,70],[39,57,62,65]],[39,577,[68,70],[19,44,52,57,62,65]],[62,577,[44,52,70],[19,39,57,65,68]],[65,577,[44,52,68],[19,39,57,62,70]],[57,580,[],[19,39,62,65,73,80]],[22,648,[75,81],[46,59,69]],[46,648,[81],[22,59,69,75]],[59,648,[],[22,46,69,75,81]],[69,648,[75],[22,46,59,81]],[44,586,[73],[]],[73,586,[44],[]],[52,706,[],[]],[66,900,[],[]],[68,600,[80],[]],[80,600,[68],[]],[70,960,[],[]]],\"edges\":[[41,[19,39,44,52,57,62,65,68,70,73,80]],[43,[22,41,46,52,59,64,66,69,70,75,81]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,5,7,14,16],[-3,14,16],[-10,5,7,16],[-12,5,7,14],[-8],[-2,18,20],[-6,20],[-9],[-15,18],[-5,17],[-17,5],[-7],[-13],[-14,19],[-19,14],[-16],[-21,5,14],[-5,21],[-14,21],[-17,22],[-19,22],[-4,23],[-11,23],[-18,24],[-20,24],[-21,25],[-24,26],[-23,26],[-22,-26,27],[-25,-27,28],[-28],[1,3,5,7,8,10,12,14,16,17,19],[2,4,6,7,9,11,13,15,16,18,20]],\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":577,\"a\":19,\"owners\":[44,52,68,70]},{\"tag\":\"mate\",\"ridge\":577,\"a\":39,\"owners\":[68,70]},{\"tag\":\"mate\",\"ridge\":577,\"a\":62,\"owners\":[44,52,70]},{\"tag\":\"mate\",\"ridge\":577,\"a\":65,\"owners\":[44,52,68]},{\"tag\":\"mate\",\"ridge\":580,\"a\":57,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":648,\"a\":22,\"owners\":[75,81]},{\"tag\":\"mate\",\"ridge\":648,\"a\":46,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":648,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":648,\"a\":69,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":586,\"a\":44,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":586,\"a\":73,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":706,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":900,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":600,\"a\":68,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":600,\"a\":80,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":960,\"a\":70,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[44,68],\"full_literals\":[-21,5,14]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":44,\"full_literals\":[-5,21]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":68,\"full_literals\":[-14,21]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":73,\"full_literals\":[-17,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":80,\"full_literals\":[-19,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":41,\"full_literals\":[-4,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":64,\"full_literals\":[-11,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":75,\"full_literals\":[-18,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":81,\"full_literals\":[-20,24]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0003\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-21,false,25],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,26],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-23,false,26],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-22,-26,27],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-25,-27,28],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[19,39,44,52,57,62,65,68,70,73,80]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[22,41,46,52,59,64,66,69,70,75,81]}]}"
  "34 1 3 5 10 12 14 17 19 0 12 5 16 32 0\n35 2 4 6 11 15 18 20 0 12 8 13 16 33 0\n36 21 0 16 12 18 19 3 11 2 15 1 4 34 0\n37 25 0 36 26 0\n38 -27 0 37 31 30 0\n39 22 0 36 20 21 10 14 17 0\n40 -26 0 39 38 29 0\n41 -24 0 40 27 0\n42 -23 0 40 28 0\n43 -18 0 41 24 0\n44 -20 0 41 25 0\n45 -4 0 42 22 0\n46 -11 0 42 23 0\n47 -15 0 43 9 0\n48 -6 0 44 7 0\n49 -2 0 44 43 6 0\n50 0 46 49 45 48 47 43 44 35 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3c2aaa5a2e9a65587663a4e2b85ef06a9964b9695551d58d934ad17783d0ec370ea368e5354cb31cd8b92e2b86c9b16d8791d2729c6745e0f43c8f13c3ca28aa0e946158360b81ea24a90e545154350b41da0d8390d4328c530ce0b22c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "34d349b49a69a4da492492492492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 59), (facetIndex 63), (facetIndex 64)]))
 (.leaf ([(facetIndex 46), (facetIndex 60), (facetIndex 66), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 70), (facetIndex 74), (facetIndex 75)]))
 (.branch 4
 (.leaf ([(facetIndex 71), (facetIndex 77), (facetIndex 79)]))
 (.leaf ([(facetIndex 41), (facetIndex 43), (facetIndex 49), (facetIndex 51), (facetIndex 52), (facetIndex 57)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 50), (facetIndex 53)]))
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 44), (facetIndex 45), (facetIndex 48)])))
 (.branch 8
 (.leaf ([(facetIndex 47), (facetIndex 54), (facetIndex 56), (facetIndex 58)]))
 (.branch 9
 (.leaf ([(facetIndex 42), (facetIndex 55)]))
 (.leaf ([(facetIndex 33), (facetIndex 38)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "30302200320101000001074787544546716648455906669z21;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 69)]))
 (.branch 2
 (.leaf ([(facetIndex 80)]))
 (.leaf ([(facetIndex 61), (facetIndex 67)]))))
 (.branch 4
 (.leaf ([(facetIndex 62), (facetIndex 65)]))
 (.branch 5
 (.leaf ([(facetIndex 72), (facetIndex 78)]))
 (.leaf ([(facetIndex 73), (facetIndex 76)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "110502c0004180dz2e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
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
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8, 9]
def grouped2_0016 : List Nat := [8]
def grouped2_0017 : List Nat := [8, 9]
def grouped2_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [0]
def grouped3_0020 : List Nat := [0, 1, 2]
def grouped3_0022 : List Nat := [1]
def grouped3_0023 : List Nat := [1, 2]
def grouped3_0024 : List Nat := [2]
def grouped3_0025 : List Nat := [3]
def grouped3_0026 : List Nat := [3, 4, 5]
def grouped3_0027 : List Nat := [4]
def grouped3_0028 : List Nat := [4, 5]
def grouped3_0029 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record007" 90

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record007" "{\"ridges\":[[13,577],[13,578],[14,385],[22,161],[30,162],[35,259],[41,577],[41,578],[42,385],[47,577],[48,385],[51,259],[52,577],[52,578],[53,259],[53,385],[55,385],[56,577],[56,578],[57,577],[57,578],[58,385],[60,161],[61,588],[66,161],[67,600],[69,385],[69,960],[71,162],[72,588],[73,396],[76,420],[77,162],[78,600],[80,960]],\"owners\":[[22,161,[11,39,50,53,54,65],[60,66,68]],[60,161,[11,50,53,54],[22,39,65,66,68]],[66,161,[11,39,53,54,65],[22,50,60,68]],[30,162,[11,39,50,53,54,76],[71,77,79]],[71,162,[11,50,53,54],[30,39,76,77,79]],[77,162,[11,39,53,54,76],[30,50,71,79]],[13,577,[61,67,69],[41,47,52,56,57]],[41,577,[67,69],[13,47,52,56,57,61]],[47,577,[69],[13,41,52,56,57,61,67]],[52,577,[61,69],[13,41,47,56,57,67]],[56,577,[61,67],[13,41,47,52,57,69]],[57,577,[61,67],[13,41,47,52,56,69]],[13,578,[72,78,80],[41,47,52,56,57]],[41,578,[78,80],[13,47,52,56,57,72]],[52,578,[72,80],[13,41,47,56,57,78]],[56,578,[72,78],[13,41,47,52,57,80]],[57,578,[72,78],[13,41,47,52,56,80]],[14,385,[62,65,69],[42,48,53,55,58]],[42,385,[69],[14,48,53,55,58,62,65]],[48,385,[65,69],[14,42,53,55,58,62]],[53,385,[62,69],[14,42,48,55,58,65]],[55,385,[62,65],[14,42,48,53,58,69]],[58,385,[62,65],[14,42,48,53,55,69]],[69,385,[14,42,48,53,62,65],[55,58]],[61,588,[72],[]],[72,588,[61],[]],[73,396,[62],[]],[76,420,[65],[]],[67,600,[78],[]],[78,600,[67],[]],[69,960,[80],[]],[80,960,[69],[]]],\"edges\":[[36,[11,22,30,39,50,53,54,60,65,66,68,71,76,77,79]],[41,[13,41,47,52,56,57,61,67,69,72,78,80]],[42,[14,42,48,53,55,58,62,65,69,73,76,80]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-7,-6],[-8,-6],[-9,-6],[-10,-8],[-11,-8],[-11,-9],[-12,-8],[-12,-11],[-13,-8],[-13,-11],[-14,-8],[-14,-11],[-15,-6],[-15,-7],[-15,-8],[-15,-11],[-15,-12],[-15,-13],[-17,-6],[-18,-6],[-18,-16],[-20,-6],[-20,-7],[-20,-9],[-20,-14],[-20,-16],[-20,-17],[-20,-18],[-21,-1],[-21,-12],[-22,-11],[-22,-18],[-23,-11],[-23,-17],[-23,-19],[-23,-21],[-23,-22],[-24,-11],[-24,-20],[-25,-18],[-25,-20],[-26,-7],[-26,-15],[-26,-17],[-26,-21],[-27,-3],[-27,-15],[-27,-21],[-27,-26],[-32,-20],[-33,-15],[-36,-22],[-39,-23],[-41,-21],[-42,-28],[-42,-29],[-42,-30],[-42,-31],[-43,-20],[-44,-15],[-47,-22],[-48,-37],[-50,-23],[-52,-21],[-52,-41],[-8,-24,-26],[-4,1,12,23,26,27,38],[-33,1,23,26,27],[-39,1,12,26,27,38],[-5,1,12,23,26,27,49],[-44,1,23,26,27],[-50,1,12,26,27,49],[-2,34,40,42],[-14,40,42],[-20,42],[-25,34,42],[-29,34,40],[-30,34,40],[-2,45,51,53],[-14,51,53],[-25,45,53],[-29,45,51],[-30,45,51],[-3,35,38,42],[-15,42],[-21,38,42],[-26,35,42],[-28,35,38],[-31,35,38],[-42,3,15,21,26,35,38],[-34,45],[-45,34],[-46,35],[-49,38],[-40,51],[-51,40],[-42,53],[-53,42],[-54,10,32,36,37],[-55,19,33,39,41],[-56,43,47,48],[-57,44,50,52],[-58,14,16,22,24,25,30],[-59,12,13,23,26],[-60,7,8,9,17,18,21],[-61,20,27,29,31],[-62,15,28],[-63,6,11],[-64,54],[-64,55],[-65,57],[-65,58],[-66,56],[-66,65],[-67,64],[-67,66],[-68,59,60],[-69,59],[-69,60],[-70,62,63],[-71,62],[-71,63],[-72,61,70],[-73,61,71],[-73,70],[-74,71],[-75,68,74],[-75,69,73],[-76,69,74],[-75,72],[-76,73],[-77,67,76],[-77,75],[77],[-78,42],[-42,78],[-53,79],[-34,80],[-40,80],[-35,81],[-38,81],[-45,82],[-51,82],[-49,83],[-80,84],[-79,84],[-85,78,84],[-84,85],[-78,85],[-78,-84,86],[-83,87],[-82,87],[-87,88],[-81,88],[-81,-87,89],[-85,-89,90],[-86,-88,90],[-90],[1,4,5,12,23,26,27,33,38,39,41,44,49,50,52],[2,14,20,25,29,30,34,40,42,45,51,53],[3,15,21,26,28,31,35,38,42,46,49,53]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":34,\"b\":33},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":36,\"b\":33},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":36},{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":35},{\"tag\":\"incompatible\",\"a\":41,\"b\":38},{\"tag\":\"incompatible\",\"a\":42,\"b\":33},{\"tag\":\"incompatible\",\"a\":42,\"b\":34},{\"tag\":\"incompatible\",\"a\":42,\"b\":35},{\"tag\":\"incompatible\",\"a\":42,\"b\":38},{\"tag\":\"incompatible\",\"a\":42,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":33},{\"tag\":\"incompatible\",\"a\":45,\"b\":33},{\"tag\":\"incompatible\",\"a\":45,\"b\":43},{\"tag\":\"incompatible\",\"a\":47,\"b\":33},{\"tag\":\"incompatible\",\"a\":47,\"b\":34},{\"tag\":\"incompatible\",\"a\":47,\"b\":36},{\"tag\":\"incompatible\",\"a\":47,\"b\":41},{\"tag\":\"incompatible\",\"a\":47,\"b\":43},{\"tag\":\"incompatible\",\"a\":47,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":45},{\"tag\":\"incompatible\",\"a\":48,\"b\":11},{\"tag\":\"incompatible\",\"a\":48,\"b\":39},{\"tag\":\"incompatible\",\"a\":49,\"b\":38},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":38},{\"tag\":\"incompatible\",\"a\":50,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":38},{\"tag\":\"incompatible\",\"a\":51,\"b\":47},{\"tag\":\"incompatible\",\"a\":52,\"b\":45},{\"tag\":\"incompatible\",\"a\":52,\"b\":47},{\"tag\":\"incompatible\",\"a\":53,\"b\":34},{\"tag\":\"incompatible\",\"a\":53,\"b\":42},{\"tag\":\"incompatible\",\"a\":53,\"b\":44},{\"tag\":\"incompatible\",\"a\":53,\"b\":48},{\"tag\":\"incompatible\",\"a\":54,\"b\":14},{\"tag\":\"incompatible\",\"a\":54,\"b\":42},{\"tag\":\"incompatible\",\"a\":54,\"b\":48},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":59,\"b\":47},{\"tag\":\"incompatible\",\"a\":60,\"b\":42},{\"tag\":\"incompatible\",\"a\":63,\"b\":49},{\"tag\":\"incompatible\",\"a\":66,\"b\":50},{\"tag\":\"incompatible\",\"a\":68,\"b\":48},{\"tag\":\"incompatible\",\"a\":69,\"b\":55},{\"tag\":\"incompatible\",\"a\":69,\"b\":56},{\"tag\":\"incompatible\",\"a\":69,\"b\":57},{\"tag\":\"incompatible\",\"a\":69,\"b\":58},{\"tag\":\"incompatible\",\"a\":70,\"b\":47},{\"tag\":\"incompatible\",\"a\":71,\"b\":42},{\"tag\":\"incompatible\",\"a\":74,\"b\":49},{\"tag\":\"incompatible\",\"a\":75,\"b\":64},{\"tag\":\"incompatible\",\"a\":77,\"b\":50},{\"tag\":\"incompatible\",\"a\":79,\"b\":48},{\"tag\":\"incompatible\",\"a\":79,\"b\":68},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[35,51,53]},{\"tag\":\"mate\",\"ridge\":161,\"a\":22,\"owners\":[11,39,50,53,54,65]},{\"tag\":\"mate\",\"ridge\":161,\"a\":60,\"owners\":[11,50,53,54]},{\"tag\":\"mate\",\"ridge\":161,\"a\":66,\"owners\":[11,39,53,54,65]},{\"tag\":\"mate\",\"ridge\":162,\"a\":30,\"owners\":[11,39,50,53,54,76]},{\"tag\":\"mate\",\"ridge\":162,\"a\":71,\"owners\":[11,50,53,54]},{\"tag\":\"mate\",\"ridge\":162,\"a\":77,\"owners\":[11,39,53,54,76]},{\"tag\":\"mate\",\"ridge\":577,\"a\":13,\"owners\":[61,67,69]},{\"tag\":\"mate\",\"ridge\":577,\"a\":41,\"owners\":[67,69]},{\"tag\":\"mate\",\"ridge\":577,\"a\":47,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":577,\"a\":52,\"owners\":[61,69]},{\"tag\":\"mate\",\"ridge\":577,\"a\":56,\"owners\":[61,67]},{\"tag\":\"mate\",\"ridge\":577,\"a\":57,\"owners\":[61,67]},{\"tag\":\"mate\",\"ridge\":578,\"a\":13,\"owners\":[72,78,80]},{\"tag\":\"mate\",\"ridge\":578,\"a\":41,\"owners\":[78,80]},{\"tag\":\"mate\",\"ridge\":578,\"a\":52,\"owners\":[72,80]},{\"tag\":\"mate\",\"ridge\":578,\"a\":56,\"owners\":[72,78]},{\"tag\":\"mate\",\"ridge\":578,\"a\":57,\"owners\":[72,78]},{\"tag\":\"mate\",\"ridge\":385,\"a\":14,\"owners\":[62,65,69]},{\"tag\":\"mate\",\"ridge\":385,\"a\":42,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":385,\"a\":48,\"owners\":[65,69]},{\"tag\":\"mate\",\"ridge\":385,\"a\":53,\"owners\":[62,69]},{\"tag\":\"mate\",\"ridge\":385,\"a\":55,\"owners\":[62,65]},{\"tag\":\"mate\",\"ridge\":385,\"a\":58,\"owners\":[62,65]},{\"tag\":\"mate\",\"ridge\":385,\"a\":69,\"owners\":[14,42,48,53,62,65]},{\"tag\":\"mate\",\"ridge\":588,\"a\":61,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":588,\"a\":72,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":396,\"a\":73,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":420,\"a\":76,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":600,\"a\":67,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":600,\"a\":78,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":960,\"a\":69,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":960,\"a\":80,\"owners\":[69]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[37,59,63,64],\"full_literals\":[-54,10,32,36,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[46,60,66,68],\"full_literals\":[-55,19,33,39,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[70,74,75],\"full_literals\":[-56,43,47,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[71,77,79],\"full_literals\":[-57,44,50,52]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[41,43,49,51,52,57],\"full_literals\":[-58,14,16,22,24,25,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[39,40,50,53],\"full_literals\":[-59,12,13,23,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[34,35,36,44,45,48],\"full_literals\":[-60,7,8,9,17,18,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[47,54,56,58],\"full_literals\":[-61,20,27,29,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[42,55],\"full_literals\":[-62,15,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[33,38],\"full_literals\":[-63,6,11]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-67,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-67,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,59,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-69,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-70,62,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-71,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,61,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,61,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-74,false,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-75,68,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-75,69,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-76,69,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-75,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-76,false,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-77,67,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-77,false,75],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[69],\"full_literals\":[-78,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":69,\"full_literals\":[-42,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-53,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":61,\"full_literals\":[-34,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-40,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":62,\"full_literals\":[-35,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":65,\"full_literals\":[-38,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":72,\"full_literals\":[-45,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":78,\"full_literals\":[-51,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":76,\"full_literals\":[-49,83]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-80,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-79,false,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,78,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-84,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-78,-84,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-81,-87,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-85,-89,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-86,-88,90],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":36,\"owners\":[11,22,30,39,50,53,54,60,65,66,68,71,76,77,79]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[13,41,47,52,56,57,61,67,69,72,78,80]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[14,42,48,53,55,58,62,65,69,73,76,80]}]}"
  "162 75 0 134 133 0\n163 72 0 162 130 0\n164 85 0 148 149 145 146 136 138 139 137 75 73 76 77 78 92 74 96 160 0\n165 -89 0 164 158 156 0\n166 84 0 164 146 147 137 135 97 0\n167 81 42 0 98 85 140 141 89 93 84 87 94 88 86 161 0\n168 42 0 165 75 98 167 155 152 142 143 79 81 82 83 91 80 95 160 0\n169 -28 0 168 55 0\n170 -29 0 168 56 0\n171 -30 0 168 57 0\n172 -31 0 168 58 0\n173 78 0 168 136 0\n174 86 0 173 166 150 0\n175 -88 0 174 158 157 0\n176 -87 0 175 153 0\n177 -81 0 175 154 0\n178 -83 0 176 151 0\n179 -35 0 177 140 0\n180 -38 0 177 141 0\n181 -49 0 178 144 0\n182 -76 27 62 21 0 172 170 121 126 129 131 119 124 125 106 120 22 23 24 27 28 108 105 5 0\n183 -73 -58 27 62 0 172 170 171 121 124 125 106 120 22 25 26 39 41 108 103 31 0\n184 -11 -59 26 0 8 10 33 104 0\n185 -6 -60 21 0 1 2 3 19 20 105 0\n186 15 21 26 0 169 180 179 168 134 162 163 172 170 171 107 90 46 182 132 116 114 112 183 128 118 119 184 185 108 120 123 106 23 24 25 26 27 28 39 41 105 103 7 9 37 104 0\n187 -67 -23 -15 0 63 53 35 60 51 115 116 110 114 100 111 65 102 0\n188 -69 21 26 0 134 172 170 186 16 13 108 122 47 18 17 15 14 118 119 104 34 187 132 131 124 106 24 28 105 0\n189 21 26 0 170 172 134 162 186 13 14 15 16 17 18 47 108 122 126 127 188 128 129 124 132 106 187 24 27 28 104 105 117 0\n190 26 0 181 180 189 29 30 36 48 54 64 67 69 70 72 68 71 159 0\n191 -7 0 190 42 0\n192 -15 0 190 43 0\n193 -17 0 190 44 0\n194 -21 0 190 45 0\n195 -27 0 190 49 0\n196 -62 0 192 169 107 0\n197 -76 0 195 196 194 182 0\n198 67 0 197 134 132 0\n199 64 0 198 115 0\n200 66 0 198 116 0\n201 54 0 199 109 0\n202 56 0 200 113 0\n203 65 0 200 114 0\n204 58 0 203 112 0\n205 -73 0 204 195 196 183 0\n206 69 0 205 162 128 0\n207 60 0 206 119 0\n208 -6 0 207 194 185 0\n209 -8 0 190 208 196 163 172 195 170 171 204 201 202 4 5 11 66 108 120 123 106 26 41 50 59 103 52 61 99 101 62 0\n210 -9 0 208 172 195 170 196 163 6 24 108 106 120 123 0\n211 18 0 210 207 193 191 209 194 105 0\n212 -16 0 211 21 0\n213 -20 0 211 28 0\n214 -22 0 211 32 0\n215 -25 0 211 40 0\n216 -61 0 213 170 195 172 106 0\n217 70 0 216 163 123 0\n218 63 0 217 196 120 0\n219 11 0 218 208 108 0\n220 -14 0 219 12 0\n221 -24 0 219 38 0\n222 0 220 221 212 215 204 214 171 103 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00044.record007
