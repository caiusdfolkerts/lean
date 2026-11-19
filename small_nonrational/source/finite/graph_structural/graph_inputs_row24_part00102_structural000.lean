module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00102Data
public import GraphInputsRow24Part00102Frames
public import GraphInputsRow24Part00102Leaves
public import GraphInputsRow24Part00102Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009
def vertexColumn : Fields := ⟨10, hexnat% "3e2d43b29c670dcb48f23aa9a368ba1eac6a98e6c5a969595635a8e3392e2b86e8791e2785eb44f13a699364b91e6c5a94e5c5695955553568d3352d2b46d8751d2745dc4e5354c734ac6b86c5b0ef0791d4789d2785d1715e0f13c1f390ac468664382e464654342d18e1344c5342c2b06e0741c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6d36db6db6da6db6da49a6db6db6da6db6da49a6d2492492492492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨56, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨80, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200100400100400000000000", hexnat% "100000102004400000", hexnat% "1800001800000000000", 2203485995008, 1984274890752, 4051697664, 68719476736]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010
def vertexColumn : Fields := ⟨10, hexnat% "f8b50ec570dc3c8ea368ba1eaa639b16a5996358ce4b8ae1ba1e4789e17ad13c5591e6c5a94e5c5695955553554d4b61d4745da8ce3c4e9334cb31cd2b1ae1b16c3bc1e8731e2749ca719e1745c9715e0f13c1f3906ca491aa18a64382e1a519164654344d0b61344d0b0ac1b81d0709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "da6db6da4d36d24d36da4da6db69349b49b692492692493692249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "122a0106c4637e7000000", hexnat% "10081000000000000000000", hexnat% "1800000c000000000", 141836999983104]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "281806c06d287000000", hexnat% "20200000000060000000", hexnat% "10080001000000000000000", 158913789952, hexnat% "101000000000000000000", 212205744160768]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "101a3a1806c06c7e3000000", 1152991942070501376, 137506062336, 141836999983104]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2121806c06c063000000", 212205744160768, hexnat% "2000000000304000000", hexnat% "100000000001400000000", hexnat% "10080801000000080000000", 137438953472]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000068c577e7000000", hexnat% "20200004000000000000", hexnat% "18000008000000000", hexnat% "181000000000000000000", hexnat% "10000801000000000000000", 2199023255552]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2020102cc53765000000", hexnat% "18040000000000000", hexnat% "3800000000000000000", hexnat% "180000000000000000000", 3023690530816, hexnat% "10000000000000080000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "101838010284017a4000000", 140876017827840, hexnat% "18044000000000000", hexnat% "20200000000000000000", 7421737041920, 1099511627776]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100818010280000a4000000", hexnat% "18044000000000000", hexnat% "120000000001000000000", hexnat% "2200000040001000000", 212206817902592, 167503724544, 3023690530816]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c13 c2
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f43b2d23caaa3ab1aa69561d92e1ba1e47ad13c6a93a719a659939555354b51d4cd4b4ad1b61d4749db0ea338f13a4e5354cd32cc73c2e8b32e2b4acab1ae1b46c9b51d2785c3783c4f07c66458564382e38691346892a465454554342d18e1344c5382d0b0ad0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6924d24934d24d34934db49249a49a4924d2492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 38), (facetIndex 40), (facetIndex 42), (facetIndex 70)]))
 (.leaf ([(facetIndex 46), (facetIndex 48), (facetIndex 49), (facetIndex 72)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 32), (facetIndex 75), (facetIndex 76)]))
 (.branch 4
 (.leaf ([(facetIndex 30), (facetIndex 33), (facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 27), (facetIndex 35), (facetIndex 36), (facetIndex 55), (facetIndex 67), (facetIndex 73)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 44), (facetIndex 51), (facetIndex 61), (facetIndex 65), (facetIndex 71)]))
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 50)]))
 (.leaf ([(facetIndex 47), (facetIndex 63), (facetIndex 64)]))))
 (.branch 9
 (.leaf ([(facetIndex 29), (facetIndex 39), (facetIndex 59)]))
 (.branch 10
 (.leaf ([(facetIndex 37), (facetIndex 57), (facetIndex 58), (facetIndex 69)]))
 (.leaf ([(facetIndex 31)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "33220415090405770508990400056117105600080944032a3824z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 60), (facetIndex 62)]))
 (.branch 2
 (.leaf ([(facetIndex 85), (facetIndex 86)]))
 (.leaf ([(facetIndex 34), (facetIndex 56), (facetIndex 66), (facetIndex 68)]))))
 (.branch 4
 (.leaf ([(facetIndex 74), (facetIndex 79), (facetIndex 80)]))
 (.branch 5
 (.leaf ([(facetIndex 41), (facetIndex 45), (facetIndex 52), (facetIndex 53)]))
 (.leaf ([(facetIndex 81), (facetIndex 82), (facetIndex 83), (facetIndex 84)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4db6b6000c000208000000202400002002000008z19;"⟩
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
def grouped2_0011 : List Nat := [5, 6, 7]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [6, 7]
def grouped2_0015 : List Nat := [7]
def grouped2_0016 : List Nat := [8]
def grouped2_0017 : List Nat := [8, 9, 10]
def grouped2_0018 : List Nat := [9]
def grouped2_0019 : List Nat := [9, 10]
def grouped2_0020 : List Nat := [10]
def grouped3_0021 : List Nat := [0]
def grouped3_0022 : List Nat := [0, 1, 2]
def grouped3_0024 : List Nat := [1]
def grouped3_0025 : List Nat := [1, 2]
def grouped3_0026 : List Nat := [2]
def grouped3_0027 : List Nat := [3]
def grouped3_0028 : List Nat := [3, 4, 5]
def grouped3_0029 : List Nat := [4]
def grouped3_0030 : List Nat := [4, 5]
def grouped3_0031 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0014\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0019\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record001" 71

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record001" "{\"ridges\":[[7,522],[10,530],[15,273],[18,641],[18,648],[20,641],[20,656],[25,274],[29,522],[36,522],[38,168],[40,522],[42,648],[43,521],[43,522],[46,208],[48,530],[49,656],[50,529],[50,530],[52,641],[52,674],[53,641],[53,706],[55,273],[66,408],[67,648],[70,648],[72,656],[73,274],[74,540],[79,154],[80,792],[82,674],[84,706]],\"owners\":[[43,521,[18,56,67,70],[7,29,36,40,68]],[7,522,[74,79,80,82],[29,36,40,42,43]],[29,522,[79,80,82],[7,36,40,42,43,74]],[36,522,[82],[7,29,40,42,43,74,79,80]],[40,522,[74,79,80],[7,29,36,42,43,82]],[43,522,[74,79,82],[7,29,36,40,42,80]],[15,273,[9,35,47,50,66,68],[55,64]],[55,273,[9,47,50],[15,35,64,66,68]],[25,274,[9,35,47,50,80],[73,78]],[73,274,[9,47,50],[25,35,78,80]],[50,529,[20,56,67,72],[10,31,36,48,68]],[10,530,[74,79,80,84],[31,36,48,49,50]],[48,530,[74,79,80],[10,31,36,49,50,84]],[50,530,[74,79,84],[10,31,36,48,49,80]],[38,168,[85],[17,58,69,70,81,82]],[18,648,[79,82],[42,67,70]],[42,648,[],[18,67,70,79,82]],[67,648,[82],[18,42,70,79]],[70,648,[79],[18,42,67,82]],[46,208,[86],[19,63,71,72,83,84]],[20,656,[79,84],[49,67,72]],[49,656,[],[20,67,72,79,84]],[72,656,[79],[20,49,67,84]],[79,154,[34],[]],[52,674,[82],[]],[82,674,[52],[]],[53,706,[84],[]],[84,706,[53],[]],[74,540,[56],[]],[66,408,[],[]],[80,792,[68],[]]],\"edges\":[[29,[7,18,29,36,40,42,43,56,67,68,70,74,79,80,82]],[33,[9,15,25,35,47,50,55,64,66,68,73,78,80]],[34,[10,20,31,36,48,49,50,56,67,68,72,74,79,80,84]],[43,[18,20,42,49,52,53,67,70,72,79,82,84]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-2],[-12,-10],[-16,-11],[-18,-8],[-18,-9],[-18,-12],[-18,-13],[-18,-15],[-20,-10],[-21,-11],[-23,-8],[-23,-10],[-23,-12],[-23,-13],[-23,-18],[-26,-13],[-28,-26],[-29,-10],[-31,-24],[-31,-25],[-31,-26],[-33,-11],[-34,-11],[-35,-13],[-35,-31],[-37,-10],[-38,-8],[-38,-12],[-38,-14],[-38,-19],[-38,-26],[-38,-32],[-38,-35],[-41,-40],[-18,5,27,31,33],[-1,36,38,39,40],[-9,38,39,40],[-13,40],[-16,36,38,39],[-18,36,38,40],[-4,2,12,20,23,30,32],[-26,2,20,23],[-7,2,12,20,23,39],[-35,2,20,23],[-23,6,27,31,34],[-3,36,38,39,41],[-21,36,38,39],[-23,36,38,41],[-14,42],[-5,-6,-24],[-5,-6,-25],[-5,38,40],[-17],[-31,40],[-33,38],[-19,43],[-6,38,41],[-22],[-34,38],[-38,11],[-24,40],[-40,24],[-25,41],[-41,25],[-36,27],[-30],[-39,32],[-44,14,16,17,33],[-45,19,21,22,34],[-46,8,12,13,26,31,35],[-47,18,23],[-48,9,15,28],[-49,10],[-50,44,45],[-51,46],[-52,51],[-53,50,52],[-54,50],[-55,47],[-56,55],[-57,49],[-58,48,57],[-59,57],[-60,56,59],[-60,58],[-61,59],[-62,53,61],[-62,54,60],[62],[-42,63],[-43,63],[-11,64],[-27,64],[-32,64],[-24,65],[-25,65],[-40,66],[-41,66],[-64,67],[-63,67],[-67,68],[-65,-66,69],[-69,70],[-68,-70,71],[-71],[1,5,9,13,16,17,18,27,31,32,33,36,38,39,40],[2,4,7,12,20,23,26,29,30,32,35,37,39],[3,6,10,13,21,22,23,27,31,32,34,36,38,39,41],[5,6,17,22,24,25,31,33,34,38,40,41]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":31,\"b\":9},{\"tag\":\"incompatible\",\"a\":35,\"b\":31},{\"tag\":\"incompatible\",\"a\":40,\"b\":34},{\"tag\":\"incompatible\",\"a\":43,\"b\":27},{\"tag\":\"incompatible\",\"a\":43,\"b\":29},{\"tag\":\"incompatible\",\"a\":43,\"b\":35},{\"tag\":\"incompatible\",\"a\":43,\"b\":36},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":47,\"b\":31},{\"tag\":\"incompatible\",\"a\":48,\"b\":34},{\"tag\":\"incompatible\",\"a\":50,\"b\":27},{\"tag\":\"incompatible\",\"a\":50,\"b\":31},{\"tag\":\"incompatible\",\"a\":50,\"b\":35},{\"tag\":\"incompatible\",\"a\":50,\"b\":36},{\"tag\":\"incompatible\",\"a\":50,\"b\":43},{\"tag\":\"incompatible\",\"a\":55,\"b\":36},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":64,\"b\":31},{\"tag\":\"incompatible\",\"a\":67,\"b\":52},{\"tag\":\"incompatible\",\"a\":67,\"b\":53},{\"tag\":\"incompatible\",\"a\":67,\"b\":55},{\"tag\":\"incompatible\",\"a\":70,\"b\":34},{\"tag\":\"incompatible\",\"a\":72,\"b\":34},{\"tag\":\"incompatible\",\"a\":73,\"b\":36},{\"tag\":\"incompatible\",\"a\":73,\"b\":67},{\"tag\":\"incompatible\",\"a\":78,\"b\":31},{\"tag\":\"incompatible\",\"a\":79,\"b\":27},{\"tag\":\"incompatible\",\"a\":79,\"b\":35},{\"tag\":\"incompatible\",\"a\":79,\"b\":38},{\"tag\":\"incompatible\",\"a\":79,\"b\":46},{\"tag\":\"incompatible\",\"a\":79,\"b\":55},{\"tag\":\"incompatible\",\"a\":79,\"b\":68},{\"tag\":\"incompatible\",\"a\":79,\"b\":73},{\"tag\":\"incompatible\",\"a\":84,\"b\":82},{\"tag\":\"mate\",\"ridge\":521,\"a\":43,\"owners\":[18,56,67,70]},{\"tag\":\"mate\",\"ridge\":522,\"a\":7,\"owners\":[74,79,80,82]},{\"tag\":\"mate\",\"ridge\":522,\"a\":29,\"owners\":[79,80,82]},{\"tag\":\"mate\",\"ridge\":522,\"a\":36,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":522,\"a\":40,\"owners\":[74,79,80]},{\"tag\":\"mate\",\"ridge\":522,\"a\":43,\"owners\":[74,79,82]},{\"tag\":\"mate\",\"ridge\":273,\"a\":15,\"owners\":[9,35,47,50,66,68]},{\"tag\":\"mate\",\"ridge\":273,\"a\":55,\"owners\":[9,47,50]},{\"tag\":\"mate\",\"ridge\":274,\"a\":25,\"owners\":[9,35,47,50,80]},{\"tag\":\"mate\",\"ridge\":274,\"a\":73,\"owners\":[9,47,50]},{\"tag\":\"mate\",\"ridge\":529,\"a\":50,\"owners\":[20,56,67,72]},{\"tag\":\"mate\",\"ridge\":530,\"a\":10,\"owners\":[74,79,80,84]},{\"tag\":\"mate\",\"ridge\":530,\"a\":48,\"owners\":[74,79,80]},{\"tag\":\"mate\",\"ridge\":530,\"a\":50,\"owners\":[74,79,84]},{\"tag\":\"mate\",\"ridge\":168,\"a\":38,\"owners\":[85]},{\"tag\":\"three\",\"ridge\":641,\"vertices\":[18,20,52]},{\"tag\":\"three\",\"ridge\":641,\"vertices\":[18,20,53]},{\"tag\":\"mate\",\"ridge\":648,\"a\":18,\"owners\":[79,82]},{\"tag\":\"mate\",\"ridge\":648,\"a\":42,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":648,\"a\":67,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":648,\"a\":70,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":208,\"a\":46,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":656,\"a\":20,\"owners\":[79,84]},{\"tag\":\"mate\",\"ridge\":656,\"a\":49,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":656,\"a\":72,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":154,\"a\":79,\"owners\":[34]},{\"tag\":\"mate\",\"ridge\":674,\"a\":52,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":674,\"a\":82,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":706,\"a\":53,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":706,\"a\":84,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":540,\"a\":74,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":408,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":792,\"a\":80,\"owners\":[68]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[38,40,42,70],\"full_literals\":[-44,14,16,17,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[46,48,49,72],\"full_literals\":[-45,19,21,22,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[27,35,36,55,67,73],\"full_literals\":[-46,8,12,13,26,31,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[43,50],\"full_literals\":[-47,18,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[29,39,59],\"full_literals\":[-48,9,15,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":10,\"members\":[31],\"full_literals\":[-49,10]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,44,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-53,50,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-54,50,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0013\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0014\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0018\",\"right_name\":\"grouped2_0020\",\"joined_name\":\"grouped2_0019\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,48,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-60,56,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":3,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-61,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-62,53,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-62,54,60],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-42,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":86,\"full_literals\":[-43,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":34,\"full_literals\":[-11,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":56,\"full_literals\":[-27,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":68,\"full_literals\":[-32,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":52,\"full_literals\":[-24,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":53,\"full_literals\":[-25,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-40,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-41,66]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-66,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-68,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[7,18,29,36,40,42,43,56,67,68,70,74,79,80,82]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[9,15,25,35,47,50,55,64,66,68,73,78,80]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[10,20,31,36,48,49,50,56,67,68,72,74,79,80,84]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,20,42,49,52,53,67,70,72,79,82,84]}]}"
  "p cnf 71 109\n-10 -2 0\n-12 -10 0\n-16 -11 0\n-18 -8 0\n-18 -9 0\n-18 -12 0\n-18 -13 0\n-18 -15 0\n-20 -10 0\n-21 -11 0\n-23 -8 0\n-23 -10 0\n-23 -12 0\n-23 -13 0\n-23 -18 0\n-26 -13 0\n-28 -26 0\n-29 -10 0\n-31 -24 0\n-31 -25 0\n-31 -26 0\n-33 -11 0\n-34 -11 0\n-35 -13 0\n-35 -31 0\n-37 -10 0\n-38 -8 0\n-38 -12 0\n-38 -14 0\n-38 -19 0\n-38 -26 0\n-38 -32 0\n-38 -35 0\n-41 -40 0\n-18 5 27 31 33 0\n-1 36 38 39 40 0\n-9 38 39 40 0\n-13 40 0\n-16 36 38 39 0\n-18 36 38 40 0\n-4 2 12 20 23 30 32 0\n-26 2 20 23 0\n-7 2 12 20 23 39 0\n-35 2 20 23 0\n-23 6 27 31 34 0\n-3 36 38 39 41 0\n-21 36 38 39 0\n-23 36 38 41 0\n-14 42 0\n-5 -6 -24 0\n-5 -6 -25 0\n-5 38 40 0\n-17 0\n-31 40 0\n-33 38 0\n-19 43 0\n-6 38 41 0\n-22 0\n-34 38 0\n-38 11 0\n-24 40 0\n-40 24 0\n-25 41 0\n-41 25 0\n-36 27 0\n-30 0\n-39 32 0\n-44 14 16 17 33 0\n-45 19 21 22 34 0\n-46 8 12 13 26 31 35 0\n-47 18 23 0\n-48 9 15 28 0\n-49 10 0\n-50 44 45 0\n-51 46 0\n-52 51 0\n-53 50 52 0\n-54 50 0\n-55 47 0\n-56 55 0\n-57 49 0\n-58 48 57 0\n-59 57 0\n-60 56 59 0\n-60 58 0\n-61 59 0\n-62 53 61 0\n-62 54 60 0\n62 0\n-42 63 0\n-43 63 0\n-11 64 0\n-27 64 0\n-32 64 0\n-24 65 0\n-25 65 0\n-40 66 0\n-41 66 0\n-64 67 0\n-63 67 0\n-67 68 0\n-65 -66 69 0\n-69 70 0\n-68 -70 71 0\n-71 0\n1 5 9 13 16 17 18 27 31 32 33 36 38 39 40 0\n2 4 7 12 20 23 26 29 30 32 35 37 39 0\n3 6 10 13 21 22 23 27 31 32 34 36 38 39 41 0\n5 6 17 22 24 25 31 33 34 38 40 41 0\n"
  "110 -44 14 16 33 0 53 68 0\n111 -45 19 21 34 0 58 69 0\n112 1 5 9 13 16 18 27 31 32 33 36 38 39 40 0 53 106 0\n113 2 4 7 12 20 23 26 29 32 35 37 39 0 66 107 0\n114 3 6 10 13 21 23 27 31 32 34 36 38 39 41 0 58 108 0\n115 5 6 24 25 31 33 34 38 40 41 0 53 58 109 0\n116 -10 32 0 66 67 1 2 9 12 18 26 41 42 44 43 113 0\n117 -18 26 35 67 0 89 99 92 60 55 100 90 49 94 67 93 65 39 110 59 91 56 47 111 74 116 73 81 83 86 87 77 76 75 4 6 7 40 70 62 19 0\n118 26 35 67 0 89 99 92 60 55 100 90 49 94 67 93 65 39 110 59 91 56 47 111 74 116 73 81 83 86 87 77 76 75 78 88 84 80 79 117 71 11 13 14 48 70 64 20 0\n119 -23 -26 64 0 21 16 94 67 92 60 93 65 39 59 55 15 48 45 34 64 51 37 36 112 0\n120 -26 67 0 89 99 92 60 55 100 90 49 94 67 93 65 39 110 59 91 56 47 111 74 78 88 116 73 81 83 84 80 79 85 82 17 119 71 5 8 72 0\n121 23 67 0 89 120 118 25 24 99 92 60 55 100 90 49 94 67 93 65 39 110 59 91 56 47 111 74 78 88 116 73 81 83 84 80 79 71 40 35 34 62 50 46 114 0\n122 67 0 99 92 93 94 60 65 67 55 59 39 120 118 24 25 121 15 48 45 34 64 51 37 36 112 0\n123 68 0 122 101 0\n124 -70 0 123 105 104 0\n125 -69 0 124 103 0\n126 40 41 31 38 0 57 63 59 55 61 52 115 0\n127 -40 0 125 62 97 95 102 0\n128 -13 0 127 38 0\n129 -31 0 127 54 0\n130 -41 0 125 64 98 96 102 0\n131 38 0 130 129 127 126 0\n132 -8 0 131 27 0\n133 -12 0 131 28 0\n134 -14 0 131 29 0\n135 -19 0 131 30 0\n136 -26 0 131 31 0\n137 -32 0 131 32 0\n138 -35 0 131 33 0\n139 11 0 131 60 0\n140 -10 0 137 116 0\n141 -46 0 138 136 128 133 129 132 70 0\n142 -16 0 139 3 0\n143 -21 0 139 10 0\n144 -33 0 139 22 0\n145 -34 0 139 23 0\n146 -49 0 140 73 0\n147 -51 0 141 75 0\n148 -44 0 142 134 144 110 0\n149 -45 0 143 135 145 111 0\n150 -57 0 146 81 0\n151 -52 0 147 76 0\n152 -50 0 148 149 74 0\n153 -59 0 150 83 0\n154 -53 0 152 151 77 0\n155 -61 0 153 86 0\n156 0 154 155 89 87 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2d4ab31ca72d23cb1a1eac6a98e6c5a969595635b0e8b92e1ba1e4785e3c6992e479a5595554d5a352d2b46d8751d2745d38e9354cd32cc734ac6b86c5b0ee8751cc749ca785d1725c5783c4f07ce48691a19a0e4382e384d1464c5294654342d18d1314d0b0ac1b41c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6da6da6db6924934db6da69269b4d269249349269a491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 52), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 34), (facetIndex 44), (facetIndex 47), (facetIndex 56), (facetIndex 63)])))
 (.branch 3
 (.leaf ([(facetIndex 67), (facetIndex 76)]))
 (.leaf ([(facetIndex 25), (facetIndex 37), (facetIndex 38), (facetIndex 39), (facetIndex 80)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 28), (facetIndex 30), (facetIndex 50), (facetIndex 65), (facetIndex 66)]))
 (.leaf ([(facetIndex 26), (facetIndex 27), (facetIndex 68), (facetIndex 69), (facetIndex 70)])))
 (.branch 7
 (.leaf ([(facetIndex 35), (facetIndex 42), (facetIndex 45)]))
 (.leaf ([(facetIndex 40), (facetIndex 41)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "300200016d5202000010001002311bf6d8c40104b58z12;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 48), (facetIndex 79)])))
 (.branch 3
 (.leaf ([(facetIndex 49), (facetIndex 55), (facetIndex 85)]))
 (.leaf ([(facetIndex 29), (facetIndex 36), (facetIndex 77), (facetIndex 78), (facetIndex 81)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 46), (facetIndex 71), (facetIndex 82)]))
 (.leaf ([(facetIndex 31), (facetIndex 57), (facetIndex 58), (facetIndex 64), (facetIndex 73), (facetIndex 74), (facetIndex 75), (facetIndex 83)])))
 (.branch 7
 (.leaf ([(facetIndex 51), (facetIndex 72), (facetIndex 84), (facetIndex 86)]))
 (.leaf ([(facetIndex 59), (facetIndex 62)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "196b182d8b6e8000051c0f68400c11100000003000a18z15;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6, 7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1]
def grouped3_0009 : List Nat := [0, 1, 2, 3]
def grouped3_0011 : List Nat := [1]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [2, 3]
def grouped3_0014 : List Nat := [3]
def grouped3_0015 : List Nat := [4]
def grouped3_0016 : List Nat := [4, 5]
def grouped3_0017 : List Nat := [4, 5, 6, 7]
def grouped3_0018 : List Nat := [5]
def grouped3_0019 : List Nat := [6]
def grouped3_0020 : List Nat := [6, 7]
def grouped3_0021 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record005" 56

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record005" "{\"ridges\":[[7,82],[16,208],[28,82],[36,644],[38,82],[42,82],[44,82],[45,82],[46,643],[46,656],[55,649],[56,208],[59,644],[62,649],[63,208],[64,92],[66,536],[72,340],[74,644],[74,656],[77,674],[78,644],[81,178],[82,656],[82,706],[83,644],[85,680],[86,596],[86,644]],\"owners\":[[7,82,[64,71,72,73,79,81,82],[28,38,42,44,45]],[28,82,[79,81,82],[7,38,42,44,45,64,71,72,73]],[38,82,[71,72,73,81,82],[7,28,42,44,45,64,79]],[42,82,[64,71,72,73,82],[7,28,38,44,45,79,81]],[44,82,[64,72,73,79],[7,28,38,42,45,71,81,82]],[45,82,[64,71,73,79,81,82],[7,28,38,42,44,72]],[16,208,[71,81,82,86],[44,56,63]],[56,208,[81,82],[16,44,63,71,86]],[63,208,[71,82,86],[16,44,56,81]],[66,536,[62],[23,39,51,80,83,84]],[46,643,[36],[]],[36,644,[83,85,86],[55,59,74,77,78]],[59,644,[77,78,85],[36,55,74,83,86]],[74,644,[55,85],[36,59,77,78,83,86]],[78,644,[55,59,83,85],[36,74,77,86]],[83,644,[36,77,78],[55,59,74,85,86]],[86,644,[36,55,77,85],[59,74,78,83]],[81,178,[43],[]],[46,656,[83,86],[59,62,74,82]],[74,656,[62],[46,59,82,83,86]],[82,656,[59,62,83],[46,74,86]],[64,92,[48],[]],[55,649,[62],[]],[62,649,[55],[]],[72,340,[57],[]],[86,596,[73],[]],[77,674,[],[]],[82,706,[78],[]],[85,680,[],[]]],\"edges\":[[31,[7,16,28,38,42,44,45,48,56,57,60,63,64,71,72,73,79,81,82,86]],[43,[36,46,55,59,62,74,77,78,82,83,85,86]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-33,-3],[-33,-4],[-33,-13],[-33,-22],[-1,21,24,25,26,30,31,32],[-3,30,31,32],[-6,24,25,26,31,32],[-7,21,24,25,26,32],[-9,21,25,26,30],[-10,21,24,26,30,31,32],[-2,24,31,32,35],[-15,31,32],[-20,24,32,35],[-23,19],[-11,5],[-5,33,34,35],[-17,28,29,34],[-27,14,34],[-29,14,17,33,34],[-33,5,28,29],[-35,5,14,28,34],[-31,8],[-11,33,35],[-27,19],[-32,17,19,33],[-21,12],[-14,19],[-19,14],[-25,16],[-35,26],[-28],[-32,29],[-34],[-36,3,4,13,22,23],[-37,36],[-38,37],[-39,38],[39],[-8,40],[-18,40],[-12,41],[-30,41],[-14,42],[-5,43],[-29,43],[-24,44],[-32,44],[-16,45],[-26,45],[-35,46],[-17,47],[-19,47],[-41,48],[-40,48],[-43,49],[-42,49],[-49,50],[-48,-49,51],[-45,52],[-44,52],[-47,53],[-46,53],[-53,54],[-52,-53,55],[-50,-55,56],[-51,-54,56],[-56],[1,2,3,6,7,9,10,12,15,16,18,20,21,24,25,26,30,31,32,35],[5,11,14,17,19,27,28,29,32,33,34,35]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":83,\"b\":28},{\"tag\":\"incompatible\",\"a\":83,\"b\":30},{\"tag\":\"incompatible\",\"a\":83,\"b\":50},{\"tag\":\"incompatible\",\"a\":83,\"b\":65},{\"tag\":\"mate\",\"ridge\":82,\"a\":7,\"owners\":[64,71,72,73,79,81,82]},{\"tag\":\"mate\",\"ridge\":82,\"a\":28,\"owners\":[79,81,82]},{\"tag\":\"mate\",\"ridge\":82,\"a\":38,\"owners\":[71,72,73,81,82]},{\"tag\":\"mate\",\"ridge\":82,\"a\":42,\"owners\":[64,71,72,73,82]},{\"tag\":\"mate\",\"ridge\":82,\"a\":44,\"owners\":[64,72,73,79]},{\"tag\":\"mate\",\"ridge\":82,\"a\":45,\"owners\":[64,71,73,79,81,82]},{\"tag\":\"mate\",\"ridge\":208,\"a\":16,\"owners\":[71,81,82,86]},{\"tag\":\"mate\",\"ridge\":208,\"a\":56,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":208,\"a\":63,\"owners\":[71,82,86]},{\"tag\":\"mate\",\"ridge\":536,\"a\":66,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":643,\"a\":46,\"owners\":[36]},{\"tag\":\"mate\",\"ridge\":644,\"a\":36,\"owners\":[83,85,86]},{\"tag\":\"mate\",\"ridge\":644,\"a\":59,\"owners\":[77,78,85]},{\"tag\":\"mate\",\"ridge\":644,\"a\":74,\"owners\":[55,85]},{\"tag\":\"mate\",\"ridge\":644,\"a\":78,\"owners\":[55,59,83,85]},{\"tag\":\"mate\",\"ridge\":644,\"a\":83,\"owners\":[36,77,78]},{\"tag\":\"mate\",\"ridge\":644,\"a\":86,\"owners\":[36,55,77,85]},{\"tag\":\"mate\",\"ridge\":178,\"a\":81,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":656,\"a\":46,\"owners\":[83,86]},{\"tag\":\"mate\",\"ridge\":656,\"a\":74,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":656,\"a\":82,\"owners\":[59,62,83]},{\"tag\":\"mate\",\"ridge\":92,\"a\":64,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":649,\"a\":55,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":649,\"a\":62,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":340,\"a\":72,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":596,\"a\":86,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":674,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":706,\"a\":82,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":680,\"a\":85,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[28,30,50,65,66],\"full_literals\":[-36,3,4,13,22,23]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-38,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-39,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":43,\"full_literals\":[-8,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":60,\"full_literals\":[-18,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":48,\"full_literals\":[-12,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":79,\"full_literals\":[-30,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":55,\"full_literals\":[-14,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":36,\"full_literals\":[-5,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":78,\"full_literals\":[-29,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":71,\"full_literals\":[-24,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":82,\"full_literals\":[-32,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":57,\"full_literals\":[-16,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":73,\"full_literals\":[-26,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-35,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":59,\"full_literals\":[-17,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":62,\"full_literals\":[-19,47]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-48,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-53,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-50,-55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":31,\"owners\":[7,16,28,38,42,44,45,48,56,57,60,63,64,71,72,73,79,81,82,86]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[36,46,55,59,62,74,77,78,82,83,85,86]}]}"
  "p cnf 56 69\n-33 -3 0\n-33 -4 0\n-33 -13 0\n-33 -22 0\n-1 21 24 25 26 30 31 32 0\n-3 30 31 32 0\n-6 24 25 26 31 32 0\n-7 21 24 25 26 32 0\n-9 21 25 26 30 0\n-10 21 24 26 30 31 32 0\n-2 24 31 32 35 0\n-15 31 32 0\n-20 24 32 35 0\n-23 19 0\n-11 5 0\n-5 33 34 35 0\n-17 28 29 34 0\n-27 14 34 0\n-29 14 17 33 34 0\n-33 5 28 29 0\n-35 5 14 28 34 0\n-31 8 0\n-11 33 35 0\n-27 19 0\n-32 17 19 33 0\n-21 12 0\n-14 19 0\n-19 14 0\n-25 16 0\n-35 26 0\n-28 0\n-32 29 0\n-34 0\n-36 3 4 13 22 23 0\n-37 36 0\n-38 37 0\n-39 38 0\n39 0\n-8 40 0\n-18 40 0\n-12 41 0\n-30 41 0\n-14 42 0\n-5 43 0\n-29 43 0\n-24 44 0\n-32 44 0\n-16 45 0\n-26 45 0\n-35 46 0\n-17 47 0\n-19 47 0\n-41 48 0\n-40 48 0\n-43 49 0\n-42 49 0\n-49 50 0\n-48 -49 51 0\n-45 52 0\n-44 52 0\n-47 53 0\n-46 53 0\n-53 54 0\n-52 -53 55 0\n-50 -55 56 0\n-51 -54 56 0\n-56 0\n1 2 3 6 7 9 10 12 15 16 18 20 21 24 25 26 30 31 32 35 0\n5 11 14 17 19 27 28 29 32 33 34 35 0\n"
  "70 38 0 38 37 0\n71 37 0 70 36 0\n72 36 0 71 35 0\n73 5 11 14 17 19 27 29 32 33 35 0 31 33 69 0\n74 49 0 33 31 55 56 44 45 43 15 17 32 20 18 28 21 73 0\n75 50 0 74 57 0\n76 -55 0 75 67 65 0\n77 52 48 0 54 39 22 53 41 26 40 42 59 60 48 49 46 47 29 30 7 11 5 10 13 8 12 6 9 68 0\n78 33 53 0 33 61 52 27 24 62 50 51 16 23 25 19 73 0\n79 53 0 72 61 52 14 78 1 2 3 4 34 0\n80 54 0 79 63 0\n81 -52 0 79 76 64 0\n82 -51 0 80 67 66 0\n83 48 0 81 77 0\n84 0 83 82 74 58 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f41f2d2aab1aa68e6558d64b86e8791e17ad13c6a9c66992e47939555354b51d52d1b61d1743db0ea3c4e9364e5354cd3c2e8b8ad2b2ac6b86d1b26c5b51cc749ca785d1725c5783c4f07d1c388664382e386913461946465454554342d0768330ca318e0b42c2b41c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6da6d269a4d26d24d249249a6da4924926d249a692449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 55), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 34), (facetIndex 36), (facetIndex 63), (facetIndex 65), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 41), (facetIndex 58), (facetIndex 68), (facetIndex 69)]))
 (.branch 4
 (.leaf ([(facetIndex 27), (facetIndex 60), (facetIndex 74), (facetIndex 77)]))
 (.leaf ([(facetIndex 46), (facetIndex 52), (facetIndex 54)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 30), (facetIndex 37), (facetIndex 61), (facetIndex 64)]))
 (.leaf ([(facetIndex 28), (facetIndex 56), (facetIndex 57), (facetIndex 59)])))
 (.branch 8
 (.leaf ([(facetIndex 29), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 47)]))
 (.branch 9
 (.leaf ([(facetIndex 35), (facetIndex 76)]))
 (.leaf ([(facetIndex 32), (facetIndex 40)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "100380300002200151053626604040000747777290051810905763z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 39), (facetIndex 67), (facetIndex 70)]))
 (.branch 2
 (.leaf ([(facetIndex 81), (facetIndex 83)]))
 (.leaf ([(facetIndex 62), (facetIndex 66)]))))
 (.branch 4
 (.leaf ([(facetIndex 85), (facetIndex 86)]))
 (.branch 5
 (.leaf ([(facetIndex 31), (facetIndex 33), (facetIndex 38), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 53)]))
 (.leaf ([(facetIndex 73), (facetIndex 75), (facetIndex 78), (facetIndex 79), (facetIndex 82), (facetIndex 84)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "dd348b40a280000800800000209200000001000208z17;"⟩
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
def grouped2_0010 : List Nat := [5, 6, 7, 8, 9]
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record006" 57

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record006" "{\"ridges\":[[6,522],[10,642],[18,536],[19,145],[19,208],[20,656],[29,522],[39,154],[41,536],[45,522],[46,522],[46,642],[47,522],[48,145],[51,402],[52,656],[54,642],[55,641],[55,642],[58,536],[63,208],[67,184],[68,536],[68,656],[69,536],[70,680],[71,145],[71,208],[72,656],[78,150],[81,154],[83,680],[84,594],[86,180]],\"owners\":[[6,522,[75,81,82,83],[29,41,45,46,47]],[29,522,[81,82,83],[6,41,45,46,47,75]],[45,522,[75,81,82],[6,29,41,46,47,83]],[46,522,[75,82],[6,29,41,45,47,81,83]],[47,522,[75,81,83],[6,29,41,45,46,82]],[55,641,[20,68,70],[10,46,54,72]],[10,642,[81,83,84],[46,52,54,55]],[46,642,[84],[10,52,54,55,81,83]],[54,642,[81,84],[10,46,52,55,83]],[55,642,[81,83],[10,46,52,54,84]],[18,536,[75,81,82],[41,58,68,69]],[41,536,[],[18,58,68,69,75,81,82]],[58,536,[81,82],[18,41,68,69,75]],[68,536,[75,82],[18,41,58,69,81]],[69,536,[75,81],[18,41,58,68,82]],[19,145,[20,31,39,51,52,62,67,68],[48,63,71]],[48,145,[20,62,67,68],[19,31,39,51,52,63,71]],[71,145,[20,31,39,51,52,68],[19,48,62,63,67]],[19,208,[78,84,86],[48,63,71,72]],[63,208,[84],[19,48,71,72,78,86]],[71,208,[78,84],[19,48,63,72,86]],[20,656,[81,84],[52,68,72]],[52,656,[],[20,68,72,81,84]],[68,656,[84],[20,52,72,81]],[72,656,[81],[20,52,68,84]],[78,150,[31],[]],[39,154,[81],[]],[81,154,[39],[]],[84,594,[50],[]],[51,402,[],[]],[86,180,[62],[]],[67,184,[],[]],[70,680,[83],[]],[83,680,[70],[]]],\"edges\":[[29,[6,18,29,41,45,46,47,58,68,69,70,75,81,82,83]],[32,[19,20,31,39,48,51,52,62,63,67,68,71,72,78,81,84,86]],[43,[10,20,46,52,54,55,68,70,72,81,83,84]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-17,-8],[-18,-7],[-18,-8],[-18,-13],[-19,-8],[-24,-8],[-26,-18],[-27,-8],[-30,-13],[-30,-29],[-33,-28],[-33,-31],[-1,28,30,31,32],[-6,30,31,32],[-10,28,30,31],[-11,28,31],[-12,28,30,32],[-18,5,23,25],[-2,30,32,33],[-11,33],[-17,30,33],[-18,30,32],[-3,28,30,31],[-9],[-19,30,31],[-23,28,31],[-24,28,30],[-4,5,7,8,15,16,20,22,23],[-13,5,20,22,23],[-26,5,7,8,15,16,23],[-4,29,33,34],[-21,33],[-26,29,33],[-5,30,33],[-16],[-23,33],[-27,30],[-29,7],[-8,30],[-30,8],[-33,14],[-15],[-34,20],[-22],[-25,32],[-32,25],[-35,13,18,26,27],[-13,35],[-26,35],[-36,9,19,23,24],[-37,11,16,17],[-38,35],[-39,37],[-40,36,39],[-41,38,40],[-42,41],[42],[-25,43],[-30,44],[-32,44],[-20,45],[-7,46],[-14,46],[-29,47],[-33,47],[-44,48],[-44,-45,49],[-48,50],[-43,50],[-43,-48,51],[-43,-49,52],[-47,53],[-46,53],[-46,-47,54],[-53,55],[-54,56],[-50,-56,57],[-51,-55,57],[-52,57],[-57],[1,3,6,9,10,11,12,19,23,24,25,28,30,31,32],[4,5,7,8,13,15,16,20,21,22,23,26,27,29,30,33,34],[2,5,11,16,17,18,23,25,27,30,32,33]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":54,\"b\":39},{\"tag\":\"incompatible\",\"a\":55,\"b\":31},{\"tag\":\"incompatible\",\"a\":55,\"b\":39},{\"tag\":\"incompatible\",\"a\":55,\"b\":48},{\"tag\":\"incompatible\",\"a\":58,\"b\":39},{\"tag\":\"incompatible\",\"a\":69,\"b\":39},{\"tag\":\"incompatible\",\"a\":71,\"b\":55},{\"tag\":\"incompatible\",\"a\":72,\"b\":39},{\"tag\":\"incompatible\",\"a\":81,\"b\":48},{\"tag\":\"incompatible\",\"a\":81,\"b\":78},{\"tag\":\"incompatible\",\"a\":84,\"b\":75},{\"tag\":\"incompatible\",\"a\":84,\"b\":82},{\"tag\":\"mate\",\"ridge\":522,\"a\":6,\"owners\":[75,81,82,83]},{\"tag\":\"mate\",\"ridge\":522,\"a\":29,\"owners\":[81,82,83]},{\"tag\":\"mate\",\"ridge\":522,\"a\":45,\"owners\":[75,81,82]},{\"tag\":\"mate\",\"ridge\":522,\"a\":46,\"owners\":[75,82]},{\"tag\":\"mate\",\"ridge\":522,\"a\":47,\"owners\":[75,81,83]},{\"tag\":\"mate\",\"ridge\":641,\"a\":55,\"owners\":[20,68,70]},{\"tag\":\"mate\",\"ridge\":642,\"a\":10,\"owners\":[81,83,84]},{\"tag\":\"mate\",\"ridge\":642,\"a\":46,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":642,\"a\":54,\"owners\":[81,84]},{\"tag\":\"mate\",\"ridge\":642,\"a\":55,\"owners\":[81,83]},{\"tag\":\"mate\",\"ridge\":536,\"a\":18,\"owners\":[75,81,82]},{\"tag\":\"mate\",\"ridge\":536,\"a\":41,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":536,\"a\":58,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":536,\"a\":68,\"owners\":[75,82]},{\"tag\":\"mate\",\"ridge\":536,\"a\":69,\"owners\":[75,81]},{\"tag\":\"mate\",\"ridge\":145,\"a\":19,\"owners\":[20,31,39,51,52,62,67,68]},{\"tag\":\"mate\",\"ridge\":145,\"a\":48,\"owners\":[20,62,67,68]},{\"tag\":\"mate\",\"ridge\":145,\"a\":71,\"owners\":[20,31,39,51,52,68]},{\"tag\":\"mate\",\"ridge\":208,\"a\":19,\"owners\":[78,84,86]},{\"tag\":\"mate\",\"ridge\":208,\"a\":63,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":208,\"a\":71,\"owners\":[78,84]},{\"tag\":\"mate\",\"ridge\":656,\"a\":20,\"owners\":[81,84]},{\"tag\":\"mate\",\"ridge\":656,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":656,\"a\":68,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":656,\"a\":72,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":150,\"a\":78,\"owners\":[31]},{\"tag\":\"mate\",\"ridge\":154,\"a\":39,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":154,\"a\":81,\"owners\":[39]},{\"tag\":\"mate\",\"ridge\":594,\"a\":84,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":402,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":180,\"a\":86,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":184,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":680,\"a\":70,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":680,\"a\":83,\"owners\":[70]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[48,55,71,72],\"full_literals\":[-35,13,18,26,27]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":48,\"full_literals\":[-13,35]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":71,\"full_literals\":[-26,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[41,58,68,69],\"full_literals\":[-36,9,19,23,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[46,52,54],\"full_literals\":[-37,11,16,17]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,35,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-39,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,36,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,38,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-42,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-25,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":81,\"full_literals\":[-30,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-32,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":62,\"full_literals\":[-20,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":31,\"full_literals\":[-7,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":50,\"full_literals\":[-14,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-29,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-33,47]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-45,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-48,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-43,-49,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-47,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-50,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[6,18,29,41,45,46,47,58,68,69,70,75,81,82,83]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[19,20,31,39,48,51,52,62,63,67,68,71,72,78,81,84,86]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[10,20,46,52,54,55,68,70,72,81,83,84]}]}"
  "p cnf 57 83\n-17 -8 0\n-18 -7 0\n-18 -8 0\n-18 -13 0\n-19 -8 0\n-24 -8 0\n-26 -18 0\n-27 -8 0\n-30 -13 0\n-30 -29 0\n-33 -28 0\n-33 -31 0\n-1 28 30 31 32 0\n-6 30 31 32 0\n-10 28 30 31 0\n-11 28 31 0\n-12 28 30 32 0\n-18 5 23 25 0\n-2 30 32 33 0\n-11 33 0\n-17 30 33 0\n-18 30 32 0\n-3 28 30 31 0\n-9 0\n-19 30 31 0\n-23 28 31 0\n-24 28 30 0\n-4 5 7 8 15 16 20 22 23 0\n-13 5 20 22 23 0\n-26 5 7 8 15 16 23 0\n-4 29 33 34 0\n-21 33 0\n-26 29 33 0\n-5 30 33 0\n-16 0\n-23 33 0\n-27 30 0\n-29 7 0\n-8 30 0\n-30 8 0\n-33 14 0\n-15 0\n-34 20 0\n-22 0\n-25 32 0\n-32 25 0\n-35 13 18 26 27 0\n-13 35 0\n-26 35 0\n-36 9 19 23 24 0\n-37 11 16 17 0\n-38 35 0\n-39 37 0\n-40 36 39 0\n-41 38 40 0\n-42 41 0\n42 0\n-25 43 0\n-30 44 0\n-32 44 0\n-20 45 0\n-7 46 0\n-14 46 0\n-29 47 0\n-33 47 0\n-44 48 0\n-44 -45 49 0\n-48 50 0\n-43 50 0\n-43 -48 51 0\n-43 -49 52 0\n-47 53 0\n-46 53 0\n-46 -47 54 0\n-53 55 0\n-54 56 0\n-50 -56 57 0\n-51 -55 57 0\n-52 57 0\n-57 0\n1 3 6 9 10 11 12 19 23 24 25 28 30 31 32 0\n4 5 7 8 13 15 16 20 21 22 23 26 27 29 30 33 34 0\n2 5 11 16 17 18 23 25 27 30 32 33 0\n"
  "84 -36 19 23 24 0 24 50 0\n85 -37 11 17 0 35 51 0\n86 41 0 57 56 0\n87 -52 0 80 79 0\n88 1 3 6 10 11 12 19 23 24 25 28 30 31 32 0 24 81 0\n89 4 5 7 8 13 20 21 23 26 27 29 30 33 34 0 42 35 44 82 0\n90 2 5 11 17 18 23 25 27 30 32 33 0 35 83 0\n91 33 50 0 68 66 59 60 22 37 69 58 20 36 21 19 34 90 0\n92 50 0 68 69 66 58 59 60 91 11 12 27 17 14 25 15 16 23 26 13 88 0\n93 -56 0 92 80 77 0\n94 -54 0 93 76 0\n95 -33 0 94 41 65 63 74 0\n96 -11 0 95 20 0\n97 -21 0 95 32 0\n98 -23 0 95 36 0\n99 32 18 30 0 95 98 96 34 21 37 45 19 90 0\n100 18 -35 30 0 95 87 80 44 98 35 42 34 39 37 99 46 60 58 66 71 70 67 78 61 75 29 73 47 62 30 0\n101 -18 30 0 87 44 35 42 98 97 95 34 39 37 2 4 7 18 22 38 58 60 71 67 61 43 28 89 0\n102 30 0 87 80 98 97 95 37 39 34 101 99 100 46 60 48 49 58 66 71 70 67 78 61 75 43 72 73 64 62 31 89 0\n103 -13 0 102 9 0\n104 -29 0 102 10 0\n105 8 0 102 40 0\n106 -26 0 104 95 33 0\n107 -17 0 105 1 0\n108 -18 0 105 3 0\n109 -19 0 105 5 0\n110 -24 0 105 6 0\n111 -27 0 105 8 0\n112 -35 0 106 108 111 103 47 0\n113 -37 0 107 96 85 0\n114 -36 0 110 98 109 84 0\n115 -38 0 112 52 0\n116 -39 0 113 53 0\n117 -40 0 114 116 54 0\n118 0 115 117 86 55 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record006
