module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00043Data
public import GraphInputsRow24Part00043Frames
public import GraphInputsRow24Part00043Leaves
public import GraphInputsRow24Part00043Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record042
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042
def vertexColumn : Fields := ⟨10, hexnat% "1b45b13c5aa9ab19c6699662d94e4b86e1783ef05b1e27495a69966539b15c569565655352d54d4b46d4745d0f6c370da358e932ce8b62d4b8ad2b1ae1b26c5ba1d8791d4731d2729c6715d0f13c2f07e4a0e8960da49525290e5855152525435a0e4324c3382c4b0ac1b21c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db4db69b69369a4924936d26da49a492492492493491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "46416209f43ee000000", hexnat% "80008800000000000000", 352530915655680, 4503633987108864, hexnat% "14000001400000000", 2305843009213693952]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5fa211437e4000000", hexnat% "84000000800002000000", 4574002731286528, hexnat% "600400000000000000", 12919261626368, 134217728]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "46406301f5eee000000", 352530915655680, hexnat% "80008800800000000000", hexnat% "15000000100000000", 2305843009213693952]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "465d62016510e000000", 2882303763664601088, hexnat% "80000000800020000000", 61203283968, 4583863976198144, 282162171478016]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "61c600161fec000000", 4035225266123964416, hexnat% "84000000800002000000", 4855580787212288, hexnat% "40020000000000000", 10720238370816]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5fa201417ec000000", hexnat% "84000000800002000000", hexnat% "600400000000000000", 4574140170240000, 283124244152320, 11269994184704]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41f611dfffae000000", hexnat% "240000000000000000", hexnat% "4000020000000000000", 1073741824, hexnat% "80000800000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "410211dfff2e000000", hexnat% "84000000000000000000", hexnat% "240000000000000000", 297237575406452736, 5764607524107976704, 12105675800519376896]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8420fe20827fee000000", hexnat% "10010000000000000", hexnat% "400000c0000000000", hexnat% "400000100000000000", 353492988329984]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "605e00127fee000000", hexnat% "1a000000000000000", hexnat% "84000000800000000000", hexnat% "40020040000000000", 353492988329984, 4512395720392704]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8404be30dfd5ee000000", 180388626432, 281474976710656, hexnat% "600000000000000000", hexnat% "14000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8400be208855ee000000", hexnat% "240000060000000000", hexnat% "14000000000000000", hexnat% "400000100000000000", 4503780015996928, 353492988329984]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "644a115fff4e000000", hexnat% "4000420000000000000", hexnat% "800000008000a0000000", hexnat% "1b000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8400be21827fee000000", 80814104641536, hexnat% "14000000000000000", hexnat% "600000100000000000", 4503599627370496, hexnat% "40000040000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "600e001255cc000000", hexnat% "84000000800002000000", 180925497344, hexnat% "40020040000000000", hexnat% "1f000000000000000", 80814104641536, 4785074604081152]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c18 c15
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c19 c14
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c21 c8
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c22 c5
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c23 c4
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c24 c3
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c25 c2
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c26 c1
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c27 c0
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record042

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f0ab29aac671aa6999962d94e1b89e17bc1ac669b15c5a9665654b55346d2745de0f43b0dc3a8e63a4d938ccb392d4b8ac6b26c5ba1e4731e2749ca719d1715d0f23c3c0e986518960d84e0b81e0e585514950d44d0b41da0d8390d4388c930cc4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6d36924936da6d2492492492492492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 66), (facetIndex 70)]))
 (.branch 2
 (.leaf ([(facetIndex 67), (facetIndex 71)]))
 (.leaf ([(facetIndex 69), (facetIndex 72)]))))
 (.branch 4
 (.leaf ([(facetIndex 79), (facetIndex 83)]))
 (.branch 5
 (.leaf ([(facetIndex 80), (facetIndex 84)]))
 (.leaf ([(facetIndex 82), (facetIndex 85)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2c7446000022102z32;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record000" 38

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record000" "{\"ridges\":[[11,546],[13,577],[15,642],[40,546],[42,577],[43,642],[47,546],[49,577],[51,545],[51,546],[53,641],[53,642],[54,546],[54,577],[55,545],[55,546],[55,642],[57,577],[57,642],[58,577],[59,642],[66,612],[67,676],[69,708],[70,616],[71,688],[72,960],[79,612],[82,708],[83,616],[85,960]],\"owners\":[[51,545,[66,67,70],[11,40,47,54,55,71]],[55,545,[66,70],[11,40,47,51,54,67,71]],[11,546,[79,80,83,84],[40,47,51,54,55]],[40,546,[83,84],[11,47,51,54,55,79,80]],[47,546,[79,80,84],[11,40,51,54,55,83]],[51,546,[79,80,83],[11,40,47,54,55,84]],[54,546,[80,84],[11,40,47,51,55,79,83]],[55,546,[79,83],[11,40,47,51,54,80,84]],[13,577,[66,69,70,72],[42,49,54,57,58]],[42,577,[70,72],[13,49,54,57,58,66,69]],[49,577,[66,69,72],[13,42,54,57,58,70]],[54,577,[69,72],[13,42,49,57,58,66,70]],[57,577,[66,70],[13,42,49,54,58,69,72]],[58,577,[66,69,70],[13,42,49,54,57,72]],[53,641,[67,69,72],[15,43,55,57,59,71]],[15,642,[80,82,84,85],[43,53,55,57,59]],[43,642,[84,85],[15,53,55,57,59,80,82]],[53,642,[80,82,85],[15,43,55,57,59,84]],[55,642,[82,85],[15,43,53,57,59,80,84]],[57,642,[80,84],[15,43,53,55,59,82,85]],[59,642,[80,82,84],[15,43,53,55,57,85]],[66,612,[79],[]],[79,612,[66],[]],[67,676,[80],[]],[69,708,[82],[]],[82,708,[69],[]],[70,616,[83],[]],[83,616,[70],[]],[71,688,[84],[]],[72,960,[85],[]],[85,960,[72],[]]],\"edges\":[[38,[11,40,47,51,54,55,66,67,70,71,79,80,83,84]],[41,[13,42,49,54,57,58,66,69,70,72,79,82,83,85]],[43,[15,43,53,55,57,59,67,69,71,72,80,82,84,85]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-16,-6],[-17,-16],[-23,-16],[-24,-4],[-24,-16],[-24,-17],[-24,-22],[-24,-23],[-9,16,17,19],[-12,16,19],[-1,22,23,25,26],[-4,25,26],[-7,22,23,26],[-9,22,23,25],[-11,23,26],[-12,22,25],[-2,16,18,19,21],[-5,19,21],[-8,16,18,21],[-11,18,21],[-13,16,19],[-14,16,18,19],[-10,17,18,21],[-3,23,24,26,27],[-6,26,27],[-10,23,24,27],[-12,24,27],[-13,23,26],[-15,23,24,26],[-16,22],[-22,16],[-17,23],[-18,24],[-24,18],[-19,25],[-25,19],[-20,26],[-21,27],[-27,21],[-16,28],[-19,28],[-18,29],[-21,29],[-22,30],[-25,30],[-23,31],[-26,31],[-24,32],[-27,32],[-29,33],[-33,34],[-28,34],[-32,35],[-31,35],[-31,-32,36],[-36,37],[-30,-35,37],[-34,-37,38],[-38],[1,4,7,9,11,12,16,17,19,20,22,23,25,26],[2,5,8,11,13,14,16,18,19,21,22,24,25,27],[3,6,10,12,13,15,17,18,20,21,23,24,26,27]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":66,\"b\":43},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":80,\"b\":66},{\"tag\":\"incompatible\",\"a\":82,\"b\":40},{\"tag\":\"incompatible\",\"a\":82,\"b\":66},{\"tag\":\"incompatible\",\"a\":82,\"b\":67},{\"tag\":\"incompatible\",\"a\":82,\"b\":79},{\"tag\":\"incompatible\",\"a\":82,\"b\":80},{\"tag\":\"mate\",\"ridge\":545,\"a\":51,\"owners\":[66,67,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":55,\"owners\":[66,70]},{\"tag\":\"mate\",\"ridge\":546,\"a\":11,\"owners\":[79,80,83,84]},{\"tag\":\"mate\",\"ridge\":546,\"a\":40,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":546,\"a\":47,\"owners\":[79,80,84]},{\"tag\":\"mate\",\"ridge\":546,\"a\":51,\"owners\":[79,80,83]},{\"tag\":\"mate\",\"ridge\":546,\"a\":54,\"owners\":[80,84]},{\"tag\":\"mate\",\"ridge\":546,\"a\":55,\"owners\":[79,83]},{\"tag\":\"mate\",\"ridge\":577,\"a\":13,\"owners\":[66,69,70,72]},{\"tag\":\"mate\",\"ridge\":577,\"a\":42,\"owners\":[70,72]},{\"tag\":\"mate\",\"ridge\":577,\"a\":49,\"owners\":[66,69,72]},{\"tag\":\"mate\",\"ridge\":577,\"a\":54,\"owners\":[69,72]},{\"tag\":\"mate\",\"ridge\":577,\"a\":57,\"owners\":[66,70]},{\"tag\":\"mate\",\"ridge\":577,\"a\":58,\"owners\":[66,69,70]},{\"tag\":\"mate\",\"ridge\":641,\"a\":53,\"owners\":[67,69,72]},{\"tag\":\"mate\",\"ridge\":642,\"a\":15,\"owners\":[80,82,84,85]},{\"tag\":\"mate\",\"ridge\":642,\"a\":43,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":642,\"a\":53,\"owners\":[80,82,85]},{\"tag\":\"mate\",\"ridge\":642,\"a\":55,\"owners\":[82,85]},{\"tag\":\"mate\",\"ridge\":642,\"a\":57,\"owners\":[80,84]},{\"tag\":\"mate\",\"ridge\":642,\"a\":59,\"owners\":[80,82,84]},{\"tag\":\"mate\",\"ridge\":612,\"a\":66,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":612,\"a\":79,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":676,\"a\":67,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":708,\"a\":69,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":708,\"a\":82,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":616,\"a\":70,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":616,\"a\":83,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":688,\"a\":71,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":960,\"a\":72,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":960,\"a\":85,\"owners\":[72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-16,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-19,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-18,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":72,\"full_literals\":[-21,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":79,\"full_literals\":[-22,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-25,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-23,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":84,\"full_literals\":[-26,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-24,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-27,32]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-32,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-30,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-34,-37,38],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[11,40,47,51,54,55,66,67,70,71,79,80,83,84]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[13,42,49,54,57,58,66,69,70,72,79,82,83,85]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[15,43,53,55,57,59,67,69,71,72,80,82,84,85]}]}"
  "p cnf 38 62\n-16 -6 0\n-17 -16 0\n-23 -16 0\n-24 -4 0\n-24 -16 0\n-24 -17 0\n-24 -22 0\n-24 -23 0\n-9 16 17 19 0\n-12 16 19 0\n-1 22 23 25 26 0\n-4 25 26 0\n-7 22 23 26 0\n-9 22 23 25 0\n-11 23 26 0\n-12 22 25 0\n-2 16 18 19 21 0\n-5 19 21 0\n-8 16 18 21 0\n-11 18 21 0\n-13 16 19 0\n-14 16 18 19 0\n-10 17 18 21 0\n-3 23 24 26 27 0\n-6 26 27 0\n-10 23 24 27 0\n-12 24 27 0\n-13 23 26 0\n-15 23 24 26 0\n-16 22 0\n-22 16 0\n-17 23 0\n-18 24 0\n-24 18 0\n-19 25 0\n-25 19 0\n-20 26 0\n-21 27 0\n-27 21 0\n-16 28 0\n-19 28 0\n-18 29 0\n-21 29 0\n-22 30 0\n-25 30 0\n-23 31 0\n-26 31 0\n-24 32 0\n-27 32 0\n-29 33 0\n-33 34 0\n-28 34 0\n-32 35 0\n-31 35 0\n-31 -32 36 0\n-36 37 0\n-30 -35 37 0\n-34 -37 38 0\n-38 0\n1 4 7 9 11 12 16 17 19 20 22 23 25 26 0\n2 5 8 11 13 14 16 18 19 21 22 24 25 27 0\n3 6 10 12 13 15 17 18 20 21 23 24 26 27 0\n"
  "63 16 21 18 19 0 17 19 21 31 18 36 20 34 22 39 61 0\n64 34 0 51 52 50 40 41 42 43 63 0\n65 -37 0 64 59 58 0\n66 -36 0 65 56 0\n67 24 19 27 0 65 38 27 33 63 1 2 3 30 23 44 57 54 47 37 24 28 29 62 0\n68 25 27 0 66 35 67 4 5 6 7 8 48 10 9 55 47 37 11 13 15 60 0\n69 27 0 65 38 68 45 57 53 54 48 46 47 27 33 26 32 25 37 24 28 29 62 0\n70 32 0 69 49 0\n71 35 0 70 53 0\n72 -31 0 70 66 55 0\n73 -30 0 71 65 57 0\n74 -23 0 72 46 0\n75 -26 0 72 47 0\n76 -22 0 73 44 0\n77 -25 0 73 45 0\n78 -17 0 74 32 0\n79 -9 0 74 76 77 14 0\n80 -20 0 75 37 0\n81 -4 0 75 77 12 0\n82 -1 0 75 74 77 76 11 0\n83 -7 0 75 74 76 13 0\n84 -11 0 75 74 15 0\n85 -12 0 76 77 16 0\n86 -16 0 76 30 0\n87 -19 0 77 35 0\n88 0 81 82 74 75 79 85 83 78 87 80 76 86 77 84 60 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1b45b15c4f1b2aaa9a2e9a659996559362da4e1b85e0fbc16c6a95a699565392e5a559595555352d64d5352d1b51d1743db0dc3a8da358e9364d534ccb3a2e2b2ac6b86c9b16c3b61e4751d2729c6745c9715c3783e4a1382e079a164649515254544d0b41da0e4328c9382c4b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db6db6924d36db69249a49249349a4da492492692492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 52), (facetIndex 74)]))
 (.leaf ([(facetIndex 67), (facetIndex 70), (facetIndex 72)])))
 (.branch 3
 (.leaf ([(facetIndex 85), (facetIndex 86), (facetIndex 87)]))
 (.branch 4
 (.leaf ([(facetIndex 68), (facetIndex 69), (facetIndex 71)]))
 (.leaf ([(facetIndex 89), (facetIndex 90), (facetIndex 91)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 35), (facetIndex 45), (facetIndex 61)]))
 (.leaf ([(facetIndex 79), (facetIndex 80), (facetIndex 82)])))
 (.branch 8
 (.leaf ([(facetIndex 84), (facetIndex 88), (facetIndex 92)]))
 (.branch 9
 (.leaf ([(facetIndex 46), (facetIndex 49)]))
 (.leaf ([(facetIndex 81), (facetIndex 83)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "7444722279696600000013133100000500000000000800850000000005z23;"⟩
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
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [5]
def grouped3_0009 : List Nat := [5, 6]
def grouped3_0010 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0011 : List Nat := [6]
def grouped3_0012 : List Nat := [7, 8, 9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record005" 41

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record005" "{\"ridges\":[[11,641],[11,642],[19,400],[20,416],[43,642],[47,400],[48,641],[48,642],[50,416],[51,641],[51,642],[52,450],[53,641],[53,642],[64,400],[66,416],[67,184],[70,664],[72,680],[73,400],[74,960],[84,390],[86,664],[87,680],[88,306],[92,180]],\"owners\":[[11,641,[70,72,74],[43,48,51,53]],[48,641,[72,74],[11,43,51,53,70]],[51,641,[70,74],[11,43,48,53,72]],[53,641,[70,72],[11,43,48,51,74]],[11,642,[86,87],[43,48,51,53]],[43,642,[],[11,48,51,53,86,87]],[48,642,[87],[11,43,51,53,86]],[51,642,[86],[11,43,48,53,87]],[53,642,[86,87],[11,43,48,51]],[19,400,[82,88,92],[47,64,73]],[47,400,[92],[19,64,73,82,88]],[64,400,[88],[19,47,73,82,92]],[73,400,[82],[19,47,64,88,92]],[20,416,[84,88,92],[50,66,73]],[50,416,[92],[20,66,73,84,88]],[66,416,[88],[20,50,73,84,92]],[84,390,[35,82],[]],[88,306,[45,80],[]],[52,450,[],[]],[92,180,[61,79],[]],[67,184,[85],[]],[70,664,[86],[]],[86,664,[70],[]],[72,680,[87],[]],[87,680,[72],[]],[74,960,[],[]]],\"edges\":[[42,[19,20,35,47,50,52,64,66,73,74,82,84,88,92]],[43,[11,43,48,51,53,70,72,74,86,87]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,17,18,20],[-8,18,20],[-10,17,20],[-12,17,18],[-1,26,27],[-5],[-8,27],[-10,26],[-12,26,27],[-2,23,28,29],[-7,29],[-14,28],[-19,23],[-3,24,28,29],[-9,29],[-15,28],[-24,4,23],[-28,6,22],[-11],[-29,13,21],[-16,25],[-17,26],[-26,17],[-18,27],[-27,18],[-20],[-30,11,20],[-31,16,17,18],[-17,31],[-18,31],[-25,32],[-26,32],[-27,32],[-4,33],[-6,33],[-13,33],[-21,34],[-22,34],[-23,34],[-35,30,31],[-31,35],[-32,36],[-37,35,36],[-36,37],[-35,37],[-35,-36,38],[-34,39],[-33,39],[-39,40],[-38,-40,41],[-41],[2,3,4,7,9,11,14,15,19,20,23,24,28,29],[1,5,8,10,12,17,18,20,26,27]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":641,\"a\":11,\"owners\":[70,72,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":48,\"owners\":[72,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":51,\"owners\":[70,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":53,\"owners\":[70,72]},{\"tag\":\"mate\",\"ridge\":642,\"a\":11,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":642,\"a\":43,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":642,\"a\":48,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":642,\"a\":51,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":642,\"a\":53,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":400,\"a\":19,\"owners\":[82,88,92]},{\"tag\":\"mate\",\"ridge\":400,\"a\":47,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":400,\"a\":64,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":400,\"a\":73,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":416,\"a\":20,\"owners\":[84,88,92]},{\"tag\":\"mate\",\"ridge\":416,\"a\":50,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":416,\"a\":66,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":390,\"a\":84,\"owners\":[35,82]},{\"tag\":\"mate\",\"ridge\":306,\"a\":88,\"owners\":[45,80]},{\"tag\":\"mate\",\"ridge\":450,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":180,\"a\":92,\"owners\":[61,79]},{\"tag\":\"mate\",\"ridge\":184,\"a\":67,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":664,\"a\":70,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":664,\"a\":86,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":680,\"a\":72,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":680,\"a\":87,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":960,\"a\":74,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[52,74],\"full_literals\":[-30,11,20]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[67,70,72],\"full_literals\":[-31,16,17,18]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":70,\"full_literals\":[-17,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":72,\"full_literals\":[-18,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":85,\"full_literals\":[-25,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":86,\"full_literals\":[-26,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":87,\"full_literals\":[-27,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":35,\"full_literals\":[-4,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":45,\"full_literals\":[-6,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":61,\"full_literals\":[-13,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":79,\"full_literals\":[-21,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-22,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-23,34]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-35,30,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-37,35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-35,-36,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-38,-40,41],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[19,20,35,47,50,52,64,66,73,74,82,84,88,92]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[11,43,48,51,53,70,72,74,86,87]}]}"
  "p cnf 41 53\n-1 17 18 20 0\n-8 18 20 0\n-10 17 20 0\n-12 17 18 0\n-1 26 27 0\n-5 0\n-8 27 0\n-10 26 0\n-12 26 27 0\n-2 23 28 29 0\n-7 29 0\n-14 28 0\n-19 23 0\n-3 24 28 29 0\n-9 29 0\n-15 28 0\n-24 4 23 0\n-28 6 22 0\n-11 0\n-29 13 21 0\n-16 25 0\n-17 26 0\n-26 17 0\n-18 27 0\n-27 18 0\n-20 0\n-30 11 20 0\n-31 16 17 18 0\n-17 31 0\n-18 31 0\n-25 32 0\n-26 32 0\n-27 32 0\n-4 33 0\n-6 33 0\n-13 33 0\n-21 34 0\n-22 34 0\n-23 34 0\n-35 30 31 0\n-31 35 0\n-32 36 0\n-37 35 36 0\n-36 37 0\n-35 37 0\n-35 -36 38 0\n-34 39 0\n-33 39 0\n-39 40 0\n-38 -40 41 0\n-41 0\n2 3 4 7 9 11 14 15 19 20 23 24 28 29 0\n1 5 8 10 12 17 18 20 26 27 0\n"
  "54 -30 0 19 26 27 0\n55 -35 31 0 54 40 0\n56 2 3 4 7 9 14 15 19 23 24 28 29 0 19 26 52 0\n57 1 8 10 12 17 18 26 27 0 6 26 53 0\n58 37 0 44 45 42 41 32 33 29 30 5 8 9 7 57 0\n59 39 0 47 48 37 38 39 34 35 36 13 17 18 20 14 12 16 10 11 15 56 0\n60 40 0 59 49 0\n61 -38 0 60 51 50 0\n62 36 0 58 42 43 31 32 33 55 21 22 24 28 0\n63 -35 0 62 61 46 0\n64 -31 0 63 41 0\n65 -17 0 64 29 0\n66 -18 0 64 30 0\n67 -1 0 65 66 26 1 0\n68 -10 0 65 26 3 0\n69 -12 0 65 66 4 0\n70 -26 0 65 23 0\n71 -8 0 66 26 2 0\n72 -27 0 66 25 0\n73 0 71 68 67 69 65 66 70 72 57 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record016
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5d1ac5713c6aa5a2e9a65987663a4e5392e2b85e0fbc15c789d25a9965594e4b969565555351d58d9354d4b4ad4745d0f6c370ea368d6394cb31cd8b92d4b4acab86c9b16c3b61e4751d2729c6783d0f23c4f0be8a15836079a1a258951525154354341da0e4328c530ce0b22c1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db69b6da4da69b6d24926934926934924da492692492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 71), (facetIndex 74)]))
 (.leaf ([(facetIndex 48), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 67), (facetIndex 68), (facetIndex 91)]))
 (.branch 4
 (.leaf ([(facetIndex 42), (facetIndex 59), (facetIndex 69), (facetIndex 89)]))
 (.leaf ([(facetIndex 79), (facetIndex 80), (facetIndex 86)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 41), (facetIndex 56), (facetIndex 66), (facetIndex 88)]))
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 85)])))
 (.branch 8
 (.leaf ([(facetIndex 35), (facetIndex 51), (facetIndex 83), (facetIndex 87)]))
 (.branch 9
 (.leaf ([(facetIndex 81), (facetIndex 90)]))
 (.leaf ([(facetIndex 84)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "283574697084466000100032250000003005000070010000035000007z23;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record016" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record016" 60

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record016" "{\"ridges\":[[9,162],[17,321],[18,392],[20,416],[31,162],[33,321],[40,162],[44,392],[46,162],[49,162],[49,416],[50,162],[51,450],[58,321],[60,392],[63,324],[64,321],[65,416],[70,416],[71,840],[72,392],[74,960],[81,390],[83,354],[84,390],[87,298],[90,172]],\"owners\":[[9,162,[77,84,85,87],[31,40,46,49,50]],[31,162,[85,87],[9,40,46,49,50,77,84]],[40,162,[84],[9,31,46,49,50,77,85,87]],[46,162,[77,84,87],[9,31,40,49,50,85]],[49,162,[77,85],[9,31,40,46,50,84,87]],[50,162,[77,84,85,87],[9,31,40,46,49]],[17,321,[42,48,51,68,71,73,74],[33,58,63,64]],[33,321,[68,71,73,74],[17,42,48,51,58,63,64]],[58,321,[48,51,73,74],[17,33,42,63,64,68,71]],[64,321,[42,51,68,71,74],[17,33,48,58,63,73]],[63,324,[79,83],[17,33,58,64,89,91]],[18,392,[81,87,90],[44,60,70,72]],[44,392,[90],[18,60,70,72,81,87]],[60,392,[87],[18,44,70,72,81,90]],[72,392,[81,87,90],[18,44,60,70]],[20,416,[84,87,90],[49,65,70]],[49,416,[90],[20,65,70,84,87]],[65,416,[87],[20,49,70,84,90]],[70,416,[84],[20,49,65,87,90]],[81,390,[35,84],[]],[84,390,[35,81],[]],[87,298,[41,78],[]],[83,354,[48],[]],[51,450,[],[]],[90,172,[56,77],[]],[71,840,[],[]],[74,960,[],[]]],\"edges\":[[36,[9,20,31,40,46,49,50,56,65,66,70,77,84,85,87,90]],[40,[17,33,42,48,51,58,63,64,68,71,73,74,79,83,89,91]],[42,[18,20,35,44,49,51,60,65,70,72,74,81,84,87,90]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record016" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record016\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,30,35,36,37],[-5,36,37],[-8,35],[-12,30,35,37],[-14,30,36],[-15,30,35,36,37],[-2,10,13,16,24,26,28,29],[-6,24,26,28,29],[-18,13,16,28,29],[-21,10,16,24,26,29],[-20,32,34],[-3,33,37,39],[-11,39],[-19,37],[-27,33,37,39],[-4,35,37,39],[-14,39],[-22,37],[-25,35],[-33,7,35],[-35,7,33],[-37,9,31],[-34,13],[-16],[-39,17,30],[-26],[-29],[-13,41],[-28,41],[-24,42],[-40,42],[-10,43],[-38,43],[-32,44],[-9,45],[-17,45],[-23,45],[-30,46],[-31,46],[-36,46],[-7,47],[-37,47],[-48,33,39],[-33,48],[-39,48],[-49,35],[-35,49],[-41,50],[-44,51],[-43,51],[-51,52],[-42,52],[-52,53],[-50,53],[-46,54],[-45,54],[-55,48,49],[-49,55],[-48,55],[-48,-49,56],[-55,57],[-56,58],[-47,57],[-47,-55,58],[-58,59],[-54,-57,59],[-53,-59,60],[-60],[1,4,5,8,12,14,15,17,22,23,25,30,35,36,37,39],[2,6,10,13,16,18,20,21,24,26,28,29,32,34,38,40],[3,4,7,11,14,16,19,22,25,27,29,33,35,37,39]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":162,\"a\":9,\"owners\":[77,84,85,87]},{\"tag\":\"mate\",\"ridge\":162,\"a\":31,\"owners\":[85,87]},{\"tag\":\"mate\",\"ridge\":162,\"a\":40,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":162,\"a\":46,\"owners\":[77,84,87]},{\"tag\":\"mate\",\"ridge\":162,\"a\":49,\"owners\":[77,85]},{\"tag\":\"mate\",\"ridge\":162,\"a\":50,\"owners\":[77,84,85,87]},{\"tag\":\"mate\",\"ridge\":321,\"a\":17,\"owners\":[42,48,51,68,71,73,74]},{\"tag\":\"mate\",\"ridge\":321,\"a\":33,\"owners\":[68,71,73,74]},{\"tag\":\"mate\",\"ridge\":321,\"a\":58,\"owners\":[48,51,73,74]},{\"tag\":\"mate\",\"ridge\":321,\"a\":64,\"owners\":[42,51,68,71,74]},{\"tag\":\"mate\",\"ridge\":324,\"a\":63,\"owners\":[79,83]},{\"tag\":\"mate\",\"ridge\":392,\"a\":18,\"owners\":[81,87,90]},{\"tag\":\"mate\",\"ridge\":392,\"a\":44,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":392,\"a\":60,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":392,\"a\":72,\"owners\":[81,87,90]},{\"tag\":\"mate\",\"ridge\":416,\"a\":20,\"owners\":[84,87,90]},{\"tag\":\"mate\",\"ridge\":416,\"a\":49,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":416,\"a\":65,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":416,\"a\":70,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":390,\"a\":81,\"owners\":[35,84]},{\"tag\":\"mate\",\"ridge\":390,\"a\":84,\"owners\":[35,81]},{\"tag\":\"mate\",\"ridge\":298,\"a\":87,\"owners\":[41,78]},{\"tag\":\"mate\",\"ridge\":354,\"a\":83,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":450,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":172,\"a\":90,\"owners\":[56,77]},{\"tag\":\"mate\",\"ridge\":840,\"a\":71,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":960,\"a\":74,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":48,\"full_literals\":[-13,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-28,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":68,\"full_literals\":[-24,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":91,\"full_literals\":[-40,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":42,\"full_literals\":[-10,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-38,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":79,\"full_literals\":[-32,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":41,\"full_literals\":[-9,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":56,\"full_literals\":[-17,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":66,\"full_literals\":[-23,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":77,\"full_literals\":[-30,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":78,\"full_literals\":[-31,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":85,\"full_literals\":[-36,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":35,\"full_literals\":[-7,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":87,\"full_literals\":[-37,47]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[81,90],\"full_literals\":[-48,33,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":81,\"full_literals\":[-33,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":90,\"full_literals\":[-39,48]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[84],\"full_literals\":[-49,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":84,\"full_literals\":[-35,49]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-48,-49,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-56,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-55,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-58,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-53,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":36,\"owners\":[9,20,31,40,46,49,50,56,65,66,70,77,84,85,87,90]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[17,33,42,48,51,58,63,64,68,71,73,74,79,83,89,91]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[18,20,35,44,49,51,60,65,70,72,74,81,84,87,90]}]}"
  "p cnf 60 71\n-1 30 35 36 37 0\n-5 36 37 0\n-8 35 0\n-12 30 35 37 0\n-14 30 36 0\n-15 30 35 36 37 0\n-2 10 13 16 24 26 28 29 0\n-6 24 26 28 29 0\n-18 13 16 28 29 0\n-21 10 16 24 26 29 0\n-20 32 34 0\n-3 33 37 39 0\n-11 39 0\n-19 37 0\n-27 33 37 39 0\n-4 35 37 39 0\n-14 39 0\n-22 37 0\n-25 35 0\n-33 7 35 0\n-35 7 33 0\n-37 9 31 0\n-34 13 0\n-16 0\n-39 17 30 0\n-26 0\n-29 0\n-13 41 0\n-28 41 0\n-24 42 0\n-40 42 0\n-10 43 0\n-38 43 0\n-32 44 0\n-9 45 0\n-17 45 0\n-23 45 0\n-30 46 0\n-31 46 0\n-36 46 0\n-7 47 0\n-37 47 0\n-48 33 39 0\n-33 48 0\n-39 48 0\n-49 35 0\n-35 49 0\n-41 50 0\n-44 51 0\n-43 51 0\n-51 52 0\n-42 52 0\n-52 53 0\n-50 53 0\n-46 54 0\n-45 54 0\n-55 48 49 0\n-49 55 0\n-48 55 0\n-48 -49 56 0\n-55 57 0\n-56 58 0\n-47 57 0\n-47 -55 58 0\n-58 59 0\n-54 -57 59 0\n-53 -59 60 0\n-60 0\n1 4 5 8 12 14 15 17 22 23 25 30 35 36 37 39 0\n2 6 10 13 16 18 20 21 24 26 28 29 32 34 38 40 0\n3 4 7 11 14 16 19 22 25 27 29 33 35 37 39 0\n"
  "72 2 6 10 13 18 20 21 24 28 32 34 38 40 0 24 26 27 70 0\n73 3 4 7 11 14 19 22 25 27 33 35 37 39 0 24 27 71 0\n74 53 0 27 26 24 53 54 51 52 48 49 50 30 31 28 29 34 32 33 8 10 23 9 7 11 72 0\n75 -59 0 74 68 67 0\n76 -58 0 75 65 0\n77 -56 0 76 62 0\n78 -49 7 0 77 46 60 21 44 0\n79 -55 39 0 76 64 41 78 47 57 20 43 0\n80 54 0 55 56 38 39 40 35 36 37 5 22 25 18 2 79 58 47 3 16 19 4 1 6 69 0\n81 -57 0 80 75 66 0\n82 -55 0 81 61 0\n83 -47 0 81 63 0\n84 -49 0 82 58 0\n85 -48 0 82 59 0\n86 -7 0 83 41 0\n87 -37 0 83 42 0\n88 -35 0 84 47 0\n89 -33 0 85 44 0\n90 -39 0 85 45 0\n91 -19 0 87 14 0\n92 -22 0 87 18 0\n93 -4 0 88 87 90 16 0\n94 -25 0 88 19 0\n95 -3 0 89 87 90 12 0\n96 -27 0 89 87 90 15 0\n97 -11 0 90 13 0\n98 -14 0 90 17 0\n99 0 93 94 86 95 98 91 92 97 96 89 88 87 90 73 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record016
