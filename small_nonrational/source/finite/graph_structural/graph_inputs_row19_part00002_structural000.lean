module
prelude
public import FacetCliqueRaw
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00002Data
public import GraphInputsRow19Part00002Frames
public import GraphInputsRow19Part00002Leaves
public import GraphInputsRow19Part00002Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00002.record057
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057
def vertexColumn : Fields := ⟨10, hexnat% "3c2cc95aa99563386e17bc1cc559a95553346d17783d0ec370f23a8f1354e334cd4b32e2b1ad1b16e8751e2729c6745c9715c8f0f03a318361382e07839314351342d07703a0d4330e2344c3312c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db4936db492492492492492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4638707615923175424, 45035996273704960, 11529215046068469760]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9006990948827136, 2314850346712694784, 4629700416936869888, 69793218560, 9259400833873739776]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [13897994098440142848, 114351356772352, 2314850208468434944]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9002800939794432, 4398046511104, 63050394783186944, 16140901064495857664]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8896801146929152, 4629700416936869888, 9259400868233478144, 110226040684544, 2314850345907388416]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8566268785328128, 63050395051622400, 16140901064495857664, 440921342607360, 8589934592]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9003191244947456, 1670742278144, 63050394783186944, 16140901064495857664, 2336999079936]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8971600149872640, 4629700416936869888, 35598836432896, 45035996273704960, 11529215046068469760]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8990843750842368, 9208409882624, 63050394783186944, 16140901064495857664, 7146825580544]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9007198986305536, 63050394783186944, 16140901064495857664]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4080287382241280, 4926911604064256, 2314850208468434944, 54043195528445952, 13835058055282163712]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [7829718938157056, 4629700971256086528, 9072581541888, 2314885530279477248, 1132531336347648, 9259400833873739776]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c19 c8
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c20 c7
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c21 c2
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00002.record057

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00002.record033
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "7cd8ad21eb861d92e1b89e1783ed86d11e7851d52d1b49d1743de0f43b0f2398d63a4e5334c7392d2b26c3bc1e8761ca719d1715c3743c8f13c6a169262582e07869165252542d07703a0e4348c6324c5312c2b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36d369249b4da492492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 39), (facetIndex 54), (facetIndex 64)]))
 (.branch 2
 (.leaf ([(facetIndex 29), (facetIndex 33), (facetIndex 34), (facetIndex 40), (facetIndex 56), (facetIndex 66)]))
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 45), (facetIndex 51)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 27), (facetIndex 38), (facetIndex 42), (facetIndex 52), (facetIndex 59), (facetIndex 62), (facetIndex 69)]))
 (.leaf ([(facetIndex 53), (facetIndex 55), (facetIndex 63), (facetIndex 65)])))
 (.branch 6
 (.leaf ([(facetIndex 41), (facetIndex 43), (facetIndex 44), (facetIndex 47), (facetIndex 49)]))
 (.leaf ([(facetIndex 37), (facetIndex 46), (facetIndex 48), (facetIndex 50)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "180608c06018235aeb95ae90f24480086z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 57)]))
 (.leaf ([(facetIndex 58)])))
 (.branch 3
 (.leaf ([(facetIndex 60)]))
 (.leaf ([(facetIndex 61)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 67)]))
 (.leaf ([(facetIndex 68)])))
 (.branch 7
 (.leaf ([(facetIndex 70)]))
 (.branch 8
 (.leaf ([(facetIndex 71)]))
 (.leaf ([(facetIndex 72)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "876054000003201z3a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

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
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0015 : List Nat := [0, 1, 2, 3]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [2, 3]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0022 : List Nat := [5]
def grouped3_0023 : List Nat := [6]
def grouped3_0024 : List Nat := [6, 7, 8]
def grouped3_0025 : List Nat := [7]
def grouped3_0026 : List Nat := [7, 8]
def grouped3_0027 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00002.record033" "{\"atoms\":[{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00002.record033" 50

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00002.record033" "{\"ridges\":[[41,515],[41,578],[45,515],[47,577],[48,515],[57,116],[58,900],[70,578],[71,578]],\"owners\":[[47,577,[60],[12,41,44,49,50,61]],[57,116,[67,72],[]],[58,900,[68],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00002.record033" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00002.record033\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-7,-5],[-7,-6],[-8,-4],[-11,-7],[-12,-7],[-18,-7],[-21,-14],[-21,-15],[-21,-19],[-21,-20],[-22,-1],[-22,-2],[-22,-3],[-22,-13],[-23,-5],[-23,-6],[-23,-11],[-24,-9],[-25,-14],[-25,-15],[-25,-19],[-25,-20],[-4,-7,-10],[-9,18],[-4,-23,-24],[-16,21,25],[-17,22],[-26,1,2,7,13],[-27,14,15,19,20],[-28,4,5,6,9,11],[-29,3,8,10,12],[-30,26],[-31,30],[-32,27],[-33,28],[-33,29],[-34,32],[-34,33],[-35,31],[-35,34],[35],[-36,16],[-37,17],[-38,21],[-39,22],[-40,23],[-41,24],[-42,25],[-43,36,37],[-44,43],[-45,38,39],[-46,41,42],[-47,42],[-48,40,47],[-48,46],[-49,45,48],[-50,44,49],[50]],\"atoms\":[{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":45,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":41},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":45},{\"tag\":\"incompatible\",\"a\":60,\"b\":45},{\"tag\":\"incompatible\",\"a\":67,\"b\":53},{\"tag\":\"incompatible\",\"a\":67,\"b\":55},{\"tag\":\"incompatible\",\"a\":67,\"b\":63},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":35},{\"tag\":\"incompatible\",\"a\":68,\"b\":36},{\"tag\":\"incompatible\",\"a\":68,\"b\":37},{\"tag\":\"incompatible\",\"a\":68,\"b\":51},{\"tag\":\"incompatible\",\"a\":70,\"b\":43},{\"tag\":\"incompatible\",\"a\":70,\"b\":44},{\"tag\":\"incompatible\",\"a\":70,\"b\":49},{\"tag\":\"incompatible\",\"a\":71,\"b\":47},{\"tag\":\"incompatible\",\"a\":72,\"b\":53},{\"tag\":\"incompatible\",\"a\":72,\"b\":55},{\"tag\":\"incompatible\",\"a\":72,\"b\":63},{\"tag\":\"incompatible\",\"a\":72,\"b\":65},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[41,45,48]},{\"tag\":\"mate\",\"ridge\":577,\"a\":47,\"owners\":[60]},{\"tag\":\"three\",\"ridge\":578,\"vertices\":[41,70,71]},{\"tag\":\"mate\",\"ridge\":116,\"a\":57,\"owners\":[67,72]},{\"tag\":\"mate\",\"ridge\":900,\"a\":58,\"owners\":[68]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[35,36,45,51],\"full_literals\":[-26,1,2,7,13]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[53,55,63,65],\"full_literals\":[-27,14,15,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[41,43,44,47,49],\"full_literals\":[-28,4,5,6,9,11]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[37,46,48,50],\"full_literals\":[-29,3,8,10,12]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-30,false,26],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-31,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-32,false,27],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-33,28,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-33,false,29],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-34,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-34,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-35,31,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-35,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[57],\"full_literals\":[-36,16]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[58],\"full_literals\":[-37,17]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[67],\"full_literals\":[-38,21]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[68],\"full_literals\":[-39,22]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[70],\"full_literals\":[-40,23]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[71],\"full_literals\":[-41,24]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[72],\"full_literals\":[-42,25]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-44,43,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,40,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,45,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,44,49],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true}]}"
  "p cnf 50 58\n-7 -5 0\n-7 -6 0\n-8 -4 0\n-11 -7 0\n-12 -7 0\n-18 -7 0\n-21 -14 0\n-21 -15 0\n-21 -19 0\n-21 -20 0\n-22 -1 0\n-22 -2 0\n-22 -3 0\n-22 -13 0\n-23 -5 0\n-23 -6 0\n-23 -11 0\n-24 -9 0\n-25 -14 0\n-25 -15 0\n-25 -19 0\n-25 -20 0\n-4 -7 -10 0\n-9 18 0\n-4 -23 -24 0\n-16 21 25 0\n-17 22 0\n-26 1 2 7 13 0\n-27 14 15 19 20 0\n-28 4 5 6 9 11 0\n-29 3 8 10 12 0\n-30 26 0\n-31 30 0\n-32 27 0\n-33 28 0\n-33 29 0\n-34 32 0\n-34 33 0\n-35 31 0\n-35 34 0\n35 0\n-36 16 0\n-37 17 0\n-38 21 0\n-39 22 0\n-40 23 0\n-41 24 0\n-42 25 0\n-43 36 37 0\n-44 43 0\n-45 38 39 0\n-46 41 42 0\n-47 42 0\n-48 40 47 0\n-48 46 0\n-49 45 48 0\n-50 44 49 0\n50 0\n"
  "59 31 0 41 39 0\n60 34 0 41 40 0\n61 30 0 59 33 0\n62 32 0 60 37 0\n63 33 0 60 38 0\n64 26 0 61 32 0\n65 27 0 62 34 0\n66 28 0 63 35 0\n67 29 0 63 36 0\n68 -25 0 65 19 20 21 22 29 0\n69 -42 0 68 48 0\n70 -47 0 69 53 0\n71 -48 0 70 69 66 55 54 52 46 47 15 16 17 18 25 30 0\n72 -21 0 65 7 8 9 10 29 0\n73 -16 0 72 68 26 0\n74 -38 0 72 44 0\n75 -36 0 73 42 0\n76 -22 0 64 66 67 11 12 13 14 28 1 2 4 5 6 24 30 3 23 31 0\n77 -17 0 76 27 0\n78 -39 0 76 45 0\n79 -37 0 77 43 0\n80 -45 0 78 74 51 0\n81 -43 0 79 75 49 0\n82 -49 0 80 71 56 0\n83 -44 0 81 50 0\n84 0 83 82 58 57 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record033_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00002.record033
