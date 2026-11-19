module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00012Data
public import GraphInputsRow24Part00012Frames
public import GraphInputsRow24Part00012Leaves
public import GraphInputsRow24Part00012Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00012.record070
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070
def vertexColumn : Fields := ⟨10, hexnat% "e61743713c1f392b4b8a3ab1aa699a36966c5956358ce1b91e2785eb44e9c6699365391e715355351d4cd4b46d4749d1743db0f2338f13a4e5334f0ba2ccb4acab1ae1b46c9b16f0731d2785d1725c5743c8f13c1f4b11c4a9261990e0ba9134499194550b41da0cc318c8b0ac4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b69b6db6da6db49b4da4db4d34924934d34d249369b49b692489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10808a7c012044c00000", hexnat% "4000400080000002000000", 714684705538048, 824650498048, hexnat% "90000200400000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [585058815251054592, hexnat% "10800000000040000000", hexnat% "4000000200000000000000", hexnat% "4000a0000000000000", hexnat% "98000200000000000", 18014398509481984]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10c982ce2b2445c00000", 140739635838976, 580964351930793984, hexnat% "4000000020000002000000", 824633720832]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "108082cc212045c00000", 9007749044109312, hexnat% "4000400000000000000000", 714684705538048, hexnat% "90810000000000000", 292057776128]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1080824c8160c7c00000", 45036546029518848, hexnat% "4000400000000000000000", hexnat% "90810000000000000", 609146621657088]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10800048000041800000", hexnat% "4000000204000000000000", 962072674304, 149535795970048, hexnat% "98810000000000000", 601450040262656, hexnat% "4000a0000002400000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00012.record070

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00012.record068
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "a713c1f392b4b2ac6a9a39a9635a8e4b86e8791e2785ee4571c66994e479395351d52d1b51d2745d0f78358ce3c4e9364d5334f0ba2c6b86d1b26c5b49ca745c9715d0f23c4f07f183530a4a8c61982e34529464c5194951542d074c348c6342c2b21c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6da4d34d26db6d34d349249349b6d269a6d2692491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 38), (facetIndex 46), (facetIndex 47)]))
 (.leaf ([(facetIndex 36), (facetIndex 52), (facetIndex 59), (facetIndex 61)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 40), (facetIndex 69), (facetIndex 76)]))
 (.leaf ([(facetIndex 26), (facetIndex 68), (facetIndex 73)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 41), (facetIndex 57), (facetIndex 71)]))
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 55)])))
 (.branch 7
 (.leaf ([(facetIndex 25), (facetIndex 53), (facetIndex 54)]))
 (.branch 8
 (.leaf ([(facetIndex 27)]))
 (.leaf ([(facetIndex 75)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "2803040230000001010405661555000000042000100000442736z19;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 56), (facetIndex 58), (facetIndex 62)]))
 (.leaf ([(facetIndex 79), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 37), (facetIndex 39), (facetIndex 48)]))
 (.leaf ([(facetIndex 44), (facetIndex 60), (facetIndex 63)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 35), (facetIndex 67), (facetIndex 70)]))
 (.leaf ([(facetIndex 65), (facetIndex 72), (facetIndex 81)])))
 (.branch 7
 (.leaf ([(facetIndex 31), (facetIndex 34), (facetIndex 42), (facetIndex 43), (facetIndex 45), (facetIndex 74), (facetIndex 77)]))
 (.leaf ([(facetIndex 64), (facetIndex 66), (facetIndex 78)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "293f01851009ef603000000002033d80410980cz17;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4, 5]
def grouped2_0003 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0004 : List Nat := [6]
def grouped2_0005 : List Nat := [6, 7, 8]
def grouped2_0006 : List Nat := [7]
def grouped2_0007 : List Nat := [7, 8]
def grouped2_0008 : List Nat := [8]
def grouped3_0009 : List Nat := [0, 1]
def grouped3_0010 : List Nat := [0, 1, 2, 3]
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00012.record068" "{\"atoms\":[{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00012.record068" 34

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00012.record068" "{\"ridges\":[[35,154],[44,656],[48,642],[63,656],[65,154],[67,534],[70,652],[72,534],[72,656],[74,154],[74,656],[75,770],[75,784],[77,594],[78,642],[81,652]],\"owners\":[[75,770,[48],[22,40,45,76,78]],[75,784,[63],[24,45,61,78]],[35,154,[65,74],[]],[65,154,[35,74],[]],[74,154,[35,65],[]],[48,642,[70,72,74,77],[39,44,78]],[78,642,[39,70],[44,48,72,74,77]],[44,656,[81],[60,63,72,74,77,78]],[63,656,[72,74,77,81],[44,60,78]],[72,656,[60,63],[44,74,77,78,81]],[74,656,[63],[44,60,72,77,78,81]],[67,534,[72],[]],[72,534,[67],[]],[70,652,[81],[]],[81,652,[70],[]],[77,594,[],[]]],\"edges\":[[43,[39,44,48,60,63,70,72,74,77,78,81]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00012.record068" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00012.record068\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-3,-1],[-6,-1],[-10,-1],[-16,-1],[-13,5],[-13,7],[-2,8,12],[-8,2,12],[-12,2,8],[-5,10,11,12,14],[-15,3,10],[-4,16],[-7,11,12,14,16],[-11,6,7],[-12,7],[-9,11],[-11,9],[-10,16],[-16,10],[-14],[-17,1],[-18,13],[-19,17,18],[-20,19],[-21,20],[-22,21],[22],[-3,23],[-5,23],[-4,24],[-6,24],[-7,24],[-25,2,9,10],[-2,25],[-9,25],[-10,25],[-26,8,11,16],[-8,26],[-11,26],[-16,26],[-12,27],[-24,28],[-23,28],[-28,29],[-30,25,26],[-26,30],[-25,30],[-25,-26,31],[-27,32],[-30,-32,33],[-31,33],[-29,-33,34],[-34],[3,4,5,6,7,10,11,12,14,15,16]],\"atoms\":[{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":39,\"b\":27},{\"tag\":\"incompatible\",\"a\":60,\"b\":27},{\"tag\":\"incompatible\",\"a\":70,\"b\":27},{\"tag\":\"incompatible\",\"a\":81,\"b\":27},{\"tag\":\"mate\",\"ridge\":770,\"a\":75,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":784,\"a\":75,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":154,\"a\":35,\"owners\":[65,74]},{\"tag\":\"mate\",\"ridge\":154,\"a\":65,\"owners\":[35,74]},{\"tag\":\"mate\",\"ridge\":154,\"a\":74,\"owners\":[35,65]},{\"tag\":\"mate\",\"ridge\":642,\"a\":48,\"owners\":[70,72,74,77]},{\"tag\":\"mate\",\"ridge\":642,\"a\":78,\"owners\":[39,70]},{\"tag\":\"mate\",\"ridge\":656,\"a\":44,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":656,\"a\":63,\"owners\":[72,74,77,81]},{\"tag\":\"mate\",\"ridge\":656,\"a\":72,\"owners\":[60,63]},{\"tag\":\"mate\",\"ridge\":656,\"a\":74,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":534,\"a\":67,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":534,\"a\":72,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":652,\"a\":70,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":652,\"a\":81,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":594,\"a\":77,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[27],\"full_literals\":[-17,1]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[75],\"full_literals\":[-18,13]},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-19,17,18],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0005\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-20,false,19],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-21,false,20],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-22,false,21],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":39,\"full_literals\":[-3,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":48,\"full_literals\":[-5,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":44,\"full_literals\":[-4,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":60,\"full_literals\":[-6,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":63,\"full_literals\":[-7,24]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[35,67,70],\"full_literals\":[-25,2,9,10]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":35,\"full_literals\":[-2,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":67,\"full_literals\":[-9,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-10,25]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[65,72,81],\"full_literals\":[-26,8,11,16]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":65,\"full_literals\":[-8,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":72,\"full_literals\":[-11,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-16,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":74,\"full_literals\":[-12,27]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-23,false,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-30,25,26],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-26,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-30,-32,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-29,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":43,\"owners\":[39,44,48,60,63,70,72,74,77,78,81]}]}"
  "p cnf 34 54\n-3 -1 0\n-6 -1 0\n-10 -1 0\n-16 -1 0\n-13 5 0\n-13 7 0\n-2 8 12 0\n-8 2 12 0\n-12 2 8 0\n-5 10 11 12 14 0\n-15 3 10 0\n-4 16 0\n-7 11 12 14 16 0\n-11 6 7 0\n-12 7 0\n-9 11 0\n-11 9 0\n-10 16 0\n-16 10 0\n-14 0\n-17 1 0\n-18 13 0\n-19 17 18 0\n-20 19 0\n-21 20 0\n-22 21 0\n22 0\n-3 23 0\n-5 23 0\n-4 24 0\n-6 24 0\n-7 24 0\n-25 2 9 10 0\n-2 25 0\n-9 25 0\n-10 25 0\n-26 8 11 16 0\n-8 26 0\n-11 26 0\n-16 26 0\n-12 27 0\n-24 28 0\n-23 28 0\n-28 29 0\n-30 25 26 0\n-26 30 0\n-25 30 0\n-25 -26 31 0\n-27 32 0\n-30 -32 33 0\n-31 33 0\n-29 -33 34 0\n-34 0\n3 4 5 6 7 10 11 12 14 15 16 0\n"
  "55 21 0 27 26 0\n56 20 0 55 25 0\n57 19 0 56 24 0\n58 3 4 5 6 7 10 11 12 15 16 0 20 54 0\n59 28 0 57 42 43 30 31 32 28 29 14 6 15 22 23 21 3 4 11 58 0\n60 29 0 59 44 0\n61 -33 0 60 53 52 0\n62 -31 0 61 51 0\n63 30 0 20 57 46 47 38 39 40 34 36 12 9 10 13 5 22 23 21 1 2 11 58 0\n64 -32 0 63 61 50 0\n65 -27 0 64 49 0\n66 -12 0 65 41 0\n67 26 0 63 66 38 39 40 45 7 16 18 33 0\n68 -25 0 67 62 48 0\n69 -2 0 68 34 0\n70 -9 0 68 35 0\n71 -10 0 68 36 0\n72 -8 0 69 66 8 0\n73 -11 0 70 17 0\n74 -16 0 71 19 0\n75 0 74 72 73 67 37 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00012.record068
