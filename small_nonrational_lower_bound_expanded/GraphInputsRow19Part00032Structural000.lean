module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow19Part00032Data
public import GraphInputsRow19Part00032Frames
public import GraphInputsRow19Part00032Leaves
public import GraphInputsRow19Part00032Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00032.record035
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨16, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 2456721293312, 4504149383184384, 20125460834811904]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 3), 1126037345796096, 2392829359816704, 2302102470656, 18858823439613952]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 240518168576, 274877906944, 549755813888]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 2370821947392, 274877906944, 549755813888]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 1126037345796096, 2252074691592192, 4785074604081152, 2851858284544]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 4504149383184384, 48395691491328, 576531121047601152, 396457504696958976]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), 900719925474099200, 2422361554944, 70918499991552, 39857296506880]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2796043444486144, (certNat% 9), 972777519512027136, 23080948091322368]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 70920647475200, 377957122048, 972777519512027136, 48378511622144]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 70920647475200, 972777519512027136, 5066549581840384]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [18414913207140352, (certNat% 12), 398709304510644224, 580964354078277632, 2851859333120, 562949953421312]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨19, by decide⟩ c16 c7
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00032.record035

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00032.record033
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "bc9cb4a969662d98e53a1e4789e9c7493a6592e479594b56354d2b46d8751d2743dd0e6358ce394e332cc73c2e8b62e4b52ccb86d1b26c5b61d4749c6785d1725e0f43c8f13c1f2983692549864a50d50d2341d90d4328c6384c3341c8709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db4db6da69b6924d249249249b6934db49249349a249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 56), (facetIndex 64)]))
 (.leaf ([(facetIndex 25), (facetIndex 43), (facetIndex 51), (facetIndex 58), (facetIndex 71)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 42), (facetIndex 44), (facetIndex 46), (facetIndex 48)]))
 (.leaf ([(facetIndex 35), (facetIndex 53), (facetIndex 62)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 22), (facetIndex 52), (facetIndex 55), (facetIndex 57)]))
 (.leaf ([(facetIndex 38), (facetIndex 45), (facetIndex 47), (facetIndex 49)])))
 (.branch 7
 (.leaf ([(facetIndex 23), (facetIndex 26), (facetIndex 29), (facetIndex 30), (facetIndex 31)]))
 (.leaf ([(facetIndex 20), (facetIndex 27), (facetIndex 50)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2000000c006081c3eaaaa280140600db2f88d07000000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 21), (facetIndex 54), (facetIndex 59)]))
 (.leaf ([(facetIndex 32), (facetIndex 60), (facetIndex 65)])))
 (.branch 3
 (.leaf ([(facetIndex 69), (facetIndex 72)]))
 (.leaf ([(facetIndex 73), (facetIndex 75)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 61), (facetIndex 63)]))
 (.leaf ([(facetIndex 33), (facetIndex 76)])))
 (.branch 7
 (.leaf ([(facetIndex 24), (facetIndex 34), (facetIndex 36), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 66)]))
 (.leaf ([(facetIndex 67), (facetIndex 68), (facetIndex 70), (facetIndex 74)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "57da1d7f88821000000000000036c061a9000006z12;"⟩
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
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6, 7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00032.record033" "{\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":2}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00032.record033" 37

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00032.record033" "{\"ridges\":[[37,328],[38,584],[42,98],[45,530],[47,97],[48,98],[49,322],[49,578],[54,108],[56,328],[60,120],[63,232],[64,328],[68,526],[69,78],[73,90],[74,778]],\"owners\":[[45,530,[68],[5,27,35,44,73,75]],[47,97,[54,60,63,65],[6,28,42,46,48,59]],[42,98,[72],[6,28,46,47,48,75]],[48,98,[72],[6,28,42,46,47,75]],[49,322,[69,72],[8,30,37,47,74]],[49,578,[73,75],[9,38,45,48,74]],[37,328,[],[16,56,64,69,74]],[56,328,[74],[16,37,64,69]],[64,328,[69],[16,37,56,74]],[38,584,[],[17,62,64,73,74]],[69,78,[21],[]],[68,526,[24],[]],[73,90,[32],[]],[74,778,[41],[]],[54,108,[],[]],[60,120,[],[]],[63,232,[],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00032.record033" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00032.record033\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-10,-2],[-12,-1],[-12,-3],[-12,-11],[-14,-3],[-14,-4],[-14,-8],[-14,-11],[-14,-13],[-16,-7],[-19,-1],[-20,-9],[-23,-12],[-26,-9],[-10,21],[-12,15,17,18,20],[-8,23],[-13,23],[-14,22,23],[-14,24,26],[-5],[-16,25],[-19,22],[-6],[-22,1],[-21,2],[-24,4],[-25,7],[-15],[-17],[-18],[-27,5,16,19],[-28,3,8,9,11,13],[-29,6,10,12,14],[-30,27],[-31,28],[-32,30,31],[-33,30],[-34,29],[-35,34],[-36,32],[-36,33,35],[36],[-37,22,23],[-22,37],[-23,37]],\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":45,\"b\":24},{\"tag\":\"incompatible\",\"a\":47,\"b\":21},{\"tag\":\"incompatible\",\"a\":47,\"b\":28},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":28},{\"tag\":\"incompatible\",\"a\":49,\"b\":32},{\"tag\":\"incompatible\",\"a\":49,\"b\":42},{\"tag\":\"incompatible\",\"a\":49,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":56,\"b\":41},{\"tag\":\"incompatible\",\"a\":64,\"b\":21},{\"tag\":\"incompatible\",\"a\":65,\"b\":44},{\"tag\":\"incompatible\",\"a\":72,\"b\":47},{\"tag\":\"incompatible\",\"a\":75,\"b\":44},{\"tag\":\"mate\",\"ridge\":530,\"a\":45,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":97,\"a\":47,\"owners\":[54,60,63,65]},{\"tag\":\"mate\",\"ridge\":98,\"a\":42,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":98,\"a\":48,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":322,\"a\":49,\"owners\":[69,72]},{\"tag\":\"mate\",\"ridge\":578,\"a\":49,\"owners\":[73,75]},{\"tag\":\"mate\",\"ridge\":328,\"a\":37,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":328,\"a\":56,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":328,\"a\":64,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":584,\"a\":38,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":78,\"a\":69,\"owners\":[21]},{\"tag\":\"mate\",\"ridge\":526,\"a\":68,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":90,\"a\":73,\"owners\":[32]},{\"tag\":\"mate\",\"ridge\":778,\"a\":74,\"owners\":[41]},{\"tag\":\"mate\",\"ridge\":108,\"a\":54,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":120,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":232,\"a\":63,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[37,56,64],\"full_literals\":[-27,5,16,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[28,42,44,46,48],\"full_literals\":[-28,3,8,9,11,13]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[38,45,47,49],\"full_literals\":[-29,6,10,12,14]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-30,27,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-31,28,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-32,30,31],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-33,30,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-34,false,29],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-35,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-36,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-36,33,35],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[69,72],\"full_literals\":[-37,22,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-22,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":72,\"full_literals\":[-23,37]}]}"
  "47 -27 16 19 0 21 32 0\n48 -29 10 12 14 0 24 34 0\n49 32 0 43 41 0\n50 -10 0 1 15 26 0\n51 37 30 0 49 43 50 31 30 29 38 42 40 39 37 36 45 46 17 18 19 48 3 4 16 33 12 0\n52 -16 0 10 22 28 0\n53 -19 0 11 23 25 0\n54 -27 0 53 52 47 0\n55 -30 0 54 35 0\n56 31 0 55 49 37 0\n57 -33 0 55 38 0\n58 37 0 55 51 0\n59 28 0 56 36 0\n60 35 0 57 43 42 0\n61 34 0 60 40 0\n62 29 0 61 39 0\n63 -12 0 58 2 13 25 44 0\n64 14 0 63 50 62 48 0\n65 -3 0 64 5 0\n66 -4 0 64 6 0\n67 -8 0 64 7 0\n68 -11 0 64 8 0\n69 -13 0 64 9 0\n70 -24 0 66 27 0\n71 9 0 68 65 67 59 69 33 0\n72 26 0 70 64 20 0\n73 0 72 71 14 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033 Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00032.record033
