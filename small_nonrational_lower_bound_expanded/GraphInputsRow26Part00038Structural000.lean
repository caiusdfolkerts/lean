module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00038Data
public import GraphInputsRow26Part00038Frames
public import GraphInputsRow26Part00038Leaves
public import GraphInputsRow26Part00038Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00038.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨72, by decide⟩, ⟨79, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨97, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 2756220568431755264, 824633720832, 3377699720527872]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 3), 721702115164028928, 54043195528445952, 38654705664, 158329674399744]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 1443404230328057856, 54043195528445952, 38654705664, 158329674399744]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), 2310348532986413056, 2215771016666284032, 272193552384, 4492604511092736]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00038.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00038.record028
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "7ce4acaa6a3a719964da1e4783ee44f1b2699366391e5c5654d54d4758751d17783b0dc338f13a4d938cd332ce8b92ccb8ae1b46c9b0ed8751cc749e1745c970de0f43c1f1b03c1a8661382ea45911a6190e465454351342d0768360cc318e0b12c2b41c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9b6db6da4da6934d249249349b69249b4924d3492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 72), (facetIndex 82)]))
 (.leaf ([(facetIndex 50), (facetIndex 63), (facetIndex 71)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 44), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56)]))
 (.leaf ([(facetIndex 31), (facetIndex 58), (facetIndex 60), (facetIndex 61)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 57), (facetIndex 59), (facetIndex 65), (facetIndex 66)]))
 (.leaf ([(facetIndex 29), (facetIndex 33), (facetIndex 35), (facetIndex 37), (facetIndex 38)])))
 (.branch 7
 (.leaf ([(facetIndex 42), (facetIndex 46), (facetIndex 51), (facetIndex 68)]))
 (.leaf ([(facetIndex 28), (facetIndex 30), (facetIndex 39), (facetIndex 43), (facetIndex 45)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "20612021b8e2490c401baf80f6aa287efz15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7]
def grouped2_0010 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00038.record028" "{\"atoms\":[{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00038.record028" 18

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00038.record028" "{\"ridges\":[[42,536],[46,642],[50,400],[51,656],[63,400],[68,656],[71,400],[76,150],[81,786]],\"owners\":[[46,642,[81],[10,51,55,56,79,80]],[42,536,[],[18,59,66,68,74,78,79]],[50,400,[],[20,63,71,76,81]],[63,400,[81],[20,50,71,76]],[71,400,[76],[20,50,63,81]],[51,656,[],[21,68,71,79,81]],[68,656,[81],[21,51,71,79]],[76,150,[32],[]],[81,786,[52],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00038.record028" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00038.record028\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-6,-3],[-7,-6],[-8,-6],[-9,-1],[-3,11],[-2],[-4],[-7,11],[-9,10],[-5],[-8,11],[-10,1],[-11,6],[-12,4,7,9],[-13,2,3,5,8],[-14,12],[-15,14],[-16,13],[-17,16],[-18,15,17],[18]],\"atoms\":[{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":52,\"b\":46},{\"tag\":\"incompatible\",\"a\":63,\"b\":52},{\"tag\":\"incompatible\",\"a\":68,\"b\":52},{\"tag\":\"incompatible\",\"a\":71,\"b\":32},{\"tag\":\"mate\",\"ridge\":642,\"a\":46,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":536,\"a\":42,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":400,\"a\":50,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":400,\"a\":63,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":400,\"a\":71,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":656,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":656,\"a\":68,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":150,\"a\":76,\"owners\":[32]},{\"tag\":\"mate\",\"ridge\":786,\"a\":81,\"owners\":[52]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[50,63,71],\"full_literals\":[-12,4,7,9]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[42,46,51,68],\"full_literals\":[-13,2,3,5,8]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-14,false,12],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-15,14,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-16,13,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-17,false,16],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-18,15,17],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true}]}"
  "22 -12 7 9 0 7 14 0\n23 -13 3 8 0 6 10 15 0\n24 -3 0 1 5 13 0\n25 -8 0 3 11 13 0\n26 -13 0 25 24 23 0\n27 -16 0 26 18 0\n28 -17 0 27 19 0\n29 15 0 28 21 20 0\n30 14 0 29 17 0\n31 12 0 30 16 0\n32 -7 0 2 8 13 0\n33 9 0 32 31 22 0\n34 -1 0 33 4 0\n35 10 0 33 9 0\n36 0 35 34 12 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00038.record028
