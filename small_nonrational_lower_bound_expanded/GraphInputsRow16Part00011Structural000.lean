module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00011Data
public import GraphInputsRow16Part00011Frames
public import GraphInputsRow16Part00011Leaves
public import GraphInputsRow16Part00011Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record024
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 436849163854938112, (certNat% 3), 9835861586177163264, 2305843009213693952, 1099511627776]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 9799832789158199296, (certNat% 5), 566253857013760, 1266654575067136]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 3762290688, 2341876238638907392, (certNat% 7), 9227876735993774080, 576460752303423488]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), 288230376151711744, 1266656722550784, 565154349580288]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [434619354718404608, 11569747442714804224, (certNat% 10), 1266656722550784, 576742228890746880, 9311572983808, 566252787466240]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record024_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record024

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "33837332cab1a36a3a4e8d68d8ce4b89e1783ecc729c64d98e539356352d4cd4b46d2745dc8f13a4cd38cd33c2d4b32e2b4ae1b46c9b16c3b89d2785c570dd0f23c2f0f0c62584e07b218c5290e4c5254351342d0770330e1324d0b12c1b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db69a69249b49249249249349349249b492489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 26), (facetIndex 52), (facetIndex 53), (facetIndex 58)]))
 (.leaf ([(facetIndex 29), (facetIndex 55), (facetIndex 56), (facetIndex 59)])))
 (.branch 3
 (.leaf ([(facetIndex 49), (facetIndex 62), (facetIndex 63)]))
 (.leaf ([(facetIndex 27), (facetIndex 30), (facetIndex 36), (facetIndex 41), (facetIndex 51), (facetIndex 54), (facetIndex 66), (facetIndex 68)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 31), (facetIndex 38), (facetIndex 45), (facetIndex 47), (facetIndex 48)]))
 (.leaf ([(facetIndex 34), (facetIndex 39), (facetIndex 64)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 35), (facetIndex 37), (facetIndex 42), (facetIndex 43)]))
 (.leaf ([(facetIndex 46), (facetIndex 50), (facetIndex 57), (facetIndex 65), (facetIndex 70)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1c30fd4802392c07d49e0d98b33d408ce6z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 60)]))
 (.leaf ([(facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 77)]))
 (.leaf ([(facetIndex 40), (facetIndex 44), (facetIndex 61)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 71), (facetIndex 72), (facetIndex 74)]))
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 78)])))
 (.branch 7
 (.leaf ([(facetIndex 32), (facetIndex 33)]))
 (.leaf ([(facetIndex 67), (facetIndex 69)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "155b0c838e00018000000000003003000036z18;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6, 7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":5}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record000" 17

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record000" "{\"ridges\":[[39,296],[62,800],[63,800]],\"owners\":[[39,296,[78],[18,53,58,62,67,71,75]],[62,800,[76],[20,49,63,75,78]],[63,800,[75],[20,49,62,76,78]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-3,-1],[-3,-2],[-6,-3],[-7,-1],[-7,-6],[-8,-1],[-8,-6],[-9,-4],[-9,-5],[-2,9],[-4,8],[-5,7],[-10,3,4,5],[-11,1,2,6],[-12,10],[-13,12],[-14,11],[-15,14],[-16,13],[-16,15],[16],[-17,7,8,9],[-8,17]],\"atoms\":[{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":49,\"b\":34},{\"tag\":\"incompatible\",\"a\":49,\"b\":39},{\"tag\":\"incompatible\",\"a\":64,\"b\":49},{\"tag\":\"incompatible\",\"a\":75,\"b\":34},{\"tag\":\"incompatible\",\"a\":75,\"b\":64},{\"tag\":\"incompatible\",\"a\":76,\"b\":34},{\"tag\":\"incompatible\",\"a\":76,\"b\":64},{\"tag\":\"incompatible\",\"a\":78,\"b\":62},{\"tag\":\"incompatible\",\"a\":78,\"b\":63},{\"tag\":\"mate\",\"ridge\":296,\"a\":39,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":800,\"a\":62,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":800,\"a\":63,\"owners\":[75]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[49,62,63],\"full_literals\":[-10,3,4,5]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[34,39,64],\"full_literals\":[-11,1,2,6]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-12,10,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-13,false,12],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-14,false,11],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-15,14,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-16,13,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-16,false,15],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[75,76,78],\"full_literals\":[-17,7,8,9]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":76,\"full_literals\":[-8,17]}]}"
  "24 13 0 21 19 0\n25 15 0 21 20 0\n26 12 0 24 16 0\n27 14 0 25 18 0\n28 10 0 26 15 0\n29 11 0 27 17 0\n30 -7 2 0 29 4 5 14 0\n31 9 -17 0 29 10 30 22 6 7 14 0\n32 -3 0 29 1 2 3 14 0\n33 -9 0 32 28 8 9 13 0\n34 -2 0 33 10 0\n35 -17 0 33 31 0\n36 -7 0 34 30 0\n37 -8 0 35 23 0\n38 -5 0 36 12 0\n39 -4 0 37 11 0\n40 0 38 39 28 32 13 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record016
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "cb0dc8f32a36b2635936c38ce8b92e2785e0fb2936639c94d58d535c364d3362d4b61d2745d0f72334d332cf0b32e2b4ac6b26c5bc1d8751e2749d1715c3783d0f23c2f0e8c62584e07b218a439c14c52560d1341d30d2324c3312c2b06d0721c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6d369b4926926d249a4924934924924d2492489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 41), (facetIndex 45), (facetIndex 46)]))
 (.leaf ([(facetIndex 48), (facetIndex 61), (facetIndex 64)])))
 (.branch 3
 (.leaf ([(facetIndex 26), (facetIndex 40), (facetIndex 42), (facetIndex 62)]))
 (.leaf ([(facetIndex 29), (facetIndex 50), (facetIndex 52), (facetIndex 54), (facetIndex 56), (facetIndex 57)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 27), (facetIndex 31), (facetIndex 38), (facetIndex 47), (facetIndex 60), (facetIndex 66), (facetIndex 73)]))
 (.leaf ([(facetIndex 33), (facetIndex 49), (facetIndex 65)])))
 (.branch 7
 (.leaf ([(facetIndex 39), (facetIndex 43), (facetIndex 51), (facetIndex 55), (facetIndex 67), (facetIndex 70)]))
 (.leaf ([(facetIndex 28), (facetIndex 32), (facetIndex 35), (facetIndex 36), (facetIndex 37)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "20180d2908c01bcc3ce9800c82d3fe2f81f88z13;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 63)]))
 (.leaf ([(facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 78)]))
 (.leaf ([(facetIndex 34), (facetIndex 44), (facetIndex 53)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 68), (facetIndex 69), (facetIndex 71)]))
 (.leaf ([(facetIndex 74), (facetIndex 76), (facetIndex 79)])))
 (.branch 7
 (.leaf ([(facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 72), (facetIndex 77)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "abd347824000000d800180000030000000cz19;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6, 7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record016" "{\"atoms\":[{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":5}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record016" 17

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record016" "{\"ridges\":[[33,290],[48,800],[61,800],[64,800]],\"owners\":[[33,290,[76],[10,41,46,48,68,72,74]],[48,800,[79],[20,61,64,74,76]],[61,800,[76],[20,48,64,74,79]],[64,800,[74],[20,48,61,76,79]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record016" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record016\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-4,-1],[-4,-3],[-6,-4],[-7,-3],[-7,-6],[-8,-5],[-9,-1],[-9,-3],[-9,-6],[-1,8],[-2,9],[-4,8],[-5,7],[-10,2,4,5],[-11,1,3,6],[-12,10],[-13,12],[-14,11],[-15,14],[-16,13],[-16,15],[16],[-17,7,8,9],[-7,17],[-8,17],[-9,17]],\"atoms\":[{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":61,\"b\":33},{\"tag\":\"incompatible\",\"a\":61,\"b\":49},{\"tag\":\"incompatible\",\"a\":65,\"b\":61},{\"tag\":\"incompatible\",\"a\":74,\"b\":49},{\"tag\":\"incompatible\",\"a\":74,\"b\":65},{\"tag\":\"incompatible\",\"a\":76,\"b\":64},{\"tag\":\"incompatible\",\"a\":79,\"b\":33},{\"tag\":\"incompatible\",\"a\":79,\"b\":49},{\"tag\":\"incompatible\",\"a\":79,\"b\":65},{\"tag\":\"mate\",\"ridge\":290,\"a\":33,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":800,\"a\":48,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":800,\"a\":61,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":800,\"a\":64,\"owners\":[74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[48,61,64],\"full_literals\":[-10,2,4,5]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[33,49,65],\"full_literals\":[-11,1,3,6]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-12,false,10],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-13,12,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-14,false,11],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-15,14,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-16,13,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-16,false,15],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[74,76,79],\"full_literals\":[-17,7,8,9]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-7,17]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":76,\"full_literals\":[-8,17]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-9,17]}]}"
  "27 13 0 22 20 0\n28 15 0 22 21 0\n29 12 0 27 17 0\n30 14 0 28 19 0\n31 10 0 29 16 0\n32 11 0 30 18 0\n33 17 0 31 24 25 26 13 12 11 14 0\n34 8 9 0 33 32 10 23 4 5 15 0\n35 -4 0 32 1 2 3 15 0\n36 9 0 35 31 11 34 14 6 0\n37 -1 0 36 7 0\n38 -3 0 36 8 0\n39 -6 0 36 9 0\n40 0 38 39 32 37 15 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record029
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "31ac98e6558d6c3a2e2b91e1783ec6725395553570d8b4ad4745d0f723a8ce3c4d5334f0b2ae1b46c5b0ef0761d4789d2719c970de0f43c8f13e2a318a6458560b81e8a4c5295151542d0770330e2328d1314e0b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da49a4926d24d2492492492492492492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 37), (facetIndex 40), (facetIndex 57), (facetIndex 68)]))
 (.leaf ([(facetIndex 30), (facetIndex 34), (facetIndex 35), (facetIndex 39), (facetIndex 50), (facetIndex 61), (facetIndex 72)])))
 (.branch 3
 (.leaf ([(facetIndex 46), (facetIndex 51), (facetIndex 52)]))
 (.leaf ([(facetIndex 54), (facetIndex 55), (facetIndex 59), (facetIndex 60)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 65), (facetIndex 66), (facetIndex 70), (facetIndex 71)]))
 (.leaf ([(facetIndex 38), (facetIndex 47), (facetIndex 48)])))
 (.branch 7
 (.leaf ([(facetIndex 33), (facetIndex 36), (facetIndex 45), (facetIndex 56), (facetIndex 67)]))
 (.branch 8
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 49)]))
 (.leaf ([(facetIndex 29), (facetIndex 31), (facetIndex 41), (facetIndex 53), (facetIndex 64)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "14400644800133006338221755267778015061160818z1d;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 58), (facetIndex 62)]))
 (.leaf ([(facetIndex 63), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 73)]))
 (.leaf ([(facetIndex 74)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "3804004z1f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
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
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [2]
def grouped3_0022 : List Nat := [2, 3]
def grouped3_0023 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record029" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record029" 86

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record029" "{\"ridges\":[[5,261],[5,262],[6,25],[10,273],[13,67],[15,13],[15,25],[18,21],[18,261],[18,276],[19,37],[22,14],[22,26],[25,22],[25,262],[25,276],[26,38],[29,13],[29,14],[29,67],[31,261],[31,262],[36,261],[36,262],[39,261],[39,262],[40,261],[40,262],[40,770],[42,25],[42,26],[45,131],[45,161],[45,162],[46,770],[48,67],[48,273],[53,21],[53,25],[53,37],[57,13],[58,13],[59,21],[60,261],[60,276],[61,37],[62,37],[62,261],[62,804],[63,25],[63,792],[64,22],[64,26],[64,38],[68,14],[69,14],[70,22],[71,262],[71,276],[72,38],[73,38],[73,262],[73,804],[74,26],[74,792]],\"owners\":[[57,13,[0,15,29,30,31,54,55],[16,32,56,58]],[68,14,[0,22,29,30,31,65,66],[23,32,67,69]],[45,131,[4,13,34,39,47],[11,30,51]],[5,261,[18,55,58,60,62],[31,36,38,39,40]],[18,261,[5,31,36,38,39,40,58,62],[55,60]],[36,261,[18,55,58,60],[5,31,38,39,40,62]],[39,261,[18,55,58,60,62],[5,31,36,38,40]],[40,261,[18,55,60],[5,31,36,38,39,58,62]],[60,261,[5,31,36,39,40,58,62],[18,38,55]],[5,262,[25,66,69,71,73],[31,36,38,39,40]],[25,262,[5,31,36,38,39,40,69,73],[66,71]],[36,262,[25,66,69,71],[5,31,38,39,40,73]],[39,262,[25,66,69,71,73],[5,31,36,38,40]],[40,262,[25,66,71],[5,31,36,38,39,69,73]],[71,262,[5,31,36,39,40,69,73],[25,38,66]],[6,25,[15,53,54,55,63],[41,42,43,44]],[10,273,[18,55,60,63],[43,48,49]],[48,273,[18,55,63],[10,43,49,60]],[45,161,[19,61],[11,50,51,56]],[45,162,[26,72],[11,50,51,67]],[40,770,[74],[14,46,49,52,69,73]],[46,770,[73],[14,40,49,52,69,74]],[18,276,[25,66,71],[55,60]],[25,276,[18,55,60],[66,71]],[60,276,[25,66],[18,55,71]],[71,276,[18,55],[25,60,66]],[62,804,[73],[]],[73,804,[62],[]],[63,792,[74],[]],[74,792,[63],[]]],\"edges\":[[22,[5,18,25,31,36,38,39,40,55,58,60,62,66,69,71,73]],[24,[6,15,22,41,42,43,44,53,54,55,63,64,65,66,74]],[33,[10,18,25,43,48,49,55,60,63,66,71,74]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record029" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record029\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-2],[-13,-3],[-17,-13],[-18,-13],[-19,-13],[-21,-1],[-21,-13],[-21,-14],[-21,-20],[-22,-13],[-23,-13],[-23,-21],[-24,-16],[-24,-17],[-24,-20],[-25,-13],[-25,-16],[-25,-24],[-26,-15],[-27,-13],[-27,-24],[-28,-24],[-30,-13],[-30,-25],[-31,-25],[-32,-15],[-33,-24],[-34,-23],[-34,-32],[-35,-17],[-36,-13],[-36,-25],[-36,-35],[-37,-15],[-39,-24],[-40,-15],[-40,-16],[-40,-20],[-40,-26],[-40,-35],[-40,-37],[-40,-39],[-41,-21],[-42,-35],[-44,-38],[-46,-17],[-47,-13],[-47,-25],[-47,-46],[-48,-15],[-48,-40],[-50,-24],[-50,-40],[-51,-46],[-52,-21],[-53,-46],[-55,-16],[-55,-19],[-55,-20],[-55,-39],[-55,-49],[-55,-50],[-56,-15],[-56,-26],[-56,-27],[-56,-29],[-56,-32],[-56,-37],[-56,-40],[-56,-48],[-56,-51],[-39,1,7,13,14,15,36,37],[-7,-13,-40],[-50,1,10,13,14,15,47,48],[-10,-13,-51],[-8,-35,-41],[-11,-46,-52],[-9,-35,-44],[-35,-43,-44],[-12,-46,-55],[-46,-54,-55],[-6,-13,-31],[-28,2,6,18,22,30],[-3,8,37,40,42,44],[-8,3,15,19,21,22,23,40,44],[-19,8,37,40,42],[-22,8,37,40,42,44],[-23,8,37,42],[-42,3,15,19,22,23,40,44],[-8,-15,-44],[-15,-42,-44],[-3,11,48,51,53,55],[-11,3,15,19,21,22,23,51,55],[-19,11,48,51,53],[-22,11,48,51,53,55],[-23,11,48,53],[-53,3,15,19,22,23,51,55],[-11,-15,-55],[-15,-53,-55],[-4,7,35,36,37,45],[-7,-25,-45],[-25,-35,-45],[-10,-25,-56],[-25,-46,-56],[-5,8,37,42,45],[-31,8,37,45],[-28,9,43],[-28,12,54],[-23,56],[-29,55],[-8,11,48,53],[-11,8,37,42],[-42,11,48],[-53,8,37],[-44,55],[-55,44],[-45,56],[-56,45],[-57,16,20,23,39,50],[-58,29,33,34],[-59,36,37,41,42],[-60,47,48,52,53],[-61,21,30,31],[-62,17,19,28,38,49],[-63,25,26,27,32],[-64,13,15,24,35,46],[-65,57],[-66,58],[-66,59],[-67,65,66],[-68,65],[-68,66],[-69,60],[-69,61],[-70,63,64],[-71,63],[-71,64],[-73,62],[-72,70],[-73,71],[-74,69,73],[-75,69],[-74,72],[-75,73],[-76,67],[-76,68,75],[-76,74],[76],[-77,40,44],[-78,45,51],[-45,78],[-79,55],[-55,79],[-80,56],[-56,80],[-78,81],[-82,77],[-82,78],[-83,79,80],[-84,80],[-79,-80,84],[-85,82,83],[-81,-84,86],[85],[-86],[3,8,11,15,19,21,22,23,37,40,42,44,48,51,53,55],[4,7,10,24,25,26,27,35,36,37,45,46,47,48,56],[5,8,11,26,31,32,37,42,45,48,53,56]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":29,\"b\":4},{\"tag\":\"incompatible\",\"a\":29,\"b\":5},{\"tag\":\"incompatible\",\"a\":33,\"b\":29},{\"tag\":\"incompatible\",\"a\":34,\"b\":29},{\"tag\":\"incompatible\",\"a\":36,\"b\":29},{\"tag\":\"incompatible\",\"a\":38,\"b\":0},{\"tag\":\"incompatible\",\"a\":38,\"b\":29},{\"tag\":\"incompatible\",\"a\":38,\"b\":30},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":29},{\"tag\":\"incompatible\",\"a\":40,\"b\":29},{\"tag\":\"incompatible\",\"a\":40,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":32},{\"tag\":\"incompatible\",\"a\":41,\"b\":33},{\"tag\":\"incompatible\",\"a\":41,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":29},{\"tag\":\"incompatible\",\"a\":42,\"b\":32},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":31},{\"tag\":\"incompatible\",\"a\":44,\"b\":29},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":45,\"b\":41},{\"tag\":\"incompatible\",\"a\":47,\"b\":29},{\"tag\":\"incompatible\",\"a\":47,\"b\":42},{\"tag\":\"incompatible\",\"a\":48,\"b\":42},{\"tag\":\"incompatible\",\"a\":49,\"b\":31},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":52,\"b\":40},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":53,\"b\":33},{\"tag\":\"incompatible\",\"a\":54,\"b\":29},{\"tag\":\"incompatible\",\"a\":54,\"b\":42},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":55,\"b\":31},{\"tag\":\"incompatible\",\"a\":57,\"b\":41},{\"tag\":\"incompatible\",\"a\":58,\"b\":31},{\"tag\":\"incompatible\",\"a\":58,\"b\":32},{\"tag\":\"incompatible\",\"a\":58,\"b\":37},{\"tag\":\"incompatible\",\"a\":58,\"b\":43},{\"tag\":\"incompatible\",\"a\":58,\"b\":53},{\"tag\":\"incompatible\",\"a\":58,\"b\":55},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":38},{\"tag\":\"incompatible\",\"a\":60,\"b\":53},{\"tag\":\"incompatible\",\"a\":62,\"b\":56},{\"tag\":\"incompatible\",\"a\":64,\"b\":33},{\"tag\":\"incompatible\",\"a\":65,\"b\":29},{\"tag\":\"incompatible\",\"a\":65,\"b\":42},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":31},{\"tag\":\"incompatible\",\"a\":66,\"b\":58},{\"tag\":\"incompatible\",\"a\":68,\"b\":41},{\"tag\":\"incompatible\",\"a\":68,\"b\":58},{\"tag\":\"incompatible\",\"a\":69,\"b\":64},{\"tag\":\"incompatible\",\"a\":70,\"b\":38},{\"tag\":\"incompatible\",\"a\":71,\"b\":64},{\"tag\":\"incompatible\",\"a\":73,\"b\":32},{\"tag\":\"incompatible\",\"a\":73,\"b\":36},{\"tag\":\"incompatible\",\"a\":73,\"b\":37},{\"tag\":\"incompatible\",\"a\":73,\"b\":57},{\"tag\":\"incompatible\",\"a\":73,\"b\":67},{\"tag\":\"incompatible\",\"a\":73,\"b\":68},{\"tag\":\"incompatible\",\"a\":74,\"b\":31},{\"tag\":\"incompatible\",\"a\":74,\"b\":43},{\"tag\":\"incompatible\",\"a\":74,\"b\":44},{\"tag\":\"incompatible\",\"a\":74,\"b\":46},{\"tag\":\"incompatible\",\"a\":74,\"b\":49},{\"tag\":\"incompatible\",\"a\":74,\"b\":55},{\"tag\":\"incompatible\",\"a\":74,\"b\":58},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":69},{\"tag\":\"mate\",\"ridge\":13,\"a\":57,\"owners\":[0,15,29,30,31,54,55]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[15,29,58]},{\"tag\":\"mate\",\"ridge\":14,\"a\":68,\"owners\":[0,22,29,30,31,65,66]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[22,29,69]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[18,53,59]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[25,64,70]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[19,53,62]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[53,61,62]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[26,64,73]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[64,72,73]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[13,29,48]},{\"tag\":\"mate\",\"ridge\":131,\"a\":45,\"owners\":[4,13,34,39,47]},{\"tag\":\"mate\",\"ridge\":261,\"a\":5,\"owners\":[18,55,58,60,62]},{\"tag\":\"mate\",\"ridge\":261,\"a\":18,\"owners\":[5,31,36,38,39,40,58,62]},{\"tag\":\"mate\",\"ridge\":261,\"a\":36,\"owners\":[18,55,58,60]},{\"tag\":\"mate\",\"ridge\":261,\"a\":39,\"owners\":[18,55,58,60,62]},{\"tag\":\"mate\",\"ridge\":261,\"a\":40,\"owners\":[18,55,60]},{\"tag\":\"mate\",\"ridge\":261,\"a\":60,\"owners\":[5,31,36,39,40,58,62]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[18,31,62]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[31,60,62]},{\"tag\":\"mate\",\"ridge\":262,\"a\":5,\"owners\":[25,66,69,71,73]},{\"tag\":\"mate\",\"ridge\":262,\"a\":25,\"owners\":[5,31,36,38,39,40,69,73]},{\"tag\":\"mate\",\"ridge\":262,\"a\":36,\"owners\":[25,66,69,71]},{\"tag\":\"mate\",\"ridge\":262,\"a\":39,\"owners\":[25,66,69,71,73]},{\"tag\":\"mate\",\"ridge\":262,\"a\":40,\"owners\":[25,66,71]},{\"tag\":\"mate\",\"ridge\":262,\"a\":71,\"owners\":[5,31,36,39,40,69,73]},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[25,31,73]},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[31,71,73]},{\"tag\":\"mate\",\"ridge\":25,\"a\":6,\"owners\":[15,53,54,55,63]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[15,42,63]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[42,53,63]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[22,42,74]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[42,64,74]},{\"tag\":\"mate\",\"ridge\":273,\"a\":10,\"owners\":[18,55,60,63]},{\"tag\":\"mate\",\"ridge\":273,\"a\":48,\"owners\":[18,55,63]},{\"tag\":\"mate\",\"ridge\":161,\"a\":45,\"owners\":[19,61]},{\"tag\":\"mate\",\"ridge\":162,\"a\":45,\"owners\":[26,72]},{\"tag\":\"mate\",\"ridge\":770,\"a\":40,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":770,\"a\":46,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":276,\"a\":18,\"owners\":[25,66,71]},{\"tag\":\"mate\",\"ridge\":276,\"a\":25,\"owners\":[18,55,60]},{\"tag\":\"mate\",\"ridge\":276,\"a\":60,\"owners\":[25,66]},{\"tag\":\"mate\",\"ridge\":276,\"a\":71,\"owners\":[18,55]},{\"tag\":\"mate\",\"ridge\":804,\"a\":62,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":804,\"a\":73,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":792,\"a\":63,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":792,\"a\":74,\"owners\":[63]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[32,37,40,57,68],\"full_literals\":[-57,16,20,23,39,50]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[46,51,52],\"full_literals\":[-58,29,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[54,55,59,60],\"full_literals\":[-59,36,37,41,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[65,66,70,71],\"full_literals\":[-60,47,48,52,53]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[38,47,48],\"full_literals\":[-61,21,30,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[33,36,45,56,67],\"full_literals\":[-62,17,19,28,38,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[42,43,44,49],\"full_literals\":[-63,25,26,27,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[29,31,41,53,64],\"full_literals\":[-64,13,15,24,35,46]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-66,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,65,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-68,65,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-69,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-70,63,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-71,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-73,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,false,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-74,69,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-75,69,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-74,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-75,false,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-76,67,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-76,68,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-76,false,74],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[58,62],\"full_literals\":[-77,40,44]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[63,69],\"full_literals\":[-78,45,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":63,\"full_literals\":[-45,78]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[73],\"full_literals\":[-79,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":73,\"full_literals\":[-55,79]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[74],\"full_literals\":[-80,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":74,\"full_literals\":[-56,80]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-82,77,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-82,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-83,79,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-84,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-79,-80,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,82,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-81,-84,86],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[5,18,25,31,36,38,39,40,55,58,60,62,66,69,71,73]},{\"tag\":\"edge\",\"edge\":24,\"owners\":[6,15,22,41,42,43,44,53,54,55,63,64,65,66,74]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[10,18,25,43,48,49,55,60,63,66,71,74]}]}"
  "169 67 0 148 145 0\n170 74 0 148 147 0\n171 72 0 170 143 0\n172 70 0 171 139 0\n173 -84 0 165 160 163 154 156 118 151 0\n174 -71 -56 0 118 67 65 64 63 136 137 125 16 18 102 104 126 0\n175 -13 -80 0 173 161 153 115 154 71 70 69 68 63 2 5 7 10 11 85 89 93 97 166 0\n176 -24 -56 0 148 174 140 144 146 132 128 131 127 66 13 15 27 35 52 120 119 28 0\n177 -35 -80 0 173 148 154 174 140 144 146 132 129 161 153 115 71 70 69 68 63 33 44 121 43 76 84 88 86 87 112 114 166 0\n178 -46 -80 0 173 170 154 174 140 141 133 161 153 115 71 70 69 68 63 49 56 122 55 77 92 96 111 94 95 113 166 0\n179 -80 0 170 148 172 154 63 64 65 67 68 70 118 174 140 144 141 146 134 131 127 175 176 177 178 126 135 125 17 24 25 32 48 101 103 123 6 8 9 12 72 74 119 0\n180 -56 0 179 155 0\n181 -23 0 180 109 0\n182 -45 0 180 117 0\n183 -13 -55 0 181 148 59 60 57 62 119 127 131 146 144 138 142 134 116 45 61 58 1 3 4 7 10 23 124 123 83 82 0\n184 -15 -55 0 180 182 116 19 26 34 50 90 91 98 99 105 106 168 0\n185 -24 -55 0 181 148 59 60 57 62 119 127 131 146 144 138 116 45 61 58 14 22 124 0\n186 -35 -55 0 181 148 59 60 57 62 119 127 131 146 144 138 116 45 61 58 30 78 79 124 107 0\n187 -55 0 181 148 57 58 59 60 61 62 116 119 45 127 131 146 144 138 140 137 183 184 185 186 126 46 80 81 124 108 0\n188 -29 0 187 110 0\n189 -44 0 187 115 0\n190 -79 0 187 152 0\n191 -83 0 190 179 159 0\n192 82 0 191 164 162 0\n193 77 0 192 157 0\n194 78 0 192 158 0\n195 40 0 193 189 149 0\n196 51 0 194 182 150 0\n197 -15 0 195 36 0\n198 -16 0 195 37 0\n199 -20 0 195 38 0\n200 -26 0 195 39 0\n201 -35 0 195 40 0\n202 -37 0 195 41 0\n203 -39 0 195 42 0\n204 -48 0 195 51 0\n205 -50 0 195 53 0\n206 -46 0 196 54 0\n207 -57 0 205 198 203 199 181 119 0\n208 -65 0 207 127 0\n209 66 0 208 169 130 0\n210 -68 0 208 131 0\n211 58 0 209 128 0\n212 75 0 210 148 146 0\n213 73 0 212 144 0\n214 71 0 213 140 0\n215 63 0 214 136 0\n216 64 0 214 137 0\n217 36 10 7 24 25 27 47 0 201 202 182 204 200 206 180 167 100 0\n218 24 0 216 206 197 201 195 196 126 16 20 31 47 73 75 217 0\n219 -25 0 218 18 0\n220 -27 0 218 21 0\n221 -33 0 218 27 0\n222 32 0 219 200 220 215 125 0\n223 34 0 221 188 211 120 0\n224 0 223 222 29 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00011.record029
