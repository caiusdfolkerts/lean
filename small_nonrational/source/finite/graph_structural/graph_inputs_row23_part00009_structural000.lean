module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00009Data
public import GraphInputsRow23Part00009Frames
public import GraphInputsRow23Part00009Leaves
public import GraphInputsRow23Part00009Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record073
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record073
def vertexColumn : Fields := ⟨10, hexnat% "bc1f0ba1eb1695a362d876c398e538ce4b86e8791e278b91e715956352d475c358d534cd4b46d8751d2771394e332cc73c2d8b52ccb4ac6b86d1b26e8761e4751cc789d2719d1725e0f2b05c0f0aa1683ac18a6858560d90e2384e0b81e2a4590e70529615154354348d1342d0770328e1314c3342c8b12c2b06e0741c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "2492492492492492492492492492492492492492492489249249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fe00400000000000", hexnat% "740001000000000000", hexnat% "ff800000000000000000", hexnat% "1d00000000000000000000", hexnat% "ff8000000000000000000000", hexnat% "1d000000000000000000000000", 143692975610789888, hexnat% "142004200080000000000000000", hexnat% "a0002000000000000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record073_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record073_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record073_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record073_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record073_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record073_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record073_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record073_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record073_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record073

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record045
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "370bc1f32a36a3a2e87ac98d64d8b61d8ce8b92e2b86eca4d98e4b91e725355352d4753362d4b4ad1b4d38cd332cc73c2e8b92ccb4acab1ae1bc1d8751cc789ca719d1783d0f2705c0f3228a89a1683a49896158362384e0b81ec8629264590e525254550d48d1342d0770388d2324c530ce0b22c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12492492492492492492492492492492492492492489249249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55)]))
 (.leaf ([(facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 63)])))
 (.branch 3
 (.leaf ([(facetIndex 71), (facetIndex 72), (facetIndex 76), (facetIndex 78)]))
 (.branch 4
 (.leaf ([(facetIndex 67), (facetIndex 83), (facetIndex 98)]))
 (.leaf ([(facetIndex 64), (facetIndex 69), (facetIndex 74), (facetIndex 79), (facetIndex 84), (facetIndex 89), (facetIndex 94), (facetIndex 99)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 68), (facetIndex 73), (facetIndex 77), (facetIndex 82), (facetIndex 88), (facetIndex 92), (facetIndex 97), (facetIndex 101)]))
 (.leaf ([(facetIndex 65), (facetIndex 70), (facetIndex 75), (facetIndex 80), (facetIndex 85), (facetIndex 90), (facetIndex 95), (facetIndex 100)])))
 (.branch 8
 (.leaf ([(facetIndex 66), (facetIndex 91), (facetIndex 93)]))
 (.branch 9
 (.leaf ([(facetIndex 81), (facetIndex 96)]))
 (.leaf ([(facetIndex 86), (facetIndex 87)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5643586475764599643586425264522645376411111111z38;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [4]
def grouped2_0008 : List Nat := [5, 6]
def grouped2_0009 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0010 : List Nat := [7]
def grouped2_0011 : List Nat := [7, 8, 9]
def grouped2_0012 : List Nat := [8]
def grouped2_0013 : List Nat := [8, 9]
def grouped2_0014 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record045" "{\"atoms\":[{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record045" 17

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record045" "{\"ridges\":[],\"owners\":[],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record045" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record045\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-2,-1],[-3,-2],[-6,-4],[-6,-5],[-7,-4],[-7,-5],[-8,1,3,7],[-9,2,6],[-10,4,5],[-11,8],[-12,11],[-13,12],[-14,9],[-14,10],[-15,14],[-16,15],[-17,13],[-17,16],[17]],\"atoms\":[{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":81,\"b\":67},{\"tag\":\"incompatible\",\"a\":83,\"b\":81},{\"tag\":\"incompatible\",\"a\":96,\"b\":86},{\"tag\":\"incompatible\",\"a\":96,\"b\":87},{\"tag\":\"incompatible\",\"a\":98,\"b\":86},{\"tag\":\"incompatible\",\"a\":98,\"b\":87},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[67,83,98],\"full_literals\":[-8,1,3,7]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[81,96],\"full_literals\":[-9,2,6]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[86,87],\"full_literals\":[-10,4,5]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-11,8,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-12,false,11],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-13,false,12],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-14,9,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-14,false,10],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-15,false,14],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-16,false,15],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-17,13,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-17,false,16],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true}]}"
  "p cnf 17 19\n-2 -1 0\n-3 -2 0\n-6 -4 0\n-6 -5 0\n-7 -4 0\n-7 -5 0\n-8 1 3 7 0\n-9 2 6 0\n-10 4 5 0\n-11 8 0\n-12 11 0\n-13 12 0\n-14 9 0\n-14 10 0\n-15 14 0\n-16 15 0\n-17 13 0\n-17 16 0\n17 0\n"
  "20 13 0 19 17 0\n21 16 0 19 18 0\n22 12 0 20 12 0\n23 15 0 21 16 0\n24 11 0 22 11 0\n25 14 0 23 15 0\n26 8 0 24 10 0\n27 9 0 25 13 0\n28 10 0 25 14 0\n29 -6 0 28 3 4 9 0\n30 2 0 29 27 8 0\n31 -1 0 30 1 0\n32 -3 0 30 2 0\n33 7 0 32 26 31 7 0\n34 -4 0 33 5 0\n35 -5 0 33 6 0\n36 0 34 35 28 9 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record045_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record045

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record071
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "c723c2f07cc693a2e87a398762ba1e4789e17a394e4b91e4e5c56958d475c364d8b4ad4749d174e3c4d934cc73c2d4b4acab86c9b16cc785d1715e0f43c8fc60b41b21c0f0b21a91a0e8a6198960d84e0b81ec44b1c2469865190e4a519615254358344d0b41d28c6344c930cd0b12c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "492492492492492492492492492492492492489249249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 52), (facetIndex 64), (facetIndex 76), (facetIndex 87)]))
 (.leaf ([(facetIndex 47), (facetIndex 48), (facetIndex 53), (facetIndex 55), (facetIndex 57), (facetIndex 58), (facetIndex 59)])))
 (.branch 3
 (.leaf ([(facetIndex 50), (facetIndex 51), (facetIndex 54), (facetIndex 61), (facetIndex 62), (facetIndex 63)]))
 (.branch 4
 (.leaf ([(facetIndex 65), (facetIndex 67), (facetIndex 69), (facetIndex 70), (facetIndex 71)]))
 (.leaf ([(facetIndex 66), (facetIndex 73), (facetIndex 74), (facetIndex 75)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 79), (facetIndex 90), (facetIndex 91)]))
 (.leaf ([(facetIndex 80), (facetIndex 94), (facetIndex 95)])))
 (.branch 8
 (.leaf ([(facetIndex 49), (facetIndex 60), (facetIndex 72), (facetIndex 77), (facetIndex 81), (facetIndex 86), (facetIndex 88), (facetIndex 92)]))
 (.branch 9
 (.leaf ([(facetIndex 46), (facetIndex 56), (facetIndex 68), (facetIndex 78), (facetIndex 82), (facetIndex 85), (facetIndex 89), (facetIndex 93)]))
 (.leaf ([(facetIndex 83), (facetIndex 84)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "66875587078998765870444733383430222711181210227118z2e;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0002 : List Nat := [5]
def grouped2_0003 : List Nat := [5, 6]
def grouped2_0004 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0005 : List Nat := [6]
def grouped2_0006 : List Nat := [7]
def grouped2_0007 : List Nat := [7, 8, 9]
def grouped2_0008 : List Nat := [8]
def grouped2_0009 : List Nat := [8, 9]
def grouped2_0010 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record071" "{\"atoms\":[{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record071" 16

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record071" "{\"ridges\":[],\"owners\":[],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record071" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record071\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-2,-1],[-5,-3],[-5,-4],[-6,-3],[-6,-4],[-7,-3],[-7,-4],[-8,-3],[-8,-4],[-9,1,5,6],[-10,2,7,8],[-11,3,4],[-12,9],[-12,10],[-13,11],[-14,13],[-15,12],[-15,14],[-16,15],[16]],\"atoms\":[{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"incompatible\",\"a\":90,\"b\":83},{\"tag\":\"incompatible\",\"a\":90,\"b\":84},{\"tag\":\"incompatible\",\"a\":91,\"b\":83},{\"tag\":\"incompatible\",\"a\":91,\"b\":84},{\"tag\":\"incompatible\",\"a\":94,\"b\":83},{\"tag\":\"incompatible\",\"a\":94,\"b\":84},{\"tag\":\"incompatible\",\"a\":95,\"b\":83},{\"tag\":\"incompatible\",\"a\":95,\"b\":84},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[79,90,91],\"full_literals\":[-9,1,5,6]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[80,94,95],\"full_literals\":[-10,2,7,8]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[83,84],\"full_literals\":[-11,3,4]},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-12,9,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-12,false,10],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-13,false,11],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-14,false,13],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-15,12,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-15,false,14],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-16,false,15],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true}]}"
  "p cnf 16 20\n-2 -1 0\n-5 -3 0\n-5 -4 0\n-6 -3 0\n-6 -4 0\n-7 -3 0\n-7 -4 0\n-8 -3 0\n-8 -4 0\n-9 1 5 6 0\n-10 2 7 8 0\n-11 3 4 0\n-12 9 0\n-12 10 0\n-13 11 0\n-14 13 0\n-15 12 0\n-15 14 0\n-16 15 0\n16 0\n"
  "21 15 0 20 19 0\n22 12 0 21 17 0\n23 14 0 21 18 0\n24 9 0 22 13 0\n25 10 0 22 14 0\n26 13 0 23 16 0\n27 11 0 26 15 0\n28 -4 0 24 25 3 5 7 9 10 11 1 0\n29 3 0 28 27 12 0\n30 -5 0 29 2 0\n31 -6 0 29 4 0\n32 -7 0 29 6 0\n33 -8 0 29 8 0\n34 1 0 31 24 30 10 0\n35 2 0 32 25 33 11 0\n36 0 35 34 1 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record071_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record071

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record072
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f07cc6a5a8e8ba1eb16559362d8763386e8791e27b19966392e479c55554d4b51d4cd1b61d4749d94d538cd332cc73c2e8b92ccb8ac6b46c9bc1d8751cc749c6785c9783d0f2b05c0f3122aa1a1683a29916158362384e0b81ec44a9864590e4a5454550d48d1342d0770328e1344c530ce0b22c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12492492492492492492492492492492492492492489249249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55)]))
 (.leaf ([(facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 63)])))
 (.branch 3
 (.leaf ([(facetIndex 74), (facetIndex 89)]))
 (.branch 4
 (.leaf ([(facetIndex 71), (facetIndex 72), (facetIndex 75), (facetIndex 77), (facetIndex 78), (facetIndex 79)]))
 (.leaf ([(facetIndex 80), (facetIndex 82), (facetIndex 83), (facetIndex 84)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 86), (facetIndex 87), (facetIndex 90), (facetIndex 92), (facetIndex 93), (facetIndex 94)]))
 (.leaf ([(facetIndex 95), (facetIndex 97), (facetIndex 98), (facetIndex 99)])))
 (.branch 8
 (.leaf ([(facetIndex 65), (facetIndex 70), (facetIndex 76), (facetIndex 81), (facetIndex 85), (facetIndex 91), (facetIndex 96), (facetIndex 101)]))
 (.branch 9
 (.leaf ([(facetIndex 64), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 73), (facetIndex 88), (facetIndex 100)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "7966676555752955744474333732933788887811111111z38;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [4]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6]
def grouped2_0010 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0011 : List Nat := [6]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8, 9]
def grouped2_0014 : List Nat := [8]
def grouped2_0015 : List Nat := [8, 9]
def grouped2_0016 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record072" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record072" 50

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record072" "{\"ridges\":[[5,261],[16,769],[23,273],[27,529],[29,273],[29,529],[36,276],[42,784],[46,261],[51,261],[53,261],[54,261],[55,769],[63,769],[66,273],[67,529],[68,273],[69,529],[71,273],[72,529],[77,273],[78,273],[79,529],[82,529],[83,529],[84,273],[86,276],[92,276],[93,276],[94,784],[97,536],[98,536],[99,784]],\"owners\":[[5,261,[23,71,77,78,79],[46,51,53,54,55]],[46,261,[23,77,78,79],[5,51,53,54,55,71]],[51,261,[23,71,78,79],[5,46,53,54,55,77]],[53,261,[23,71,77,79],[5,46,51,54,55,78]],[54,261,[23,71,77,78,79],[5,46,51,53,55]],[16,769,[29,79,84],[55,63]],[55,769,[29,84],[16,63,79]],[63,769,[29,79],[16,55,84]],[36,276,[23,71,77,78,79],[86,92,93,94]],[86,276,[23,77,78,79],[36,71,92,93,94]],[92,276,[23,71,78,79],[36,77,86,93,94]],[93,276,[23,71,77,79],[36,78,86,92,94]],[97,536,[27,72,83,84],[40,82,87,98,99]],[98,536,[27,72,82,84],[40,83,87,97,99]],[42,784,[29,79,84],[94,99]],[94,784,[29,84],[42,79,99]],[99,784,[29,79],[42,84,94]]],\"edges\":[[22,[5,23,36,46,51,53,54,55,71,77,78,79,86,92,93,94]],[44,[16,29,42,55,63,79,84,94,99]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record072" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record072\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-15,-9],[-15,-12],[-17,-10],[-17,-12],[-21,-14],[-22,-15],[-23,-17],[-24,-5],[-24,-15],[-24,-17],[-24,-20],[-26,-16],[-27,-18],[-28,-8],[-28,-16],[-28,-18],[-28,-19],[-28,-24],[-29,-28],[-30,-14],[-31,-15],[-32,-17],[-33,-15],[-33,-17],[-34,-25],[-35,-16],[-36,-18],[-37,-16],[-37,-18],[-38,-14],[-1,3,19,22,23,24],[-8,3,22,23,24],[-9,3,19,23,24],[-10,3,19,22,24],[-11,3,19,22,23,24],[-3,-5,-15],[-3,-5,-17],[-3,-15,-28],[-3,-17,-28],[-5,-15,-19],[-5,-15,-23],[-5,-17,-19],[-5,-17,-22],[-15,-23,-28],[-17,-22,-28],[-4,-5,-16],[-4,-5,-18],[-4,-16,-24],[-4,-18,-24],[-5,-16,-20],[-5,-16,-27],[-5,-18,-20],[-5,-18,-26],[-16,-24,-27],[-18,-24,-26],[-2,5,24,28],[-12,5,28],[-13,5,24],[-6,3,19,22,23,24],[-29,3,22,23,24],[-31,3,19,23,24],[-32,3,19,22,24],[-35,4,20,27,28],[-36,4,20,26,28],[-7,5,24,28],[-33,5,28],[-37,5,24],[-39,25,26,27,28],[-40,34,35,36,37],[-41,14,15,16,17,18],[-42,21,30,38],[-43,39],[-44,43],[-45,44],[-46,40],[-47,41],[-47,42],[-48,47],[-49,46],[-49,48],[-50,45],[-50,49],[50],[1,3,6,8,9,10,11,12,19,22,23,24,29,31,32,33],[2,5,7,12,13,24,28,33,37]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":66,\"b\":51},{\"tag\":\"incompatible\",\"a\":66,\"b\":55},{\"tag\":\"incompatible\",\"a\":68,\"b\":53},{\"tag\":\"incompatible\",\"a\":68,\"b\":55},{\"tag\":\"incompatible\",\"a\":73,\"b\":64},{\"tag\":\"incompatible\",\"a\":77,\"b\":66},{\"tag\":\"incompatible\",\"a\":78,\"b\":68},{\"tag\":\"incompatible\",\"a\":79,\"b\":29},{\"tag\":\"incompatible\",\"a\":79,\"b\":66},{\"tag\":\"incompatible\",\"a\":79,\"b\":68},{\"tag\":\"incompatible\",\"a\":79,\"b\":72},{\"tag\":\"incompatible\",\"a\":82,\"b\":67},{\"tag\":\"incompatible\",\"a\":83,\"b\":69},{\"tag\":\"incompatible\",\"a\":84,\"b\":46},{\"tag\":\"incompatible\",\"a\":84,\"b\":67},{\"tag\":\"incompatible\",\"a\":84,\"b\":69},{\"tag\":\"incompatible\",\"a\":84,\"b\":71},{\"tag\":\"incompatible\",\"a\":84,\"b\":79},{\"tag\":\"incompatible\",\"a\":86,\"b\":84},{\"tag\":\"incompatible\",\"a\":88,\"b\":64},{\"tag\":\"incompatible\",\"a\":92,\"b\":66},{\"tag\":\"incompatible\",\"a\":93,\"b\":68},{\"tag\":\"incompatible\",\"a\":94,\"b\":66},{\"tag\":\"incompatible\",\"a\":94,\"b\":68},{\"tag\":\"incompatible\",\"a\":95,\"b\":80},{\"tag\":\"incompatible\",\"a\":97,\"b\":67},{\"tag\":\"incompatible\",\"a\":98,\"b\":69},{\"tag\":\"incompatible\",\"a\":99,\"b\":67},{\"tag\":\"incompatible\",\"a\":99,\"b\":69},{\"tag\":\"incompatible\",\"a\":100,\"b\":64},{\"tag\":\"mate\",\"ridge\":261,\"a\":5,\"owners\":[23,71,77,78,79]},{\"tag\":\"mate\",\"ridge\":261,\"a\":46,\"owners\":[23,77,78,79]},{\"tag\":\"mate\",\"ridge\":261,\"a\":51,\"owners\":[23,71,78,79]},{\"tag\":\"mate\",\"ridge\":261,\"a\":53,\"owners\":[23,71,77,79]},{\"tag\":\"mate\",\"ridge\":261,\"a\":54,\"owners\":[23,71,77,78,79]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[23,29,66]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[23,29,68]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[23,66,84]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[23,68,84]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[29,66,71]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[29,66,78]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[29,68,71]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[29,68,77]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[66,78,84]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[68,77,84]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[27,29,67]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[27,29,69]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[27,67,79]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[27,69,79]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[29,67,72]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[29,67,83]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[29,69,72]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[29,69,82]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[67,79,83]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[69,79,82]},{\"tag\":\"mate\",\"ridge\":769,\"a\":16,\"owners\":[29,79,84]},{\"tag\":\"mate\",\"ridge\":769,\"a\":55,\"owners\":[29,84]},{\"tag\":\"mate\",\"ridge\":769,\"a\":63,\"owners\":[29,79]},{\"tag\":\"mate\",\"ridge\":276,\"a\":36,\"owners\":[23,71,77,78,79]},{\"tag\":\"mate\",\"ridge\":276,\"a\":86,\"owners\":[23,77,78,79]},{\"tag\":\"mate\",\"ridge\":276,\"a\":92,\"owners\":[23,71,78,79]},{\"tag\":\"mate\",\"ridge\":276,\"a\":93,\"owners\":[23,71,77,79]},{\"tag\":\"mate\",\"ridge\":536,\"a\":97,\"owners\":[27,72,83,84]},{\"tag\":\"mate\",\"ridge\":536,\"a\":98,\"owners\":[27,72,82,84]},{\"tag\":\"mate\",\"ridge\":784,\"a\":42,\"owners\":[29,79,84]},{\"tag\":\"mate\",\"ridge\":784,\"a\":94,\"owners\":[29,84]},{\"tag\":\"mate\",\"ridge\":784,\"a\":99,\"owners\":[29,79]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[80,82,83,84],\"full_literals\":[-39,25,26,27,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[95,97,98,99],\"full_literals\":[-40,34,35,36,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[64,66,67,68,69],\"full_literals\":[-41,14,15,16,17,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[73,88,100],\"full_literals\":[-42,21,30,38]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-45,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-49,46,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-49,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-50,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-50,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[5,23,36,46,51,53,54,55,71,77,78,79,86,92,93,94]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[16,29,42,55,63,79,84,94,99]}]}"
  "p cnf 50 85\n-15 -9 0\n-15 -12 0\n-17 -10 0\n-17 -12 0\n-21 -14 0\n-22 -15 0\n-23 -17 0\n-24 -5 0\n-24 -15 0\n-24 -17 0\n-24 -20 0\n-26 -16 0\n-27 -18 0\n-28 -8 0\n-28 -16 0\n-28 -18 0\n-28 -19 0\n-28 -24 0\n-29 -28 0\n-30 -14 0\n-31 -15 0\n-32 -17 0\n-33 -15 0\n-33 -17 0\n-34 -25 0\n-35 -16 0\n-36 -18 0\n-37 -16 0\n-37 -18 0\n-38 -14 0\n-1 3 19 22 23 24 0\n-8 3 22 23 24 0\n-9 3 19 23 24 0\n-10 3 19 22 24 0\n-11 3 19 22 23 24 0\n-3 -5 -15 0\n-3 -5 -17 0\n-3 -15 -28 0\n-3 -17 -28 0\n-5 -15 -19 0\n-5 -15 -23 0\n-5 -17 -19 0\n-5 -17 -22 0\n-15 -23 -28 0\n-17 -22 -28 0\n-4 -5 -16 0\n-4 -5 -18 0\n-4 -16 -24 0\n-4 -18 -24 0\n-5 -16 -20 0\n-5 -16 -27 0\n-5 -18 -20 0\n-5 -18 -26 0\n-16 -24 -27 0\n-18 -24 -26 0\n-2 5 24 28 0\n-12 5 28 0\n-13 5 24 0\n-6 3 19 22 23 24 0\n-29 3 22 23 24 0\n-31 3 19 23 24 0\n-32 3 19 22 24 0\n-35 4 20 27 28 0\n-36 4 20 26 28 0\n-7 5 24 28 0\n-33 5 28 0\n-37 5 24 0\n-39 25 26 27 28 0\n-40 34 35 36 37 0\n-41 14 15 16 17 18 0\n-42 21 30 38 0\n-43 39 0\n-44 43 0\n-45 44 0\n-46 40 0\n-47 41 0\n-47 42 0\n-48 47 0\n-49 46 0\n-49 48 0\n-50 45 0\n-50 49 0\n50 0\n1 3 6 8 9 10 11 12 19 22 23 24 29 31 32 33 0\n2 5 7 12 13 24 28 33 37 0\n"
  "86 45 0 83 81 0\n87 49 0 83 82 0\n88 44 0 86 74 0\n89 46 0 87 79 0\n90 48 0 87 80 0\n91 43 0 88 73 0\n92 40 0 89 75 0\n93 47 0 90 78 0\n94 39 0 91 72 0\n95 41 0 93 76 0\n96 42 0 93 77 0\n97 24 28 5 0 66 57 58 67 56 65 85 0\n98 -14 0 96 5 20 30 71 0\n99 -15 -28 0 19 18 17 14 1 2 6 21 23 38 44 31 34 35 62 59 84 0\n100 -28 0 98 95 14 15 16 17 18 19 99 70 3 4 7 22 24 39 45 33 61 31 35 59 84 0\n101 -18 -24 0 100 94 92 11 13 27 29 49 55 63 68 69 25 0\n102 -16 -5 0 94 100 92 12 26 28 50 51 46 68 64 69 25 0\n103 -15 -5 0 8 1 2 6 21 23 40 41 36 32 60 31 34 35 62 59 84 0\n104 -17 -5 0 8 3 4 7 22 24 42 43 37 33 61 32 60 31 35 59 84 0\n105 -5 0 98 95 100 94 92 102 103 104 70 13 27 29 52 53 47 63 68 69 25 0\n106 24 0 100 105 97 0\n107 -15 0 106 9 0\n108 -17 0 106 10 0\n109 -20 0 106 11 0\n110 -18 0 106 101 0\n111 16 0 110 95 98 108 107 70 0\n112 -26 0 111 12 0\n113 -35 0 111 26 0\n114 -37 0 111 28 0\n115 -4 0 111 106 48 0\n116 -27 0 111 106 54 0\n117 25 0 112 94 116 100 68 0\n118 -36 0 112 115 109 100 64 0\n119 34 0 113 92 118 114 69 0\n120 0 119 117 25 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00009.record072_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00009.record072
