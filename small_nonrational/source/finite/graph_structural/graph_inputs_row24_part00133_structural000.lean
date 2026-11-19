module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00133Data
public import GraphInputsRow24Part00133Frames
public import GraphInputsRow24Part00133Leaves
public import GraphInputsRow24Part00133Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record012
def vertexColumn : Fields := ⟨10, hexnat% "26a5a95a1ea66599561d98e8b92e2b91e0fb499a569965591e74599565955551d70da358d4b4ad8751d0f66358d5334c7362e4b52e2b4acab1ad1b16c3b61e4751e2749ca719d1715c3783e2c2709a2590e2382e07a618a499894958350d2342d0754318c9314d0b22c2b06d0721c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6924934db6d36da4924924924d2492493492492449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨69, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8200101004000000000", hexnat% "1fe00000080000000", 67562799093514240, hexnat% "7e0000000000000000000", 3010772074496, 3083030604283904]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record013
def vertexColumn : Fields := ⟨10, hexnat% "16a5687ad1a6659a565587663a2e4b8ae4783e5a5591e74599565955551d58d8b52d2b51d0f74358e5354cd31cd8b52e2b4acab1ad1b16c3bc1e8761e4751d2729c6785d1715c3783c9c9889a898964388e0b81e98499894954348d0b41d90d4388c6324c5342c8b0ac1b81d0721c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db69b6d24926db4db692492492492492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000800010044000000000", hexnat% "7e000000200000000", hexnat% "3f0000000000000000000", 65678639890432, 2269954949683085312, 31314091159060480]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2748f2725a95a1ea6659a5655a361d98e4b8ae4783e9c569566391e74599565a5655556351d58d8b52d2b61d4743d98d6394d5334e331cd8b52d2b2ac6b46c5b0ed8791d4789d2729c6785d1715c372709a2590e2382e07a6194499896152550d2342d0754318c9314d0b22c2b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db6da4924db6d349a6924924924d2492492692492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 76), (facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62)])))
 (.branch 3
 (.leaf ([(facetIndex 33), (facetIndex 64), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 55), (facetIndex 69), (facetIndex 75)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 31), (facetIndex 42), (facetIndex 49), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 41), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48)])))
 (.branch 7
 (.leaf ([(facetIndex 30), (facetIndex 32), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 40)]))
 (.leaf ([(facetIndex 38)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "600018482049249724825b6db2e1f6d9698z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7]
def grouped2_0010 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record002" 13

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record002" "{\"ridges\":[[55,608],[75,592]],\"owners\":[[75,592,[84],[21,53,66,90,92]],[55,608,[92],[22,69,75,86,90]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-3,-1],[-5,-1],[-6,-1],[-4,5],[-2,6],[-7,2,3,4],[-8,1],[-9,7],[-10,9],[-11,8],[-12,11],[-13,10],[-13,12],[13]],\"atoms\":[{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":69,\"b\":38},{\"tag\":\"incompatible\",\"a\":84,\"b\":38},{\"tag\":\"incompatible\",\"a\":92,\"b\":38},{\"tag\":\"mate\",\"ridge\":592,\"a\":75,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":608,\"a\":55,\"owners\":[92]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[55,69,75],\"full_literals\":[-7,2,3,4]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[38],\"full_literals\":[-8,1]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-9,false,7],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-10,false,9],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-11,false,8],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-12,false,11],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-13,10,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-13,false,12],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "p cnf 13 14\n-3 -1 0\n-5 -1 0\n-6 -1 0\n-4 5 0\n-2 6 0\n-7 2 3 4 0\n-8 1 0\n-9 7 0\n-10 9 0\n-11 8 0\n-12 11 0\n-13 10 0\n-13 12 0\n13 0\n"
  "15 10 0 14 12 0\n16 12 0 14 13 0\n17 9 0 15 9 0\n18 11 0 16 11 0\n19 7 0 17 8 0\n20 8 0 18 10 0\n21 1 0 20 7 0\n22 -3 0 21 1 0\n23 -5 0 21 2 0\n24 -6 0 21 3 0\n25 -4 0 23 4 0\n26 -2 0 24 5 0\n27 0 26 25 19 22 6 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "26a9687a59996558768b8ae4783e9a6591e565655551d62d2b51d0f74358d9394cd31ce8b92cab1ae1b46c5b0ed8751e2749ca719c570de0f43c9c989528a89a458962382e07a6154629265152548d0b41d90d4388c6344c9314e0b22c2b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "26da4d24936d2692492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 42), (facetIndex 49), (facetIndex 51), (facetIndex 69), (facetIndex 80)]))
 (.leaf ([(facetIndex 36), (facetIndex 59), (facetIndex 61), (facetIndex 62)])))
 (.branch 3
 (.leaf ([(facetIndex 38), (facetIndex 60), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 71), (facetIndex 75), (facetIndex 76)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 35), (facetIndex 45), (facetIndex 47), (facetIndex 48), (facetIndex 50), (facetIndex 52)]))
 (.leaf ([(facetIndex 70), (facetIndex 72), (facetIndex 73)])))
 (.branch 7
 (.leaf ([(facetIndex 46), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 57), (facetIndex 58)]))
 (.branch 8
 (.leaf ([(facetIndex 37), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 43), (facetIndex 44)]))
 (.leaf ([(facetIndex 56)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "330553500002201121668666404044647707772714z23;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 63), (facetIndex 66)]))
 (.leaf ([(facetIndex 67), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 74), (facetIndex 77)]))
 (.leaf ([(facetIndex 78), (facetIndex 79)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "f820014z21;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record007" 99

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record007" "{\"ridges\":[[7,11],[8,11],[9,19],[10,19],[10,131],[11,19],[11,259],[13,35],[13,515],[14,321],[14,322],[20,273],[22,521],[23,273],[24,577],[29,274],[31,522],[32,82],[32,274],[33,578],[37,35],[40,35],[40,131],[41,35],[41,38],[41,259],[44,131],[44,259],[47,11],[47,259],[48,19],[48,515],[52,131],[52,515],[52,522],[53,19],[54,131],[55,515],[56,131],[56,273],[56,274],[57,35],[57,259],[57,321],[57,322],[58,259],[58,321],[58,322],[58,515],[60,273],[60,276],[62,521],[63,116],[64,81],[64,261],[64,321],[66,356],[67,120],[68,600],[69,521],[69,577],[71,274],[71,276],[72,38],[73,38],[73,522],[74,38],[75,82],[75,262],[75,322],[78,120],[79,522],[79,600],[80,522],[80,578]],\"owners\":[[53,19,[1,5,10,11,48],[9,37,45,55]],[37,35,[6,12,13,50,57],[2,40,41,45,53]],[40,35,[6,12,13,45,53,57],[2,37,41,50]],[41,35,[6,12,13,45,50,53],[2,37,40,57]],[40,131,[7,10,52,54,56],[3,44,50]],[44,131,[7,10,50,52,54],[3,40,56]],[11,259,[4,14,35,41,44,57,58],[47,56]],[57,259,[4,11,35,44,47,56],[14,41,58]],[64,261,[4,35,41,44],[20,43,60,65,66]],[75,262,[4,35,41,44],[29,43,71,76,77]],[52,515,[13,15,42,55,58],[8,36,48]],[22,521,[8,36,48,51,52,68],[62,69]],[62,521,[8,48,51,52,68],[22,36,69]],[69,521,[8,36,48,52],[22,51,62,68]],[31,522,[8,36,48,51,52,79],[73,80]],[73,522,[8,48,51,52,79],[31,36,80]],[80,522,[8,36,48,52],[31,51,73,79]],[64,81,[9,46,53,54,55,67,68],[23,38,63]],[32,82,[9,38,46,53,54,55,74,78,79],[75]],[75,82,[9,46,53,54,55,78,79],[32,38,74]],[14,321,[23,64,66],[43,57,58]],[57,321,[23,64],[14,43,58,66]],[58,321,[23,64,66],[14,43,57]],[64,321,[14,57,58],[23,43,66]],[14,322,[32,75,77],[43,57,58]],[57,322,[32,75],[14,43,58,77]],[58,322,[32,75,77],[14,43,57]],[75,322,[14,57,58],[32,43,77]],[24,577,[15,51,55,58,68],[69]],[69,577,[15,55,58],[24,51,68]],[33,578,[15,51,55,58,79],[80]],[80,578,[15,55,58],[33,51,79]],[60,276,[29,75,76],[20,64,65,71]],[71,276,[20,64,65],[29,60,75,76]],[63,116,[74],[]],[66,356,[77],[]],[67,120,[78],[]],[78,120,[67],[]],[68,600,[79],[]],[79,600,[68],[]]],\"edges\":[[29,[8,22,31,36,48,51,52,62,68,69,73,79,80]],[40,[14,23,32,43,57,58,64,66,75,77]],[41,[15,24,33,51,55,58,68,69,79,80]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-24,-2],[-24,-22],[-25,-24],[-27,-1],[-27,-2],[-27,-22],[-29,-23],[-29,-24],[-29,-26],[-29,-27],[-29,-28],[-30,-25],[-31,-22],[-31,-25],[-31,-29],[-32,-6],[-32,-23],[-34,-8],[-34,-23],[-34,-24],[-34,-33],[-35,-4],[-35,-5],[-35,-25],[-35,-32],[-35,-33],[-35,-34],[-36,-24],[-36,-26],[-36,-27],[-36,-28],[-36,-32],[-36,-33],[-36,-35],[-37,-6],[-37,-23],[-37,-35],[-37,-36],[-38,-32],[-38,-37],[-39,-3],[-39,-4],[-39,-32],[-39,-33],[-39,-35],[-39,-36],[-39,-38],[-40,-12],[-40,-13],[-40,-36],[-40,-38],[-41,-34],[-41,-35],[-42,-10],[-42,-12],[-42,-34],[-42,-35],[-42,-36],[-42,-40],[-43,-25],[-43,-30],[-43,-31],[-43,-33],[-43,-34],[-43,-35],[-43,-41],[-43,-42],[-44,-13],[-44,-28],[-44,-36],[-44,-38],[-44,-42],[-45,-7],[-45,-10],[-45,-36],[-45,-38],[-45,-40],[-45,-42],[-45,-44],[-47,-24],[-47,-46],[-48,-47],[-49,-29],[-50,-26],[-50,-30],[-51,-30],[-51,-43],[-52,-24],[-52,-31],[-52,-43],[-53,-26],[-53,-28],[-53,-30],[-54,-36],[-54,-38],[-55,-36],[-55,-38],[-56,-54],[-56,-55],[-57,-50],[-58,-22],[-58,-24],[-58,-34],[-58,-47],[-58,-57],[-59,-58],[-60,-32],[-60,-37],[-61,-40],[-61,-58],[-62,-26],[-62,-30],[-62,-43],[-63,-24],[-63,-31],[-63,-43],[-63,-52],[-64,-28],[-65,-60],[-66,-35],[-67,-54],[-67,-55],[-5,-6,-34],[-40,1,3,8,9,35],[-7,-8,-35],[-8,-9,-35],[-8,-35,-40],[-24,4,10,11,37,44],[-27,4,10,11,32,40,44],[-28,4,10,11,32,37,40],[-11,-27,-44],[-28,-59,-61],[-28,-60,-61],[-27,5,8,39,41,43],[-31,5,8,37,39,41],[-8,-27,-39],[-27,-39,-41],[-27,-39,-43],[-31,-39,-41],[-9,2,12,22,28,31,44,45],[-44,2,9,22,31,34,43],[-28,-34,-45],[-31,-34,-45],[-51,2,22,28,31],[-62,2,22,28,31],[-39,11,13,29,42,45],[-11,-35,-45],[-11,-39,-42],[-11,-39,-45],[-15,6,23,35,38,39,55],[-49,6,35,38,39,55],[-56,6,23,35,39],[-19,6,23,35,38,39,66],[-60,6,35,38,39,66],[-67,6,23,35,39],[-39,-60,-66],[-51,7,33,40,41,42,54,55],[-20,7,25,33,40,41,42,61,65,66],[-62,7,33,40,41,42,65,66],[-14,-16,-43],[-16,-43,-47],[-18,-20,-43],[-20,-43,-58],[-12,16,51,53],[-44,16,51],[-45,16,51,53],[-51,12,44,45],[-12,20,62,64],[-44,20,62],[-45,20,62,64],[-62,12,44,45],[-17,13,38,42,45,55],[-56,13,42,45],[-21,13,38,42,45,66],[-67,13,42,45],[-47,18,62,63],[-58,14,51,52],[-50,61],[-53,64],[-54,65],[-65,54],[-55,66],[-66,55],[-68,29,36,38,56,67],[-69,23,46,48,49],[-70,25,47,51,52],[-71,58,62,63],[-72,22,32,34,35,37,39],[-73,57,59,60],[-74,33,40,41,42,44,45],[-75,24,26,27,28,30,31],[-76,43],[-77,68],[-77,69],[-78,70,71],[-79,70],[-79,71],[-81,77],[-80,78],[-81,79],[-82,72],[-82,73],[-83,75,76],[-84,75],[-84,76],[-85,74,84],[-86,74],[-85,83],[-86,84],[-87,82,86],[-88,82],[-87,85],[-88,86],[-89,80],[-89,81,88],[-89,87],[89],[-90,50,53],[-91,54,55],[-54,91],[-55,91],[-92,61,64],[-61,92],[-64,92],[-93,65,66],[-65,93],[-66,93],[-94,90,91],[-91,94],[-95,91],[-96,92,93],[-97,93],[-92,-93,97],[-98,94,97],[-98,95,96],[-94,-97,99],[98],[-99],[6,15,19,23,35,38,39,49,55,56,60,66,67],[12,16,20,30,44,45,51,53,62,64],[13,17,21,38,42,45,55,56,66,67]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":37,\"b\":4},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":1},{\"tag\":\"incompatible\",\"a\":40,\"b\":4},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":42,\"b\":36},{\"tag\":\"incompatible\",\"a\":42,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":40},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":38},{\"tag\":\"incompatible\",\"a\":44,\"b\":35},{\"tag\":\"incompatible\",\"a\":44,\"b\":38},{\"tag\":\"incompatible\",\"a\":44,\"b\":42},{\"tag\":\"incompatible\",\"a\":45,\"b\":8},{\"tag\":\"incompatible\",\"a\":45,\"b\":36},{\"tag\":\"incompatible\",\"a\":47,\"b\":10},{\"tag\":\"incompatible\",\"a\":47,\"b\":36},{\"tag\":\"incompatible\",\"a\":47,\"b\":37},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":48,\"b\":6},{\"tag\":\"incompatible\",\"a\":48,\"b\":7},{\"tag\":\"incompatible\",\"a\":48,\"b\":38},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":48,\"b\":46},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":37},{\"tag\":\"incompatible\",\"a\":49,\"b\":39},{\"tag\":\"incompatible\",\"a\":49,\"b\":40},{\"tag\":\"incompatible\",\"a\":49,\"b\":41},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":8},{\"tag\":\"incompatible\",\"a\":50,\"b\":36},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":45},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":5},{\"tag\":\"incompatible\",\"a\":52,\"b\":6},{\"tag\":\"incompatible\",\"a\":52,\"b\":45},{\"tag\":\"incompatible\",\"a\":52,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":14},{\"tag\":\"incompatible\",\"a\":53,\"b\":15},{\"tag\":\"incompatible\",\"a\":53,\"b\":49},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":47},{\"tag\":\"incompatible\",\"a\":54,\"b\":48},{\"tag\":\"incompatible\",\"a\":55,\"b\":12},{\"tag\":\"incompatible\",\"a\":55,\"b\":14},{\"tag\":\"incompatible\",\"a\":55,\"b\":47},{\"tag\":\"incompatible\",\"a\":55,\"b\":48},{\"tag\":\"incompatible\",\"a\":55,\"b\":49},{\"tag\":\"incompatible\",\"a\":55,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":38},{\"tag\":\"incompatible\",\"a\":56,\"b\":43},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":56,\"b\":46},{\"tag\":\"incompatible\",\"a\":56,\"b\":47},{\"tag\":\"incompatible\",\"a\":56,\"b\":48},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":15},{\"tag\":\"incompatible\",\"a\":57,\"b\":41},{\"tag\":\"incompatible\",\"a\":57,\"b\":49},{\"tag\":\"incompatible\",\"a\":57,\"b\":51},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":58,\"b\":9},{\"tag\":\"incompatible\",\"a\":58,\"b\":12},{\"tag\":\"incompatible\",\"a\":58,\"b\":49},{\"tag\":\"incompatible\",\"a\":58,\"b\":51},{\"tag\":\"incompatible\",\"a\":58,\"b\":53},{\"tag\":\"incompatible\",\"a\":58,\"b\":55},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":60,\"b\":37},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":42},{\"tag\":\"incompatible\",\"a\":63,\"b\":39},{\"tag\":\"incompatible\",\"a\":63,\"b\":43},{\"tag\":\"incompatible\",\"a\":64,\"b\":43},{\"tag\":\"incompatible\",\"a\":64,\"b\":56},{\"tag\":\"incompatible\",\"a\":65,\"b\":37},{\"tag\":\"incompatible\",\"a\":65,\"b\":44},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":39},{\"tag\":\"incompatible\",\"a\":66,\"b\":41},{\"tag\":\"incompatible\",\"a\":66,\"b\":43},{\"tag\":\"incompatible\",\"a\":67,\"b\":49},{\"tag\":\"incompatible\",\"a\":67,\"b\":51},{\"tag\":\"incompatible\",\"a\":68,\"b\":49},{\"tag\":\"incompatible\",\"a\":68,\"b\":51},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":63},{\"tag\":\"incompatible\",\"a\":71,\"b\":35},{\"tag\":\"incompatible\",\"a\":71,\"b\":37},{\"tag\":\"incompatible\",\"a\":71,\"b\":47},{\"tag\":\"incompatible\",\"a\":71,\"b\":60},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":45},{\"tag\":\"incompatible\",\"a\":73,\"b\":50},{\"tag\":\"incompatible\",\"a\":74,\"b\":53},{\"tag\":\"incompatible\",\"a\":74,\"b\":71},{\"tag\":\"incompatible\",\"a\":75,\"b\":39},{\"tag\":\"incompatible\",\"a\":75,\"b\":43},{\"tag\":\"incompatible\",\"a\":75,\"b\":56},{\"tag\":\"incompatible\",\"a\":76,\"b\":37},{\"tag\":\"incompatible\",\"a\":76,\"b\":44},{\"tag\":\"incompatible\",\"a\":76,\"b\":56},{\"tag\":\"incompatible\",\"a\":76,\"b\":65},{\"tag\":\"incompatible\",\"a\":77,\"b\":41},{\"tag\":\"incompatible\",\"a\":78,\"b\":73},{\"tag\":\"incompatible\",\"a\":79,\"b\":48},{\"tag\":\"incompatible\",\"a\":80,\"b\":67},{\"tag\":\"incompatible\",\"a\":80,\"b\":68},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[7,8,47]},{\"tag\":\"mate\",\"ridge\":19,\"a\":53,\"owners\":[1,5,10,11,48]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[9,10,48]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[10,11,48]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[10,48,53]},{\"tag\":\"mate\",\"ridge\":35,\"a\":37,\"owners\":[6,12,13,50,57]},{\"tag\":\"mate\",\"ridge\":35,\"a\":40,\"owners\":[6,12,13,45,53,57]},{\"tag\":\"mate\",\"ridge\":35,\"a\":41,\"owners\":[6,12,13,45,50,53]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[13,40,57]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[41,72,74]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[41,73,74]},{\"tag\":\"mate\",\"ridge\":131,\"a\":40,\"owners\":[7,10,52,54,56]},{\"tag\":\"mate\",\"ridge\":131,\"a\":44,\"owners\":[7,10,50,52,54]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[10,40,52]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[40,52,54]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[40,52,56]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[44,52,54]},{\"tag\":\"mate\",\"ridge\":259,\"a\":11,\"owners\":[4,14,35,41,44,57,58]},{\"tag\":\"mate\",\"ridge\":259,\"a\":57,\"owners\":[4,11,35,44,47,56]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[41,47,58]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[44,47,58]},{\"tag\":\"mate\",\"ridge\":261,\"a\":64,\"owners\":[4,35,41,44]},{\"tag\":\"mate\",\"ridge\":262,\"a\":75,\"owners\":[4,35,41,44]},{\"tag\":\"mate\",\"ridge\":515,\"a\":52,\"owners\":[13,15,42,55,58]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[13,48,58]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[13,52,55]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[13,52,58]},{\"tag\":\"mate\",\"ridge\":521,\"a\":22,\"owners\":[8,36,48,51,52,68]},{\"tag\":\"mate\",\"ridge\":521,\"a\":62,\"owners\":[8,48,51,52,68]},{\"tag\":\"mate\",\"ridge\":521,\"a\":69,\"owners\":[8,36,48,52]},{\"tag\":\"mate\",\"ridge\":522,\"a\":31,\"owners\":[8,36,48,51,52,79]},{\"tag\":\"mate\",\"ridge\":522,\"a\":73,\"owners\":[8,48,51,52,79]},{\"tag\":\"mate\",\"ridge\":522,\"a\":80,\"owners\":[8,36,48,52]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[52,73,79]},{\"tag\":\"mate\",\"ridge\":81,\"a\":64,\"owners\":[9,46,53,54,55,67,68]},{\"tag\":\"mate\",\"ridge\":82,\"a\":32,\"owners\":[9,38,46,53,54,55,74,78,79]},{\"tag\":\"mate\",\"ridge\":82,\"a\":75,\"owners\":[9,46,53,54,55,78,79]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[20,23,56]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[23,56,60]},{\"tag\":\"three\",\"ridge\":274,\"vertices\":[29,32,56]},{\"tag\":\"three\",\"ridge\":274,\"vertices\":[32,56,71]},{\"tag\":\"mate\",\"ridge\":321,\"a\":14,\"owners\":[23,64,66]},{\"tag\":\"mate\",\"ridge\":321,\"a\":57,\"owners\":[23,64]},{\"tag\":\"mate\",\"ridge\":321,\"a\":58,\"owners\":[23,64,66]},{\"tag\":\"mate\",\"ridge\":321,\"a\":64,\"owners\":[14,57,58]},{\"tag\":\"mate\",\"ridge\":322,\"a\":14,\"owners\":[32,75,77]},{\"tag\":\"mate\",\"ridge\":322,\"a\":57,\"owners\":[32,75]},{\"tag\":\"mate\",\"ridge\":322,\"a\":58,\"owners\":[32,75,77]},{\"tag\":\"mate\",\"ridge\":322,\"a\":75,\"owners\":[14,57,58]},{\"tag\":\"mate\",\"ridge\":577,\"a\":24,\"owners\":[15,51,55,58,68]},{\"tag\":\"mate\",\"ridge\":577,\"a\":69,\"owners\":[15,55,58]},{\"tag\":\"mate\",\"ridge\":578,\"a\":33,\"owners\":[15,51,55,58,79]},{\"tag\":\"mate\",\"ridge\":578,\"a\":80,\"owners\":[15,55,58]},{\"tag\":\"mate\",\"ridge\":276,\"a\":60,\"owners\":[29,75,76]},{\"tag\":\"mate\",\"ridge\":276,\"a\":71,\"owners\":[20,64,65]},{\"tag\":\"mate\",\"ridge\":116,\"a\":63,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":356,\"a\":66,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":120,\"a\":67,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":120,\"a\":78,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":600,\"a\":68,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":600,\"a\":79,\"owners\":[68]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[42,49,51,69,80],\"full_literals\":[-68,29,36,38,56,67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[36,59,61,62],\"full_literals\":[-69,23,46,48,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[38,60,64,65],\"full_literals\":[-70,25,47,51,52]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[71,75,76],\"full_literals\":[-71,58,62,63]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[35,45,47,48,50,52],\"full_literals\":[-72,22,32,34,35,37,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[70,72,73],\"full_literals\":[-73,57,59,60]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[46,53,54,55,57,58],\"full_literals\":[-74,33,40,41,42,44,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[37,39,40,41,43,44],\"full_literals\":[-75,24,26,27,28,30,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[56],\"full_literals\":[-76,43]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-77,68,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,70,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-79,70,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,false,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-81,77,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,false,78],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-81,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-82,72,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-82,false,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-83,75,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-84,75,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-84,false,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-85,74,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-86,74,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,false,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,false,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-87,82,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-88,82,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-87,false,85],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-88,false,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-89,80,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-89,81,88],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-89,false,87],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[63,66],\"full_literals\":[-90,50,53]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[67,68],\"full_literals\":[-91,54,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-54,91]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":68,\"full_literals\":[-55,91]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[74,77],\"full_literals\":[-92,61,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":74,\"full_literals\":[-61,92]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":77,\"full_literals\":[-64,92]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[78,79],\"full_literals\":[-93,65,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":78,\"full_literals\":[-65,93]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":79,\"full_literals\":[-66,93]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-94,90,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-91,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-95,false,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-96,92,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-97,false,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-92,-93,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-98,94,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-98,95,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-94,-97,99],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[8,22,31,36,48,51,52,62,68,69,73,79,80]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[14,23,32,43,57,58,64,66,75,77]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[15,24,33,51,55,58,68,69,79,80]}]}"
  "p cnf 99 241\n-24 -2 0\n-24 -22 0\n-25 -24 0\n-27 -1 0\n-27 -2 0\n-27 -22 0\n-29 -23 0\n-29 -24 0\n-29 -26 0\n-29 -27 0\n-29 -28 0\n-30 -25 0\n-31 -22 0\n-31 -25 0\n-31 -29 0\n-32 -6 0\n-32 -23 0\n-34 -8 0\n-34 -23 0\n-34 -24 0\n-34 -33 0\n-35 -4 0\n-35 -5 0\n-35 -25 0\n-35 -32 0\n-35 -33 0\n-35 -34 0\n-36 -24 0\n-36 -26 0\n-36 -27 0\n-36 -28 0\n-36 -32 0\n-36 -33 0\n-36 -35 0\n-37 -6 0\n-37 -23 0\n-37 -35 0\n-37 -36 0\n-38 -32 0\n-38 -37 0\n-39 -3 0\n-39 -4 0\n-39 -32 0\n-39 -33 0\n-39 -35 0\n-39 -36 0\n-39 -38 0\n-40 -12 0\n-40 -13 0\n-40 -36 0\n-40 -38 0\n-41 -34 0\n-41 -35 0\n-42 -10 0\n-42 -12 0\n-42 -34 0\n-42 -35 0\n-42 -36 0\n-42 -40 0\n-43 -25 0\n-43 -30 0\n-43 -31 0\n-43 -33 0\n-43 -34 0\n-43 -35 0\n-43 -41 0\n-43 -42 0\n-44 -13 0\n-44 -28 0\n-44 -36 0\n-44 -38 0\n-44 -42 0\n-45 -7 0\n-45 -10 0\n-45 -36 0\n-45 -38 0\n-45 -40 0\n-45 -42 0\n-45 -44 0\n-47 -24 0\n-47 -46 0\n-48 -47 0\n-49 -29 0\n-50 -26 0\n-50 -30 0\n-51 -30 0\n-51 -43 0\n-52 -24 0\n-52 -31 0\n-52 -43 0\n-53 -26 0\n-53 -28 0\n-53 -30 0\n-54 -36 0\n-54 -38 0\n-55 -36 0\n-55 -38 0\n-56 -54 0\n-56 -55 0\n-57 -50 0\n-58 -22 0\n-58 -24 0\n-58 -34 0\n-58 -47 0\n-58 -57 0\n-59 -58 0\n-60 -32 0\n-60 -37 0\n-61 -40 0\n-61 -58 0\n-62 -26 0\n-62 -30 0\n-62 -43 0\n-63 -24 0\n-63 -31 0\n-63 -43 0\n-63 -52 0\n-64 -28 0\n-65 -60 0\n-66 -35 0\n-67 -54 0\n-67 -55 0\n-5 -6 -34 0\n-40 1 3 8 9 35 0\n-7 -8 -35 0\n-8 -9 -35 0\n-8 -35 -40 0\n-24 4 10 11 37 44 0\n-27 4 10 11 32 40 44 0\n-28 4 10 11 32 37 40 0\n-11 -27 -44 0\n-28 -59 -61 0\n-28 -60 -61 0\n-27 5 8 39 41 43 0\n-31 5 8 37 39 41 0\n-8 -27 -39 0\n-27 -39 -41 0\n-27 -39 -43 0\n-31 -39 -41 0\n-9 2 12 22 28 31 44 45 0\n-44 2 9 22 31 34 43 0\n-28 -34 -45 0\n-31 -34 -45 0\n-51 2 22 28 31 0\n-62 2 22 28 31 0\n-39 11 13 29 42 45 0\n-11 -35 -45 0\n-11 -39 -42 0\n-11 -39 -45 0\n-15 6 23 35 38 39 55 0\n-49 6 35 38 39 55 0\n-56 6 23 35 39 0\n-19 6 23 35 38 39 66 0\n-60 6 35 38 39 66 0\n-67 6 23 35 39 0\n-39 -60 -66 0\n-51 7 33 40 41 42 54 55 0\n-20 7 25 33 40 41 42 61 65 66 0\n-62 7 33 40 41 42 65 66 0\n-14 -16 -43 0\n-16 -43 -47 0\n-18 -20 -43 0\n-20 -43 -58 0\n-12 16 51 53 0\n-44 16 51 0\n-45 16 51 53 0\n-51 12 44 45 0\n-12 20 62 64 0\n-44 20 62 0\n-45 20 62 64 0\n-62 12 44 45 0\n-17 13 38 42 45 55 0\n-56 13 42 45 0\n-21 13 38 42 45 66 0\n-67 13 42 45 0\n-47 18 62 63 0\n-58 14 51 52 0\n-50 61 0\n-53 64 0\n-54 65 0\n-65 54 0\n-55 66 0\n-66 55 0\n-68 29 36 38 56 67 0\n-69 23 46 48 49 0\n-70 25 47 51 52 0\n-71 58 62 63 0\n-72 22 32 34 35 37 39 0\n-73 57 59 60 0\n-74 33 40 41 42 44 45 0\n-75 24 26 27 28 30 31 0\n-76 43 0\n-77 68 0\n-77 69 0\n-78 70 71 0\n-79 70 0\n-79 71 0\n-81 77 0\n-80 78 0\n-81 79 0\n-82 72 0\n-82 73 0\n-83 75 76 0\n-84 75 0\n-84 76 0\n-85 74 84 0\n-86 74 0\n-85 83 0\n-86 84 0\n-87 82 86 0\n-88 82 0\n-87 85 0\n-88 86 0\n-89 80 0\n-89 81 88 0\n-89 87 0\n89 0\n-90 50 53 0\n-91 54 55 0\n-54 91 0\n-55 91 0\n-92 61 64 0\n-61 92 0\n-64 92 0\n-93 65 66 0\n-65 93 0\n-66 93 0\n-94 90 91 0\n-91 94 0\n-95 91 0\n-96 92 93 0\n-97 93 0\n-92 -93 97 0\n-98 94 97 0\n-98 95 96 0\n-94 -97 99 0\n98 0\n-99 0\n6 15 19 23 35 38 39 49 55 56 60 66 67 0\n12 16 20 30 44 45 51 53 62 64 0\n13 17 21 38 42 45 55 56 66 67 0\n"
  "242 80 0 217 214 0\n243 87 0 217 216 0\n244 78 0 242 199 0\n245 85 0 243 212 0\n246 83 0 245 208 0\n247 -97 0 238 232 236 229 220 221 181 183 225 0\n248 94 0 247 237 234 0\n249 -79 -43 0 116 113 90 87 60 196 197 186 187 104 0\n250 -58 -43 64 0 113 90 87 61 179 177 163 160 168 169 170 240 0\n251 -43 64 0 244 179 60 61 87 90 113 116 250 187 195 186 176 161 162 164 165 166 240 0\n252 -58 -93 0 247 243 233 224 251 192 205 209 210 202 201 101 103 105 106 189 107 108 119 225 120 156 188 0\n253 -29 -62 -75 0 112 111 8 10 11 15 191 0\n254 -38 -91 0 95 97 219 0\n255 -56 -91 0 98 99 219 0\n256 -67 -91 0 121 122 219 0\n257 -29 -93 0 246 247 217 252 233 224 251 192 205 209 213 215 200 197 196 198 194 203 7 8 9 10 11 15 83 253 191 187 12 86 117 186 81 82 185 0\n258 -93 0 247 248 217 233 223 224 178 179 218 228 251 192 205 209 213 215 198 193 254 255 256 257 184 94 96 219 0\n259 -65 0 258 226 0\n260 -66 0 258 227 0\n261 -54 0 259 180 0\n262 -55 0 260 182 0\n263 -91 0 262 261 219 0\n264 90 0 263 248 228 0\n265 -31 -36 0 245 243 75 70 58 50 46 38 34 33 32 13 62 192 205 209 206 210 190 201 52 188 0\n266 75 -36 0 246 245 75 70 58 50 33 203 204 192 206 66 190 0\n267 -30 0 264 85 93 218 0\n268 -36 0 267 28 29 30 31 265 266 191 0\n269 75 0 246 217 203 204 192 209 249 213 200 215 0\n270 -24 28 31 0 244 1 2 3 80 88 102 114 144 145 186 187 195 0\n271 -26 0 264 84 91 218 0\n272 -88 45 44 42 40 39 35 33 32 37 22 0 211 213 201 207 188 190 52 0\n273 45 22 44 42 40 39 35 33 32 37 0 243 245 217 272 215 200 249 192 205 209 206 210 190 201 52 188 0\n274 -95 0 263 230 0\n275 96 0 274 237 235 0\n276 92 0 275 258 231 0\n277 -33 32 35 37 39 22 0 243 21 63 188 192 201 205 210 209 0\n278 42 44 22 32 45 39 35 37 33 0 262 260 273 49 51 173 175 172 174 241 0\n279 -42 32 35 37 39 22 0 243 56 67 188 192 201 205 210 209 0\n280 42 45 22 32 33 39 35 37 0 262 260 278 68 71 173 175 172 174 241 0\n281 82 0 243 217 210 211 209 215 205 200 192 249 0\n282 72 0 281 201 0\n283 73 0 281 202 0\n284 6 23 39 35 38 0 262 260 150 151 153 154 152 155 239 0\n285 32 35 22 37 39 0 267 269 271 282 277 279 188 280 18 19 20 52 64 142 143 76 191 134 123 284 0\n286 35 37 22 39 0 285 16 17 39 284 0\n287 -45 -35 37 0 217 260 259 262 261 271 269 267 65 192 205 209 213 215 200 197 196 57 53 26 25 24 22 73 74 77 79 147 159 157 128 129 130 191 89 115 186 187 104 0\n288 -31 -35 37 39 0 245 217 259 260 287 65 192 205 209 213 215 200 197 206 57 53 26 24 23 115 135 125 127 159 190 169 187 158 110 0\n289 28 27 31 0 271 269 267 270 191 0\n290 -28 45 -74 42 41 33 0 276 69 118 190 222 109 0\n291 37 39 22 0 245 286 23 26 27 53 57 65 192 205 206 287 288 290 289 5 134 126 127 141 190 0\n292 39 22 0 291 35 36 37 40 284 0\n293 -28 0 264 276 283 92 118 218 222 100 132 133 189 0\n294 44 42 45 31 22 0 245 293 292 289 138 192 205 206 136 137 5 4 45 44 41 190 48 124 140 0\n295 42 45 31 22 0 293 289 10 292 294 68 131 146 0\n296 -42 -27 -39 0 43 42 54 59 72 148 129 0\n297 31 22 0 293 292 43 42 289 296 295 74 77 79 149 129 0\n298 -45 22 0 217 260 259 262 261 297 62 192 205 209 213 215 200 197 196 292 139 115 89 14 44 73 77 78 159 157 187 186 104 0\n299 13 42 22 0 217 268 298 297 62 192 205 209 213 215 198 193 15 292 47 173 175 184 0\n300 42 22 0 245 298 297 62 192 205 206 292 139 44 299 49 68 190 0\n301 22 0 217 297 14 62 89 115 192 205 209 213 215 200 196 197 298 300 55 72 171 167 187 186 104 0\n302 -24 0 301 2 0\n303 -27 0 301 6 0\n304 -31 0 301 13 0\n305 0 302 303 267 269 304 293 271 191 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record010
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9b15c1f26a2eb46999968da4e53a2e1b91e0f9719a5592e479d1665655558d4759354d3362d1b51d1743dd0e6358d938cd332ce4b52e2b2ac6b46f07a1d8791d4789c6785c3783d0f13c2f2709a0e9162588e07a611a4990e645515152548d1341d88d1324c3322c2b06e0741c8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6d369b6da4d349249b49349269a493692492493492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 45), (facetIndex 49), (facetIndex 71), (facetIndex 85)]))
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 50), (facetIndex 51), (facetIndex 52)])))
 (.branch 3
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 82)]))
 (.leaf ([(facetIndex 54), (facetIndex 68), (facetIndex 73)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 37), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 42)]))
 (.leaf ([(facetIndex 31), (facetIndex 57), (facetIndex 59), (facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 69)])))
 (.branch 7
 (.leaf ([(facetIndex 38), (facetIndex 58), (facetIndex 66), (facetIndex 67)]))
 (.branch 8
 (.leaf ([(facetIndex 30), (facetIndex 44), (facetIndex 46), (facetIndex 70)]))
 (.leaf ([(facetIndex 56)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "20000022030075366005550565803011100070704444640114457z1e;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 64), (facetIndex 72), (facetIndex 74)]))
 (.branch 2
 (.leaf ([(facetIndex 47), (facetIndex 88)]))
 (.leaf ([(facetIndex 36), (facetIndex 60), (facetIndex 65), (facetIndex 87)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 81)]))
 (.leaf ([(facetIndex 48), (facetIndex 53), (facetIndex 55), (facetIndex 79), (facetIndex 83)])))
 (.branch 6
 (.leaf ([(facetIndex 80), (facetIndex 84)]))
 (.leaf ([(facetIndex 86), (facetIndex 89)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "3158581d8d8000000010002000820004200000002z1b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
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
def grouped3_0009 : List Nat := [0]
def grouped3_0010 : List Nat := [0, 1, 2]
def grouped3_0012 : List Nat := [1]
def grouped3_0013 : List Nat := [1, 2]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [3]
def grouped3_0016 : List Nat := [3, 4]
def grouped3_0017 : List Nat := [3, 4, 5, 6]
def grouped3_0018 : List Nat := [4]
def grouped3_0019 : List Nat := [5]
def grouped3_0020 : List Nat := [5, 6]
def grouped3_0021 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record010" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record010" 73

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record010" "{\"ridges\":[[4,518],[13,76],[17,321],[17,324],[18,580],[21,104],[22,608],[33,518],[35,518],[37,546],[38,321],[38,324],[39,518],[39,580],[41,518],[42,518],[47,330],[53,354],[54,608],[55,834],[57,76],[59,76],[60,556],[61,76],[62,76],[62,321],[62,324],[63,76],[63,580],[65,564],[66,321],[66,324],[68,608],[69,321],[69,324],[69,580],[70,104],[72,344],[73,104],[73,608],[74,368],[79,330],[83,102],[84,834],[88,344]],\"owners\":[[4,518,[78,80,81,83,84],[33,35,37,39,41,42]],[33,518,[81,83,84],[4,35,37,39,41,42,78,80]],[35,518,[78,80,83,84],[4,33,37,39,41,42,81]],[39,518,[78,81],[4,33,35,37,41,42,80,83,84]],[41,518,[78,80,81,83,84],[4,33,35,37,39,42]],[42,518,[78,80,81,83],[4,33,35,37,39,41,84]],[37,546,[86],[11,46,51,54,78,81,83]],[13,76,[77,79,80,87,88,89],[31,57,59,61,62,63]],[57,76,[77,79,80,89],[13,31,59,61,62,63,87,88]],[59,76,[79,80,88],[13,31,57,61,62,63,77,87,89]],[61,76,[77,79,80,87,88,89],[13,31,57,59,62,63]],[62,76,[77,80,87,89],[13,31,57,59,61,63,79,88]],[63,76,[77,79,87,88],[13,31,57,59,61,62,80,89]],[17,321,[47,53,55,72,74],[38,62,66,69]],[38,321,[72,74],[17,47,53,55,62,66,69]],[62,321,[53,55,74],[17,38,47,66,69,72]],[66,321,[47,53,55],[17,38,62,69,72,74]],[69,321,[47,53,72,74],[17,38,55,62,66]],[17,324,[79,84,88],[38,62,66,69]],[38,324,[88],[17,62,66,69,79,84]],[62,324,[84],[17,38,66,69,79,88]],[66,324,[79,84],[17,38,62,69,88]],[69,324,[79,88],[17,38,62,66,84]],[18,580,[80,83,84,89],[39,63,68,69]],[39,580,[89],[18,63,68,69,80,83,84]],[63,580,[83,84],[18,39,68,69,80,89]],[69,580,[80,83,89],[18,39,63,68,84]],[21,104,[77,86,87,89],[44,59,70,73]],[70,104,[77,86,89],[21,44,59,73,87]],[73,104,[77,87],[21,44,59,70,86,89]],[22,608,[83,86,89],[54,68,73]],[54,608,[89],[22,68,73,83,86]],[68,608,[86],[22,54,73,83,89]],[73,608,[83],[22,54,68,86,89]],[83,102,[36,77],[]],[47,330,[79],[]],[79,330,[47],[]],[53,354,[],[]],[55,834,[84],[]],[84,834,[55],[]],[60,556,[78,89],[]],[65,564,[81],[]],[72,344,[88],[]],[88,344,[72],[]],[74,368,[],[]]],\"edges\":[[23,[4,18,33,35,37,39,41,42,60,63,65,68,69,78,80,81,83,84,89]],[26,[13,21,31,44,47,48,57,59,61,62,63,70,72,73,77,79,80,86,87,88,89]],[40,[17,38,47,53,55,62,66,69,72,74,79,84,88]],[41,[18,22,39,48,54,55,63,68,69,73,80,83,84,86,89]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record010" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record010\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-18,-11],[-23,-8],[-23,-17],[-23,-20],[-39,-23],[-42,-23],[-44,-7],[-44,-17],[-44,-24],[-46,-23],[-1,40,42,43,44,45],[-9,43,44,45],[-10,40,42,44,45],[-14,40,43],[-15,40,42,43,44,45],[-16,40,42,43,44],[-12,46],[-2,39,41,42,47,48,49],[-25,39,41,42,49],[-26,41,42,48],[-28,39,41,42,47,48,49],[-29,39,42,47,49],[-30,39,41,47,48],[-3,19,21,23,36,38],[-13,36,38],[-29,21,23,38],[-32,19,21,23],[-34,19,21,36,38],[-3,41,45,48],[-13,48],[-29,45],[-32,41,45],[-34,41,48],[-4,42,44,45,49],[-14,49],[-30,44,45],[-34,42,44,49],[-5,39,46,47,49],[-35,39,46,49],[-37,39,47],[-6,44,46,49],[-22,49],[-33,46],[-37,44],[-44,11,39],[-19,41],[-41,19],[-21],[-23,45],[-45,23],[-27,40,49],[-31,43],[-36,48],[-48,36],[-38],[-50,7,17,18,35],[-51,24],[-52,50,51],[-53,52],[-54,53],[-55,54],[55],[-36,56],[-19,57],[-48,57],[-47,58],[-39,59],[-40,59],[-43,59],[-20,60],[-23,60],[-41,60],[-44,60],[-42,61],[-45,61],[-46,62],[-49,62],[-58,63],[-57,63],[-63,64],[-56,64],[-56,-63,65],[-60,66],[-59,-60,67],[-62,68],[-61,68],[-61,-62,69],[-68,70],[-66,-68,71],[-66,-69,72],[-67,71],[-72,73],[-64,-71,73],[-65,-70,73],[-73],[1,4,9,10,12,14,15,16,27,30,31,33,34,40,42,43,44,45,49],[2,5,8,17,19,20,25,26,28,29,30,35,36,37,39,41,42,46,47,48,49],[3,13,19,21,23,29,32,34,36,38,41,45,48],[4,6,14,20,22,23,30,33,34,37,42,44,45,46,49]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":46,\"b\":36},{\"tag\":\"incompatible\",\"a\":55,\"b\":31},{\"tag\":\"incompatible\",\"a\":55,\"b\":44},{\"tag\":\"incompatible\",\"a\":55,\"b\":48},{\"tag\":\"incompatible\",\"a\":77,\"b\":55},{\"tag\":\"incompatible\",\"a\":80,\"b\":55},{\"tag\":\"incompatible\",\"a\":83,\"b\":30},{\"tag\":\"incompatible\",\"a\":83,\"b\":44},{\"tag\":\"incompatible\",\"a\":83,\"b\":56},{\"tag\":\"incompatible\",\"a\":86,\"b\":55},{\"tag\":\"mate\",\"ridge\":518,\"a\":4,\"owners\":[78,80,81,83,84]},{\"tag\":\"mate\",\"ridge\":518,\"a\":33,\"owners\":[81,83,84]},{\"tag\":\"mate\",\"ridge\":518,\"a\":35,\"owners\":[78,80,83,84]},{\"tag\":\"mate\",\"ridge\":518,\"a\":39,\"owners\":[78,81]},{\"tag\":\"mate\",\"ridge\":518,\"a\":41,\"owners\":[78,80,81,83,84]},{\"tag\":\"mate\",\"ridge\":518,\"a\":42,\"owners\":[78,80,81,83]},{\"tag\":\"mate\",\"ridge\":546,\"a\":37,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":76,\"a\":13,\"owners\":[77,79,80,87,88,89]},{\"tag\":\"mate\",\"ridge\":76,\"a\":57,\"owners\":[77,79,80,89]},{\"tag\":\"mate\",\"ridge\":76,\"a\":59,\"owners\":[79,80,88]},{\"tag\":\"mate\",\"ridge\":76,\"a\":61,\"owners\":[77,79,80,87,88,89]},{\"tag\":\"mate\",\"ridge\":76,\"a\":62,\"owners\":[77,80,87,89]},{\"tag\":\"mate\",\"ridge\":76,\"a\":63,\"owners\":[77,79,87,88]},{\"tag\":\"mate\",\"ridge\":321,\"a\":17,\"owners\":[47,53,55,72,74]},{\"tag\":\"mate\",\"ridge\":321,\"a\":38,\"owners\":[72,74]},{\"tag\":\"mate\",\"ridge\":321,\"a\":62,\"owners\":[53,55,74]},{\"tag\":\"mate\",\"ridge\":321,\"a\":66,\"owners\":[47,53,55]},{\"tag\":\"mate\",\"ridge\":321,\"a\":69,\"owners\":[47,53,72,74]},{\"tag\":\"mate\",\"ridge\":324,\"a\":17,\"owners\":[79,84,88]},{\"tag\":\"mate\",\"ridge\":324,\"a\":38,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":324,\"a\":62,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":324,\"a\":66,\"owners\":[79,84]},{\"tag\":\"mate\",\"ridge\":324,\"a\":69,\"owners\":[79,88]},{\"tag\":\"mate\",\"ridge\":580,\"a\":18,\"owners\":[80,83,84,89]},{\"tag\":\"mate\",\"ridge\":580,\"a\":39,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":580,\"a\":63,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":580,\"a\":69,\"owners\":[80,83,89]},{\"tag\":\"mate\",\"ridge\":104,\"a\":21,\"owners\":[77,86,87,89]},{\"tag\":\"mate\",\"ridge\":104,\"a\":70,\"owners\":[77,86,89]},{\"tag\":\"mate\",\"ridge\":104,\"a\":73,\"owners\":[77,87]},{\"tag\":\"mate\",\"ridge\":608,\"a\":22,\"owners\":[83,86,89]},{\"tag\":\"mate\",\"ridge\":608,\"a\":54,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":608,\"a\":68,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":608,\"a\":73,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":102,\"a\":83,\"owners\":[36,77]},{\"tag\":\"mate\",\"ridge\":330,\"a\":47,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":330,\"a\":79,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":354,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":834,\"a\":55,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":834,\"a\":84,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":556,\"a\":60,\"owners\":[78,89]},{\"tag\":\"mate\",\"ridge\":564,\"a\":65,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":344,\"a\":72,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":344,\"a\":88,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":368,\"a\":74,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[30,44,46,70],\"full_literals\":[-50,7,17,18,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[56],\"full_literals\":[-51,24]},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,50,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0005\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-55,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":72,\"full_literals\":[-36,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":47,\"full_literals\":[-19,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":88,\"full_literals\":[-48,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":87,\"full_literals\":[-47,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":77,\"full_literals\":[-39,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":78,\"full_literals\":[-40,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":81,\"full_literals\":[-43,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":48,\"full_literals\":[-20,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":55,\"full_literals\":[-23,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":79,\"full_literals\":[-41,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":83,\"full_literals\":[-44,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":80,\"full_literals\":[-42,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-45,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-46,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":89,\"full_literals\":[-49,62]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-60,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-62,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-68,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-66,-69,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-64,-71,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-70,73],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[4,18,33,35,37,39,41,42,60,63,65,68,69,78,80,81,83,84,89]},{\"tag\":\"edge\",\"edge\":26,\"owners\":[13,21,31,44,47,48,57,59,61,62,63,70,72,73,77,79,80,86,87,88,89]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[17,38,47,53,55,62,66,69,72,74,79,84,88]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[18,22,39,48,54,55,63,68,69,73,80,83,84,86,89]}]}"
  "p cnf 73 99\n-18 -11 0\n-23 -8 0\n-23 -17 0\n-23 -20 0\n-39 -23 0\n-42 -23 0\n-44 -7 0\n-44 -17 0\n-44 -24 0\n-46 -23 0\n-1 40 42 43 44 45 0\n-9 43 44 45 0\n-10 40 42 44 45 0\n-14 40 43 0\n-15 40 42 43 44 45 0\n-16 40 42 43 44 0\n-12 46 0\n-2 39 41 42 47 48 49 0\n-25 39 41 42 49 0\n-26 41 42 48 0\n-28 39 41 42 47 48 49 0\n-29 39 42 47 49 0\n-30 39 41 47 48 0\n-3 19 21 23 36 38 0\n-13 36 38 0\n-29 21 23 38 0\n-32 19 21 23 0\n-34 19 21 36 38 0\n-3 41 45 48 0\n-13 48 0\n-29 45 0\n-32 41 45 0\n-34 41 48 0\n-4 42 44 45 49 0\n-14 49 0\n-30 44 45 0\n-34 42 44 49 0\n-5 39 46 47 49 0\n-35 39 46 49 0\n-37 39 47 0\n-6 44 46 49 0\n-22 49 0\n-33 46 0\n-37 44 0\n-44 11 39 0\n-19 41 0\n-41 19 0\n-21 0\n-23 45 0\n-45 23 0\n-27 40 49 0\n-31 43 0\n-36 48 0\n-48 36 0\n-38 0\n-50 7 17 18 35 0\n-51 24 0\n-52 50 51 0\n-53 52 0\n-54 53 0\n-55 54 0\n55 0\n-36 56 0\n-19 57 0\n-48 57 0\n-47 58 0\n-39 59 0\n-40 59 0\n-43 59 0\n-20 60 0\n-23 60 0\n-41 60 0\n-44 60 0\n-42 61 0\n-45 61 0\n-46 62 0\n-49 62 0\n-58 63 0\n-57 63 0\n-63 64 0\n-56 64 0\n-56 -63 65 0\n-60 66 0\n-59 -60 67 0\n-62 68 0\n-61 68 0\n-61 -62 69 0\n-68 70 0\n-66 -68 71 0\n-66 -69 72 0\n-67 71 0\n-72 73 0\n-64 -71 73 0\n-65 -70 73 0\n-73 0\n1 4 9 10 12 14 15 16 27 30 31 33 34 40 42 43 44 45 49 0\n2 5 8 17 19 20 25 26 28 29 30 35 36 37 39 41 42 46 47 48 49 0\n3 13 19 21 23 29 32 34 36 38 41 45 48 0\n4 6 14 20 22 23 30 33 34 37 42 44 45 46 49 0\n"
  "100 54 0 62 61 0\n101 53 0 100 60 0\n102 52 0 101 59 0\n103 -72 0 95 92 0\n104 3 13 19 23 29 32 34 36 41 45 48 0 48 55 98 0\n105 23 64 0 55 48 80 79 64 47 81 63 28 25 65 26 50 24 27 104 0\n106 64 0 103 80 81 78 79 63 66 64 65 47 105 2 3 4 5 6 10 49 71 40 23 20 75 83 90 87 77 22 19 21 18 38 39 97 0\n107 -71 0 106 95 93 0\n108 -67 0 107 91 0\n109 41 48 45 0 53 30 49 31 33 46 29 32 104 0\n110 44 -60 0 107 108 84 68 83 89 85 77 51 76 43 17 86 75 74 69 52 14 12 34 37 16 36 11 13 15 96 0\n111 -60 0 108 107 102 83 84 89 67 85 76 77 39 110 7 8 9 45 57 1 58 56 0\n112 -20 0 111 70 0\n113 -23 0 111 71 0\n114 -41 0 111 72 0\n115 -44 0 111 73 0\n116 -45 0 113 50 0\n117 48 0 114 116 109 0\n118 -37 0 115 44 0\n119 -30 0 115 116 36 0\n120 36 0 117 54 0\n121 57 0 117 65 0\n122 56 0 120 63 0\n123 63 0 121 79 0\n124 65 0 123 122 82 0\n125 -70 0 124 95 94 0\n126 -68 0 125 88 0\n127 -62 0 126 85 0\n128 -61 0 126 86 0\n129 -46 0 127 76 0\n130 -49 0 127 77 0\n131 -42 0 128 74 0\n132 -33 0 129 43 0\n133 -14 0 130 35 0\n134 -22 0 130 42 0\n135 -6 0 130 115 129 41 0\n136 -4 0 131 115 116 130 34 0\n137 -34 0 131 115 130 37 0\n138 0 135 132 136 112 134 133 113 119 137 118 131 115 116 129 130 99 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record010
