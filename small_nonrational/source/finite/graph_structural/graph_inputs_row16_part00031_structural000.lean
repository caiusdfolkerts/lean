module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00031Data
public import GraphInputsRow16Part00031Frames
public import GraphInputsRow16Part00031Leaves
public import GraphInputsRow16Part00031Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record012
def vertexColumn : Fields := ⟨10, hexnat% "8e87a59a364d876638ce8789e17a698e479c9665596354d475a358d934cd2745d68d638cd331cd8b32e2b1ae1b26c5b0ed4731e2749c6785d1725c570de0f43e1c6188e1381e8c619616158348d1341d60d2318c3322c4b06d0721c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6d24934db69b4924924924d24924d2492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [289340865615233024, 9223374235878031360, hexnat% "100010080004000000", hexnat% "260000000000000000", 66428094503714816, hexnat% "80000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9512143252334051328, 563018706452480, hexnat% "200040100800000000", hexnat% "1e0000000004000000", 52917295621603328]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9224334089564192768, 288372215299178496, hexnat% "200040100020000000", 52917295688712192, hexnat% "1e0000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9511746588750381056, 949986636333056, 70931694231748608, hexnat% "360000000000000000", 27212912787456, hexnat% "80000000000000000", 109253230592]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record014
def vertexColumn : Fields := ⟨10, hexnat% "25c8f1aa8e87a65a3633a2e8785e0fb316a6598e479656558d68d934cd8b61d1743d68d9354e331cd8b32e2b4acab1ae1b16c3b61cc789e1745c970de0f0bc1f4c8562384e8c5318a6151560d2344d60d2344c530cc8b12c2b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db4da69b4da492493492492493492692492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "90976c6ef57000000", 2252899325313024, 61573322244096, 4647714815446351872]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "90976060d47000000", 38280596966866944, 4611712406706454528, 141020956196864, 1786706395136, 105553921572864]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5224756109889241088, 34902897179230208, hexnat% "90000000101000000", 215512868978688, 72057596051193856, 4277820981248, 44014824849408]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c3 c2
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record014_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record021
def vertexColumn : Fields := ⟨10, hexnat% "26c8f23a4e9968d87663a2e1ba1e4783e9a7198e53999695656351d58d9362d1b61d4743d8cd332cc7362d4b8ad2b86d1b0ed8731e2719e1745c570de0f43c8f0bc1f6486a2584e646318a469854958344d60c6344c930cd0b12c2b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36da6db4db4d36926d249b4924926924d2492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1effd8fb0fe61f000000", hexnat% "1000200201080000000", 40265318400, 2379026503158464512, 228698418577408, 288230376151711744]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c2 c3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c2 c4
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1effdfffffa7ff000000", 103079215104, 2305843284091600896, hexnat% "1000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1effddfff7a6ff000000", 38654705664, 9139690405888, 2305843009213693952, hexnat% "1000200000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1efff9fff7e6e3000000", 432345568522534912, 8865013825536, hexnat% "1000000000000000000", 34628173824]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ef7f8fbf7a6e2000000", hexnat% "80100000000000000", hexnat% "1000200001008000000", 9070970929152, 289356280370298880, 34695282688]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ff75ac3349480000000", hexnat% "80118000222000000", 80539226734592, 289356280370298880, 9232379236109516800, 2305986083164258304, 35903242240]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record021_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record022
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9e23c8e87a65a3663a2e8785e0fa719a6598e479c55958d68d6362d8745d0f59354e334cd8b32e2b2ae1b16c3b89e1725c570de0f43c4f0bc1f1c86a6191623a311c6291a585855158348d60c6344c530cc8b12c2b41c8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6da4d36da4d24924936924924d2692492489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 29), (facetIndex 33), (facetIndex 65), (facetIndex 67)]))
 (.leaf ([(facetIndex 26), (facetIndex 36), (facetIndex 37), (facetIndex 49), (facetIndex 56), (facetIndex 57), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 34), (facetIndex 54), (facetIndex 55)]))
 (.leaf ([(facetIndex 30), (facetIndex 51), (facetIndex 52)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 27), (facetIndex 40), (facetIndex 50), (facetIndex 59)]))
 (.leaf ([(facetIndex 31), (facetIndex 44), (facetIndex 53), (facetIndex 60)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 39), (facetIndex 41), (facetIndex 42)]))
 (.leaf ([(facetIndex 32), (facetIndex 43), (facetIndex 45), (facetIndex 46)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "10000058094ab7081fdfb4c09087ac684z13;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 38), (facetIndex 47)]))
 (.leaf ([(facetIndex 61), (facetIndex 63), (facetIndex 64)])))
 (.branch 3
 (.leaf ([(facetIndex 66), (facetIndex 69), (facetIndex 70)]))
 (.branch 4
 (.leaf ([(facetIndex 48), (facetIndex 58)]))
 (.leaf ([(facetIndex 62), (facetIndex 71)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "8900813080c0000003z24;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
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
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0016 : List Nat := [1]
def grouped3_0017 : List Nat := [2]
def grouped3_0018 : List Nat := [2, 3, 4]
def grouped3_0019 : List Nat := [3]
def grouped3_0020 : List Nat := [3, 4]
def grouped3_0021 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record022" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record022" 62

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record022" "{\"ridges\":[[13,524],[15,532],[27,7],[30,524],[34,532],[40,552],[44,560],[49,524],[50,524],[52,524],[53,532],[55,532],[57,552],[61,60],[62,92],[66,550],[70,60],[71,600]],\"owners\":[[27,7,[1,2,3,32,34],[0,28,30,31,35]],[13,524,[63,64,70],[30,49,50,52]],[30,524,[70],[13,49,50,52,63,64]],[49,524,[64],[13,30,50,52,63,70]],[50,524,[63],[13,30,49,52,64,70]],[52,524,[63,64,70],[13,30,49,50]],[15,532,[63,66,70],[34,49,53,55]],[34,532,[70],[15,49,53,55,63,66]],[53,532,[63],[15,34,49,55,66,70]],[55,532,[63,66,70],[15,34,49,53]],[40,552,[70,71],[18,50,57,59,64,69]],[57,552,[64],[18,40,50,59,69,70,71]],[44,560,[70,71],[20,53,57,60,66,69]],[66,550,[35,64],[]],[61,60,[47,70],[]],[70,60,[47,61],[]],[62,92,[48],[]],[71,600,[58],[]]],\"edges\":[[23,[13,15,30,34,35,49,50,52,53,55,63,64,66,70]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record022" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record022\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-19,-7],[-22,-19],[-23,-2],[-23,-8],[-23,-12],[-26,-23],[-27,-1],[-27,-10],[-27,-11],[-31,-19],[-32,-31],[-35,-6],[-35,-15],[-35,-16],[-35,-28],[-36,-7],[-36,-10],[-36,-22],[-36,-25],[-37,-23],[-39,-3],[-40,-35],[-41,-6],[-41,-15],[-41,-16],[-41,-28],[-41,-36],[-41,-40],[-7,1,2,3,11,13],[-4,35,36,41],[-9,41],[-21,36],[-22,35],[-24,35,36,41],[-5,35,38,41],[-13,41],[-25,35],[-27,35,38,41],[-17,41,42],[-29,36],[-18,41,42],[-38,14,36],[-33,19,41],[-41,19,33],[-34,20],[-42,30],[-43,8,12,37,39],[-44,6,15,16,21,28,29,40],[-45,13,26,27],[-46,9,23,24],[-47,7,17,22,31],[-48,10,18,25,32],[-49,43],[-49,44],[-50,45],[-50,46],[-51,49],[-51,50],[-52,47],[-52,48],[-53,52],[-54,51],[-54,53],[54],[-14,55],[-19,55],[-56,33,35,36],[-33,56],[-35,56],[-36,56],[-20,57],[-30,57],[-58,34,42],[-42,58],[-56,59],[-55,59],[-57,-58,60],[-60,61],[-59,-61,62],[-62],[4,5,9,13,14,21,22,24,25,27,35,36,38,41]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":47,\"b\":27},{\"tag\":\"incompatible\",\"a\":50,\"b\":47},{\"tag\":\"incompatible\",\"a\":51,\"b\":2},{\"tag\":\"incompatible\",\"a\":51,\"b\":29},{\"tag\":\"incompatible\",\"a\":51,\"b\":33},{\"tag\":\"incompatible\",\"a\":54,\"b\":51},{\"tag\":\"incompatible\",\"a\":55,\"b\":1},{\"tag\":\"incompatible\",\"a\":55,\"b\":31},{\"tag\":\"incompatible\",\"a\":55,\"b\":32},{\"tag\":\"incompatible\",\"a\":59,\"b\":47},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":26},{\"tag\":\"incompatible\",\"a\":63,\"b\":36},{\"tag\":\"incompatible\",\"a\":63,\"b\":37},{\"tag\":\"incompatible\",\"a\":63,\"b\":56},{\"tag\":\"incompatible\",\"a\":64,\"b\":27},{\"tag\":\"incompatible\",\"a\":64,\"b\":31},{\"tag\":\"incompatible\",\"a\":64,\"b\":50},{\"tag\":\"incompatible\",\"a\":64,\"b\":53},{\"tag\":\"incompatible\",\"a\":65,\"b\":51},{\"tag\":\"incompatible\",\"a\":67,\"b\":3},{\"tag\":\"incompatible\",\"a\":68,\"b\":63},{\"tag\":\"incompatible\",\"a\":70,\"b\":26},{\"tag\":\"incompatible\",\"a\":70,\"b\":36},{\"tag\":\"incompatible\",\"a\":70,\"b\":37},{\"tag\":\"incompatible\",\"a\":70,\"b\":56},{\"tag\":\"incompatible\",\"a\":70,\"b\":64},{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"mate\",\"ridge\":7,\"a\":27,\"owners\":[1,2,3,32,34]},{\"tag\":\"mate\",\"ridge\":524,\"a\":13,\"owners\":[63,64,70]},{\"tag\":\"mate\",\"ridge\":524,\"a\":30,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":524,\"a\":49,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":524,\"a\":50,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":524,\"a\":52,\"owners\":[63,64,70]},{\"tag\":\"mate\",\"ridge\":532,\"a\":15,\"owners\":[63,66,70]},{\"tag\":\"mate\",\"ridge\":532,\"a\":34,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":532,\"a\":53,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":532,\"a\":55,\"owners\":[63,66,70]},{\"tag\":\"mate\",\"ridge\":552,\"a\":40,\"owners\":[70,71]},{\"tag\":\"mate\",\"ridge\":552,\"a\":57,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":560,\"a\":44,\"owners\":[70,71]},{\"tag\":\"mate\",\"ridge\":550,\"a\":66,\"owners\":[35,64]},{\"tag\":\"mate\",\"ridge\":60,\"a\":61,\"owners\":[47,70]},{\"tag\":\"mate\",\"ridge\":60,\"a\":70,\"owners\":[47,61]},{\"tag\":\"mate\",\"ridge\":92,\"a\":62,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":600,\"a\":71,\"owners\":[58]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[29,33,65,67],\"full_literals\":[-43,8,12,37,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[26,36,37,49,56,57,68],\"full_literals\":[-44,6,15,16,21,28,29,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[34,54,55],\"full_literals\":[-45,13,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[30,51,52],\"full_literals\":[-46,9,23,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[27,40,50,59],\"full_literals\":[-47,7,17,22,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[31,44,53,60],\"full_literals\":[-48,10,18,25,32]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-51,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-53,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-54,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-54,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":35,\"full_literals\":[-14,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":47,\"full_literals\":[-19,55]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[61,63,64],\"full_literals\":[-56,33,35,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":61,\"full_literals\":[-33,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":63,\"full_literals\":[-35,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":64,\"full_literals\":[-36,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":48,\"full_literals\":[-20,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":58,\"full_literals\":[-30,57]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[62,71],\"full_literals\":[-58,34,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":71,\"full_literals\":[-42,58]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-59,-61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[13,15,30,34,35,49,50,52,53,55,63,64,66,70]}]}"
  "p cnf 62 81\n-19 -7 0\n-22 -19 0\n-23 -2 0\n-23 -8 0\n-23 -12 0\n-26 -23 0\n-27 -1 0\n-27 -10 0\n-27 -11 0\n-31 -19 0\n-32 -31 0\n-35 -6 0\n-35 -15 0\n-35 -16 0\n-35 -28 0\n-36 -7 0\n-36 -10 0\n-36 -22 0\n-36 -25 0\n-37 -23 0\n-39 -3 0\n-40 -35 0\n-41 -6 0\n-41 -15 0\n-41 -16 0\n-41 -28 0\n-41 -36 0\n-41 -40 0\n-7 1 2 3 11 13 0\n-4 35 36 41 0\n-9 41 0\n-21 36 0\n-22 35 0\n-24 35 36 41 0\n-5 35 38 41 0\n-13 41 0\n-25 35 0\n-27 35 38 41 0\n-17 41 42 0\n-29 36 0\n-18 41 42 0\n-38 14 36 0\n-33 19 41 0\n-41 19 33 0\n-34 20 0\n-42 30 0\n-43 8 12 37 39 0\n-44 6 15 16 21 28 29 40 0\n-45 13 26 27 0\n-46 9 23 24 0\n-47 7 17 22 31 0\n-48 10 18 25 32 0\n-49 43 0\n-49 44 0\n-50 45 0\n-50 46 0\n-51 49 0\n-51 50 0\n-52 47 0\n-52 48 0\n-53 52 0\n-54 51 0\n-54 53 0\n54 0\n-14 55 0\n-19 55 0\n-56 33 35 36 0\n-33 56 0\n-35 56 0\n-36 56 0\n-20 57 0\n-30 57 0\n-58 34 42 0\n-42 58 0\n-56 59 0\n-55 59 0\n-57 -58 60 0\n-60 61 0\n-59 -61 62 0\n-62 0\n4 5 9 13 14 21 22 24 25 27 35 36 38 41 0\n"
  "82 51 0 64 62 0\n83 53 0 64 63 0\n84 49 0 82 57 0\n85 50 0 82 58 0\n86 52 0 83 61 0\n87 43 0 84 53 0\n88 44 0 84 54 0\n89 45 0 85 55 0\n90 46 0 85 56 0\n91 47 0 86 59 0\n92 48 0 86 60 0\n93 59 0 75 76 68 69 70 65 66 44 33 37 32 42 31 36 30 34 35 38 81 0\n94 -61 0 93 80 79 0\n95 -60 0 94 78 0\n96 -58 0 95 77 71 72 45 46 73 0\n97 -42 0 96 74 0\n98 -41 15 36 0 88 40 32 23 25 26 28 48 0\n99 -41 36 0 24 98 0\n100 56 0 97 90 87 89 92 91 69 70 33 37 99 31 36 39 41 34 50 3 4 5 6 20 47 49 21 7 8 9 52 29 11 51 0\n101 36 33 0 100 88 32 40 67 12 13 14 15 22 48 0\n102 41 19 0 97 91 92 39 41 43 101 16 17 18 19 51 52 11 0\n103 -41 0 27 99 0\n104 -17 0 103 97 39 0\n105 19 0 103 102 0\n106 -7 0 105 1 0\n107 -22 0 105 2 0\n108 -31 0 105 10 0\n109 0 106 108 91 104 107 51 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record024
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "26c8f23a65a361d98e33a2e1ba1e0fa698e665c55958d475a358d934cd8b46d8743d64e334cc7362ccb8acab86c3b51cc789c6785c9715c3783d0f0bc1f1a9864588e13a318a469616154560d2344d60c6344c3322c4b0ad0721c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db4da4d3693493492493492492692692492489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.branch 2
 (.leaf ([(facetIndex 1)]))
 (.leaf ([(facetIndex 2)]))))
 (.branch 4
 (.leaf ([(facetIndex 3)]))
 (.branch 5
 (.leaf ([(facetIndex 4)]))
 (.leaf ([(facetIndex 5)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 6)]))
 (.branch 8
 (.leaf ([(facetIndex 7)]))
 (.leaf ([(facetIndex 8)]))))
 (.branch 11
 (.branch 10
 (.leaf ([(facetIndex 9)]))
 (.leaf ([(facetIndex 10)])))
 (.branch 12
 (.leaf ([(facetIndex 11)]))
 (.leaf ([(facetIndex 12)]))))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ([(facetIndex 13)]))
 (.branch 15
 (.leaf ([(facetIndex 14)]))
 (.leaf ([(facetIndex 15)]))))
 (.branch 17
 (.leaf ([(facetIndex 16)]))
 (.branch 18
 (.leaf ([(facetIndex 17)]))
 (.leaf ([(facetIndex 18)])))))
 (.branch 22
 (.branch 20
 (.leaf ([(facetIndex 19)]))
 (.branch 21
 (.leaf ([(facetIndex 20)]))
 (.leaf ([(facetIndex 21)]))))
 (.branch 24
 (.branch 23
 (.leaf ([(facetIndex 22)]))
 (.leaf ([(facetIndex 23)])))
 (.branch 25
 (.leaf ([(facetIndex 24)]))
 (.leaf ([(facetIndex 25)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "338bdab49ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 26
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 32), (facetIndex 68), (facetIndex 71)]))
 (.leaf ([(facetIndex 33), (facetIndex 49), (facetIndex 57), (facetIndex 59)])))
 (.branch 3
 (.leaf ([(facetIndex 38), (facetIndex 41), (facetIndex 61), (facetIndex 62)]))
 (.branch 4
 (.leaf ([(facetIndex 27), (facetIndex 42), (facetIndex 65), (facetIndex 67)]))
 (.leaf ([(facetIndex 40), (facetIndex 43)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 30), (facetIndex 44), (facetIndex 45), (facetIndex 46)]))
 (.leaf ([(facetIndex 29), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55)])))
 (.branch 8
 (.leaf ([(facetIndex 26), (facetIndex 31), (facetIndex 34), (facetIndex 36), (facetIndex 37)]))
 (.branch 9
 (.leaf ([(facetIndex 47), (facetIndex 58)]))
 (.leaf ([(facetIndex 50), (facetIndex 51)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "303002201810666699108555432402770710756037z1a;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 39), (facetIndex 48)]))
 (.leaf ([(facetIndex 63), (facetIndex 64), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 70), (facetIndex 72), (facetIndex 73)]))
 (.branch 4
 (.leaf ([(facetIndex 56), (facetIndex 60)]))
 (.leaf ([(facetIndex 69), (facetIndex 74)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1120a0041203003z2a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0]
def grouped1_0001 : List Nat := [0, 1, 2]
def grouped1_0002 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped1_0003 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
def grouped1_0005 : List Nat := [1]
def grouped1_0006 : List Nat := [1, 2]
def grouped1_0007 : List Nat := [2]
def grouped1_0008 : List Nat := [3, 4, 5]
def grouped1_0009 : List Nat := [6, 7, 8]
def grouped1_0010 : List Nat := [6, 7, 8, 9, 10, 11, 12]
def grouped1_0011 : List Nat := [9]
def grouped1_0012 : List Nat := [9, 10]
def grouped1_0013 : List Nat := [9, 10, 11, 12]
def grouped1_0014 : List Nat := [10]
def grouped1_0015 : List Nat := [11]
def grouped1_0016 : List Nat := [11, 12]
def grouped1_0017 : List Nat := [12]
def grouped1_0018 : List Nat := [13, 14, 15]
def grouped1_0019 : List Nat := [13, 14, 15, 16, 17, 18]
def grouped1_0020 : List Nat := [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
def grouped1_0021 : List Nat := [16]
def grouped1_0022 : List Nat := [16, 17, 18]
def grouped1_0023 : List Nat := [17]
def grouped1_0024 : List Nat := [17, 18]
def grouped1_0025 : List Nat := [18]
def grouped1_0026 : List Nat := [19]
def grouped1_0027 : List Nat := [19, 20, 21]
def grouped1_0028 : List Nat := [19, 20, 21, 22, 23, 24, 25]
def grouped1_0029 : List Nat := [20]
def grouped1_0030 : List Nat := [20, 21]
def grouped1_0031 : List Nat := [21]
def grouped1_0032 : List Nat := [22, 23]
def grouped1_0033 : List Nat := [22, 23, 24, 25]
def grouped1_0034 : List Nat := [24]
def grouped1_0035 : List Nat := [24, 25]
def grouped1_0036 : List Nat := [25]
def grouped2_0037 : List Nat := [0, 1]
def grouped2_0038 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0040 : List Nat := [2]
def grouped2_0041 : List Nat := [2, 3, 4]
def grouped2_0042 : List Nat := [3]
def grouped2_0043 : List Nat := [3, 4]
def grouped2_0044 : List Nat := [4]
def grouped2_0045 : List Nat := [5]
def grouped2_0046 : List Nat := [5, 6]
def grouped2_0047 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0048 : List Nat := [6]
def grouped2_0049 : List Nat := [7]
def grouped2_0050 : List Nat := [7, 8, 9]
def grouped2_0051 : List Nat := [8]
def grouped2_0052 : List Nat := [8, 9]
def grouped2_0053 : List Nat := [9]
def grouped3_0054 : List Nat := [0]
def grouped3_0055 : List Nat := [0, 1]
def grouped3_0057 : List Nat := [1]
def grouped3_0058 : List Nat := [2]
def grouped3_0059 : List Nat := [2, 3, 4]
def grouped3_0060 : List Nat := [3]
def grouped3_0061 : List Nat := [3, 4]
def grouped3_0062 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record024" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"kind\":1,\"index\":2},{\"tag\":\"group\",\"kind\":1,\"index\":10},{\"tag\":\"group\",\"kind\":1,\"index\":12},{\"tag\":\"group\",\"kind\":1,\"index\":18},{\"tag\":\"group\",\"kind\":1,\"index\":21},{\"tag\":\"group\",\"kind\":1,\"index\":25},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0006\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0024\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0030\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0027\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0033\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0028\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0020\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0020\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0043\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0043\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0041\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0041\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0041\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0038\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0038\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0038\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0046\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0046\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0050\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0050\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0055\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0055\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0061\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0061\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0059\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0059\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record024" 130

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record024" "{\"ridges\":[[0,14],[2,69],[2,70],[5,42],[7,11],[7,137],[8,49],[10,97],[12,13],[12,76],[13,13],[13,140],[14,13],[14,524],[16,532],[19,521],[19,552],[20,560],[21,14],[21,70],[21,76],[22,14],[22,140],[25,42],[28,14],[29,14],[29,524],[30,50],[31,69],[33,532],[34,70],[34,98],[35,550],[36,69],[37,69],[38,50],[40,42],[40,137],[41,42],[41,552],[42,137],[43,11],[43,137],[44,49],[44,50],[44,98],[45,49],[45,50],[46,50],[46,560],[48,13],[49,524],[49,532],[50,76],[50,104],[51,13],[51,524],[51,552],[52,140],[53,524],[54,13],[54,140],[55,140],[55,524],[56,116],[57,532],[57,560],[59,532],[60,612],[61,521],[61,552],[61,560],[62,104],[62,521],[62,552],[63,14],[63,42],[63,60],[64,14],[64,524],[65,14],[65,42],[66,524],[68,14],[68,140],[69,116],[70,550],[72,42],[72,538],[72,552],[73,60],[73,524],[74,612]],\"owners\":[[7,11,[0,5,6,26,28,29,38,39,41],[43]],[43,11,[0,5,6,26,29,38,39,41],[7,28]],[2,69,[12,50,52,53,56,60],[31,34,36,37]],[31,69,[12,50,52,53,60],[2,34,36,37,56]],[36,69,[12,50,53,56,60],[2,31,34,37,52]],[37,69,[12,50,52,53,56,60],[2,31,34,36]],[2,70,[21,65,67,69],[31,34,36,37]],[21,70,[2,31,34,36,37,69],[65,67]],[34,70,[21,67],[2,31,36,37,65,69]],[7,137,[13,52,54,55],[40,42,43]],[40,137,[13,52,54,55],[7,42,43]],[42,137,[13,54,55],[7,40,43,52]],[43,137,[13,52,55],[7,40,42,54]],[8,49,[20,48,56,57,61],[30,38,44,45]],[44,49,[20,48,57,61],[8,30,38,45,56]],[45,49,[20,48,56,57,61],[8,30,38,44]],[30,50,[72],[8,38,44,45,46,63,69,70]],[38,50,[69,70],[8,30,44,45,46,63,72]],[44,50,[63,70,72],[8,30,38,45,46,69]],[45,50,[63,69,70,72],[8,30,38,44,46]],[46,50,[63,69],[8,30,38,44,45,70,72]],[10,97,[18,50,56,60,62],[34,44]],[34,98,[25],[10,44,65,69]],[44,98,[25,65],[10,34,69]],[12,76,[21,65,67,74],[50,52,53]],[21,76,[12,50,52,53,74],[65,67]],[50,76,[21,67],[12,52,53,65,74]],[13,140,[22,67,68],[52,54,55]],[22,140,[13,52,54,55],[67,68]],[52,140,[22,68],[13,54,55,67]],[54,140,[22,67],[13,52,55,68]],[55,140,[22,67,68],[13,52,54]],[68,140,[13,52,55],[22,54,67]],[19,521,[14,29,39,49,53,55],[41,61,62]],[61,521,[14,29,53,55],[19,39,41,49,62]],[62,521,[14,29,39,49,55],[19,41,53,61]],[14,524,[64,66,73,74],[29,49,51,53,55]],[29,524,[73,74],[14,49,51,53,55,64,66]],[49,524,[66,74],[14,29,51,53,55,64,73]],[51,524,[64],[14,29,49,53,55,66,73,74]],[53,524,[64,66,73],[14,29,49,51,55,74]],[55,524,[64,66,73,74],[14,29,49,51,53]],[64,524,[14,51,53,55,74],[29,49,66,73]],[66,524,[14,49,53,55],[29,51,64,73,74]],[73,524,[14,29,53,55],[49,51,64,66,74]],[16,532,[64,70,73],[33,49,57,59]],[33,532,[73],[16,49,57,59,64,70]],[49,532,[70],[16,33,57,59,64,73]],[57,532,[64],[16,33,49,59,70,73]],[59,532,[64,70,73],[16,33,49,57]],[50,104,[25],[18,62,65,74]],[62,104,[25,65],[18,50,74]],[19,552,[66,72,73,74],[41,51,61,62]],[41,552,[73,74],[19,51,61,62,66,72]],[51,552,[72],[19,41,61,62,66,73,74]],[61,552,[66,74],[19,41,51,62,72,73]],[62,552,[66,72,73],[19,41,51,61,74]],[72,552,[19,51,62,74],[41,61,66,73]],[20,560,[70,72,73],[46,57,61]],[46,560,[73],[20,57,61,70,72]],[57,560,[72],[20,46,61,70,73]],[61,560,[70],[20,46,57,72,73]],[35,550,[66,70],[]],[70,550,[35,66],[]],[72,538,[39,64],[]],[63,60,[48,73],[]],[73,60,[48,63],[]],[56,116,[69],[]],[69,116,[56],[]],[60,612,[74],[]],[74,612,[60],[]]],\"edges\":[[20,[2,12,21,31,34,36,37,50,52,53,56,60,65,67,69,74]],[23,[14,16,29,33,35,49,51,53,55,57,59,60,64,66,70,73,74]],[27,[7,13,22,40,42,43,52,54,55,67,68]],[29,[14,19,29,39,41,49,51,53,55,61,62,64,66,72,73,74]],[30,[8,20,30,38,44,45,46,48,56,57,61,63,69,70,72,73]],[34,[16,20,33,39,46,49,57,59,61,64,70,72,73]],[35,[10,18,25,34,44,50,56,60,62,65,69,74]],[38,[19,20,35,41,46,51,57,60,61,62,66,70,72,73,74]]],\"groupings\":[1,2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record024" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record024\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-21,-8],[-23,-19],[-23,-21],[-23,-22],[-25,-4],[-25,-18],[-25,-20],[-27,-19],[-27,-21],[-28,-19],[-28,-21],[-29,-25],[-32,-12],[-33,-25],[-33,-27],[-33,-31],[-34,-27],[-34,-33],[-35,-23],[-35,-32],[-36,-23],[-38,-28],[-39,-21],[-41,-4],[-41,-19],[-41,-21],[-41,-26],[-41,-33],[-43,-10],[-43,-21],[-43,-39],[-43,-40],[-43,-42],[-44,-9],[-44,-39],[-44,-41],[-44,-43],[-45,-27],[-45,-44],[-46,-8],[-46,-39],[-46,-41],[-46,-43],[-46,-44],[-49,-28],[-53,-41],[-53,-44],[-55,-18],[-56,-4],[-56,-33],[-57,-25],[-57,-39],[-57,-41],[-57,-54],[-57,-56],[-58,-54],[-58,-55],[-58,-57],[-61,-25],[-61,-30],[-61,-41],[-61,-56],[-62,-61],[-63,-19],[-63,-22],[-63,-25],[-63,-29],[-63,-41],[-63,-42],[-63,-52],[-63,-56],[-63,-61],[-63,-62],[-5,1,3,4,18,20,21,29,30,32],[-34,1,3,4,18,21,29,30,32],[-8,-9,-42],[-8,-10,-45],[-8,-42,-45],[-10,-39,-45],[-1,-15,-55],[-1,-55,-56],[-15,-16,-54],[-15,-16,-55],[-15,-21,-54],[-15,-55,-59],[-16,-55,-56],[-20,-55,-56],[-55,-56,-59],[-2,8,41,43,44,47,51],[-23,8,41,43,44,51],[-27,8,41,44,47,51],[-28,8,41,43,44,47,51],[-2,15,56,58,60],[-15,2,23,25,27,28,60],[-25,15,58],[-3,-17,-62],[-3,-56,-62],[-17,-31,-62],[-17,-32,-54],[-31,-56,-62],[-5,9,43,45,46],[-31,9,43,45,46],[-33,9,45,46],[-34,9,43,46],[-6,14,39,47,48,52],[-35,14,39,48,52],[-36,14,39,47,48,52],[-22,62],[-29,60,61],[-35,54,61,62],[-36,54,60,61,62],[-37,54,60],[-7,12,41,47,51,53],[-25,17],[-35,17,56],[-8,15,56,58,64],[-15,8,41,43,44,64],[-41,15,58],[-9,16,58,59],[-16,9,43,45,46],[-43,16,59],[-45,16,58],[-46,16,58,59],[-59,9,43,46],[-13,10,21,30,40,44,46],[-52,10,21,44,46],[-53,10,21,30,40,46],[-10,55,57,63,64],[-21,63,64],[-40,57,64],[-42,55],[-44,55,57,63],[-46,55,57,63,64],[-55,10,42,44,46,64],[-57,10,40,44,46],[-63,10,21,44,46],[-11,55,61,63],[-24,63],[-40,61],[-48,55],[-50,55,61,63],[-41,17],[-53,17,56],[-13,57,62,63,64],[-32,63,64],[-42,62],[-52,57,64],[-53,57,62,63],[-62,13,42,53,64],[-14,61,62,63],[-37,63],[-48,62],[-52,61],[-26,57,61],[-61,26,57],[-62,30,55],[-54,39,63],[-63,39,54],[-47,60],[-60,47],[-51,64],[-64,51],[-2,65],[-7,66],[-8,67],[-12,68],[-15,69],[-17,70],[-65,71],[-71,72],[-72,73],[-66,74],[-67,75],[-75,76],[-74,-75,77],[-76,78],[-77,79],[-73,-78,80],[-73,-79,81],[-68,82],[-82,83],[-83,84],[-69,85],[-85,86],[-70,87],[-87,88],[-86,89],[-86,-88,90],[-89,91],[-90,92],[-84,-89,92],[-80,-92,93],[-81,-91,93],[-93],[-94,29,32,52,53],[-95,19,33,56,58],[-96,31,34],[-97,22,35,36,37],[-98,21,43,44,45,46],[-99,38,49],[-100,41,42],[-101,95,96],[-102,95],[-102,96],[-103,94,101],[-104,94,102],[-104,101],[-105,102],[-106,103],[-107,104],[-108,105],[-109,97,98],[-110,97],[-110,98],[-111,99,100],[-112,99],[-112,100],[-113,111],[-114,112],[-115,109,114],[-116,109],[-116,110,114],[-117,110],[-116,113],[-117,114],[-118,106],[-118,107,117],[-118,108,116],[-118,115],[118],[-26,119],[-30,119],[-39,119],[-120,54,55,57],[-54,120],[-55,120],[-57,120],[-121,61,62,63],[-61,121],[-62,121],[-63,121],[-122,47,51],[-47,122],[-51,122],[-123,60,64],[-60,123],[-64,123],[-120,124],[-119,124],[-119,-120,125],[-126,122,123],[-122,-123,127],[-128,121,126],[-127,129],[-121,128],[-124,-129,130],[-125,-128,130],[-130],[2,8,15,23,25,27,28,41,43,44,47,51,56,58,60,64],[10,11,21,24,26,40,42,44,46,48,50,51,55,57,61,63,64],[5,9,16,31,33,34,43,45,46,58,59],[10,13,21,30,32,40,42,44,46,52,53,55,57,62,63,64],[6,14,22,29,35,36,37,39,47,48,52,54,60,61,62,63],[11,14,24,30,37,40,48,50,52,55,61,62,63],[7,12,17,25,35,41,47,51,53,56,60,64],[13,14,26,32,37,42,48,51,52,53,57,61,62,63,64]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"index\":2,\"kind\":1},{\"tag\":\"group\",\"index\":10,\"kind\":1},{\"tag\":\"group\",\"index\":12,\"kind\":1},{\"tag\":\"group\",\"index\":18,\"kind\":1},{\"tag\":\"group\",\"index\":21,\"kind\":1},{\"tag\":\"group\",\"index\":25,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":29,\"b\":12},{\"tag\":\"incompatible\",\"a\":31,\"b\":27},{\"tag\":\"incompatible\",\"a\":31,\"b\":29},{\"tag\":\"incompatible\",\"a\":31,\"b\":30},{\"tag\":\"incompatible\",\"a\":34,\"b\":6},{\"tag\":\"incompatible\",\"a\":34,\"b\":26},{\"tag\":\"incompatible\",\"a\":34,\"b\":28},{\"tag\":\"incompatible\",\"a\":36,\"b\":27},{\"tag\":\"incompatible\",\"a\":36,\"b\":29},{\"tag\":\"incompatible\",\"a\":37,\"b\":27},{\"tag\":\"incompatible\",\"a\":37,\"b\":29},{\"tag\":\"incompatible\",\"a\":38,\"b\":34},{\"tag\":\"incompatible\",\"a\":41,\"b\":18},{\"tag\":\"incompatible\",\"a\":42,\"b\":34},{\"tag\":\"incompatible\",\"a\":42,\"b\":36},{\"tag\":\"incompatible\",\"a\":42,\"b\":40},{\"tag\":\"incompatible\",\"a\":43,\"b\":36},{\"tag\":\"incompatible\",\"a\":43,\"b\":42},{\"tag\":\"incompatible\",\"a\":44,\"b\":31},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":45,\"b\":31},{\"tag\":\"incompatible\",\"a\":47,\"b\":37},{\"tag\":\"incompatible\",\"a\":48,\"b\":29},{\"tag\":\"incompatible\",\"a\":50,\"b\":6},{\"tag\":\"incompatible\",\"a\":50,\"b\":27},{\"tag\":\"incompatible\",\"a\":50,\"b\":29},{\"tag\":\"incompatible\",\"a\":50,\"b\":35},{\"tag\":\"incompatible\",\"a\":50,\"b\":42},{\"tag\":\"incompatible\",\"a\":52,\"b\":14},{\"tag\":\"incompatible\",\"a\":52,\"b\":29},{\"tag\":\"incompatible\",\"a\":52,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":13},{\"tag\":\"incompatible\",\"a\":53,\"b\":48},{\"tag\":\"incompatible\",\"a\":53,\"b\":50},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":36},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":55,\"b\":12},{\"tag\":\"incompatible\",\"a\":55,\"b\":48},{\"tag\":\"incompatible\",\"a\":55,\"b\":50},{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":55,\"b\":53},{\"tag\":\"incompatible\",\"a\":58,\"b\":37},{\"tag\":\"incompatible\",\"a\":62,\"b\":50},{\"tag\":\"incompatible\",\"a\":62,\"b\":53},{\"tag\":\"incompatible\",\"a\":64,\"b\":26},{\"tag\":\"incompatible\",\"a\":65,\"b\":6},{\"tag\":\"incompatible\",\"a\":65,\"b\":42},{\"tag\":\"incompatible\",\"a\":66,\"b\":34},{\"tag\":\"incompatible\",\"a\":66,\"b\":48},{\"tag\":\"incompatible\",\"a\":66,\"b\":50},{\"tag\":\"incompatible\",\"a\":66,\"b\":63},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":63},{\"tag\":\"incompatible\",\"a\":67,\"b\":64},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":34},{\"tag\":\"incompatible\",\"a\":70,\"b\":39},{\"tag\":\"incompatible\",\"a\":70,\"b\":50},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":72,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":27},{\"tag\":\"incompatible\",\"a\":73,\"b\":30},{\"tag\":\"incompatible\",\"a\":73,\"b\":34},{\"tag\":\"incompatible\",\"a\":73,\"b\":38},{\"tag\":\"incompatible\",\"a\":73,\"b\":50},{\"tag\":\"incompatible\",\"a\":73,\"b\":51},{\"tag\":\"incompatible\",\"a\":73,\"b\":61},{\"tag\":\"incompatible\",\"a\":73,\"b\":65},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"mate\",\"ridge\":11,\"a\":7,\"owners\":[0,5,6,26,28,29,38,39,41]},{\"tag\":\"mate\",\"ridge\":11,\"a\":43,\"owners\":[0,5,6,26,29,38,39,41]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[12,13,51]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[12,14,54]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[12,51,54]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[14,48,54]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[0,21,64]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[0,64,65]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[21,22,63]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[21,22,64]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[21,29,63]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[21,64,68]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[22,64,65]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[28,64,65]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[64,65,68]},{\"tag\":\"mate\",\"ridge\":69,\"a\":2,\"owners\":[12,50,52,53,56,60]},{\"tag\":\"mate\",\"ridge\":69,\"a\":31,\"owners\":[12,50,52,53,60]},{\"tag\":\"mate\",\"ridge\":69,\"a\":36,\"owners\":[12,50,53,56,60]},{\"tag\":\"mate\",\"ridge\":69,\"a\":37,\"owners\":[12,50,52,53,56,60]},{\"tag\":\"mate\",\"ridge\":70,\"a\":2,\"owners\":[21,65,67,69]},{\"tag\":\"mate\",\"ridge\":70,\"a\":21,\"owners\":[2,31,34,36,37,69]},{\"tag\":\"mate\",\"ridge\":70,\"a\":34,\"owners\":[21,67]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[5,25,72]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[5,65,72]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[25,40,72]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[25,41,63]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[40,65,72]},{\"tag\":\"mate\",\"ridge\":137,\"a\":7,\"owners\":[13,52,54,55]},{\"tag\":\"mate\",\"ridge\":137,\"a\":40,\"owners\":[13,52,54,55]},{\"tag\":\"mate\",\"ridge\":137,\"a\":42,\"owners\":[13,54,55]},{\"tag\":\"mate\",\"ridge\":137,\"a\":43,\"owners\":[13,52,55]},{\"tag\":\"mate\",\"ridge\":49,\"a\":8,\"owners\":[20,48,56,57,61]},{\"tag\":\"mate\",\"ridge\":49,\"a\":44,\"owners\":[20,48,57,61]},{\"tag\":\"mate\",\"ridge\":49,\"a\":45,\"owners\":[20,48,56,57,61]},{\"tag\":\"mate\",\"ridge\":50,\"a\":30,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":50,\"a\":38,\"owners\":[69,70]},{\"tag\":\"mate\",\"ridge\":50,\"a\":44,\"owners\":[63,70,72]},{\"tag\":\"mate\",\"ridge\":50,\"a\":45,\"owners\":[63,69,70,72]},{\"tag\":\"mate\",\"ridge\":50,\"a\":46,\"owners\":[63,69]},{\"tag\":\"mate\",\"ridge\":97,\"a\":10,\"owners\":[18,50,56,60,62]},{\"tag\":\"mate\",\"ridge\":98,\"a\":34,\"owners\":[25]},{\"tag\":\"mate\",\"ridge\":98,\"a\":44,\"owners\":[25,65]},{\"tag\":\"mate\",\"ridge\":76,\"a\":12,\"owners\":[21,65,67,74]},{\"tag\":\"mate\",\"ridge\":76,\"a\":21,\"owners\":[12,50,52,53,74]},{\"tag\":\"mate\",\"ridge\":76,\"a\":50,\"owners\":[21,67]},{\"tag\":\"mate\",\"ridge\":140,\"a\":13,\"owners\":[22,67,68]},{\"tag\":\"mate\",\"ridge\":140,\"a\":22,\"owners\":[13,52,54,55]},{\"tag\":\"mate\",\"ridge\":140,\"a\":52,\"owners\":[22,68]},{\"tag\":\"mate\",\"ridge\":140,\"a\":54,\"owners\":[22,67]},{\"tag\":\"mate\",\"ridge\":140,\"a\":55,\"owners\":[22,67,68]},{\"tag\":\"mate\",\"ridge\":140,\"a\":68,\"owners\":[13,52,55]},{\"tag\":\"mate\",\"ridge\":521,\"a\":19,\"owners\":[14,29,39,49,53,55]},{\"tag\":\"mate\",\"ridge\":521,\"a\":61,\"owners\":[14,29,53,55]},{\"tag\":\"mate\",\"ridge\":521,\"a\":62,\"owners\":[14,29,39,49,55]},{\"tag\":\"mate\",\"ridge\":524,\"a\":14,\"owners\":[64,66,73,74]},{\"tag\":\"mate\",\"ridge\":524,\"a\":29,\"owners\":[73,74]},{\"tag\":\"mate\",\"ridge\":524,\"a\":49,\"owners\":[66,74]},{\"tag\":\"mate\",\"ridge\":524,\"a\":51,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":524,\"a\":53,\"owners\":[64,66,73]},{\"tag\":\"mate\",\"ridge\":524,\"a\":55,\"owners\":[64,66,73,74]},{\"tag\":\"mate\",\"ridge\":524,\"a\":64,\"owners\":[14,51,53,55,74]},{\"tag\":\"mate\",\"ridge\":524,\"a\":66,\"owners\":[14,49,53,55]},{\"tag\":\"mate\",\"ridge\":524,\"a\":73,\"owners\":[14,29,53,55]},{\"tag\":\"mate\",\"ridge\":532,\"a\":16,\"owners\":[64,70,73]},{\"tag\":\"mate\",\"ridge\":532,\"a\":33,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":532,\"a\":49,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":532,\"a\":57,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":532,\"a\":59,\"owners\":[64,70,73]},{\"tag\":\"mate\",\"ridge\":104,\"a\":50,\"owners\":[25]},{\"tag\":\"mate\",\"ridge\":104,\"a\":62,\"owners\":[25,65]},{\"tag\":\"mate\",\"ridge\":552,\"a\":19,\"owners\":[66,72,73,74]},{\"tag\":\"mate\",\"ridge\":552,\"a\":41,\"owners\":[73,74]},{\"tag\":\"mate\",\"ridge\":552,\"a\":51,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":552,\"a\":61,\"owners\":[66,74]},{\"tag\":\"mate\",\"ridge\":552,\"a\":62,\"owners\":[66,72,73]},{\"tag\":\"mate\",\"ridge\":552,\"a\":72,\"owners\":[19,51,62,74]},{\"tag\":\"mate\",\"ridge\":560,\"a\":20,\"owners\":[70,72,73]},{\"tag\":\"mate\",\"ridge\":560,\"a\":46,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":560,\"a\":57,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":560,\"a\":61,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":550,\"a\":35,\"owners\":[66,70]},{\"tag\":\"mate\",\"ridge\":550,\"a\":70,\"owners\":[35,66]},{\"tag\":\"mate\",\"ridge\":538,\"a\":72,\"owners\":[39,64]},{\"tag\":\"mate\",\"ridge\":60,\"a\":63,\"owners\":[48,73]},{\"tag\":\"mate\",\"ridge\":60,\"a\":73,\"owners\":[48,63]},{\"tag\":\"mate\",\"ridge\":116,\"a\":56,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":116,\"a\":69,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":612,\"a\":60,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":612,\"a\":74,\"owners\":[60]},{\"tag\":\"group_take\",\"kind\":1,\"index\":2,\"member\":2,\"full_literals\":[-2,65]},{\"tag\":\"group_take\",\"kind\":1,\"index\":10,\"member\":10,\"full_literals\":[-7,66]},{\"tag\":\"group_take\",\"kind\":1,\"index\":12,\"member\":12,\"full_literals\":[-8,67]},{\"tag\":\"group_take\",\"kind\":1,\"index\":18,\"member\":18,\"full_literals\":[-12,68]},{\"tag\":\"group_take\",\"kind\":1,\"index\":21,\"member\":21,\"full_literals\":[-15,69]},{\"tag\":\"group_take\",\"kind\":1,\"index\":25,\"member\":25,\"full_literals\":[-17,70]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped1_0005\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,71],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,72],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,73],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,74],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11],\"right\":[12],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,75],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,76],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-74,-75,77],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-76,78],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11,12],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-77,79],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-73,-78,80],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11,12],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-73,-79,81],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18],\"left_name\":\"grouped1_0023\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,82],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16],\"right\":[17,18],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-82,83],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15],\"right\":[16,17,18],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,84],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21],\"left_name\":\"grouped1_0029\",\"right_name\":\"grouped1_0031\",\"joined_name\":\"grouped1_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,85],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[19],\"right\":[20,21],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0027\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-85,86],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24],\"right\":[25],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0035\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,87],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[22,23],\"right\":[24,25],\"left_name\":\"grouped1_0032\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0033\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,88],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[19,20,21],\"right\":[22,23,24,25],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-86,false,89],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[19,20,21],\"right\":[22,23,24,25],\"left_name\":\"grouped1_0027\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-86,-88,90],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15,16,17,18],\"right\":[19,20,21,22,23,24,25],\"left_name\":\"grouped1_0019\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-89,91],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15,16,17,18],\"right\":[19,20,21,22,23,24,25],\"left_name\":\"grouped1_0019\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0020\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-90,92],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[13,14,15,16,17,18],\"right\":[19,20,21,22,23,24,25],\"left_name\":\"grouped1_0019\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-84,-89,92],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12],\"right\":[13,14,15,16,17,18,19,20,21,22,23,24,25],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-80,-92,93],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12],\"right\":[13,14,15,16,17,18,19,20,21,22,23,24,25],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"groupKind1\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-81,-91,93],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":3,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[38,41,61,62],\"full_literals\":[-94,29,32,52,53]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[27,42,65,67],\"full_literals\":[-95,19,33,56,58]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[40,43],\"full_literals\":[-96,31,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[30,44,45,46],\"full_literals\":[-97,22,35,36,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[29,52,53,54,55],\"full_literals\":[-98,21,43,44,45,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[47,58],\"full_literals\":[-99,38,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[50,51],\"full_literals\":[-100,41,42]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0044\",\"joined_name\":\"grouped2_0043\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-101,95,96],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0044\",\"joined_name\":\"grouped2_0043\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-102,95,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0044\",\"joined_name\":\"grouped2_0043\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-102,false,96],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0041\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-103,94,101],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0041\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-104,94,102],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0041\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-104,false,101],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0041\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-105,false,102],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0037\",\"right_name\":\"grouped2_0041\",\"joined_name\":\"grouped2_0038\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-106,false,103],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0037\",\"right_name\":\"grouped2_0041\",\"joined_name\":\"grouped2_0038\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-107,false,104],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0037\",\"right_name\":\"grouped2_0041\",\"joined_name\":\"grouped2_0038\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-108,false,105],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0046\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-109,97,98],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0046\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-110,97,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0046\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-110,false,98],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-111,99,100],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-112,99,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0052\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-112,false,100],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-113,false,111],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-114,false,112],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-115,109,114],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-116,109,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-116,110,114],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-117,110,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0047\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-116,false,113],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0047\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-117,false,114],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0038\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-118,106,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0038\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-118,107,117],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0038\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-118,108,116],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0038\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-118,false,115],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":35,\"full_literals\":[-26,119]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":39,\"full_literals\":[-30,119]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":48,\"full_literals\":[-39,119]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[63,64,66],\"full_literals\":[-120,54,55,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":63,\"full_literals\":[-54,120]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":64,\"full_literals\":[-55,120]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-57,120]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[70,72,73],\"full_literals\":[-121,61,62,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":70,\"full_literals\":[-61,121]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":72,\"full_literals\":[-62,121]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":73,\"full_literals\":[-63,121]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[56,60],\"full_literals\":[-122,47,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":56,\"full_literals\":[-47,122]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":60,\"full_literals\":[-51,122]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[69,74],\"full_literals\":[-123,60,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":69,\"full_literals\":[-60,123]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-64,123]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0054\",\"right_name\":\"grouped3_0057\",\"joined_name\":\"grouped3_0055\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-120,124],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0054\",\"right_name\":\"grouped3_0057\",\"joined_name\":\"grouped3_0055\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-119,false,124],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0054\",\"right_name\":\"grouped3_0057\",\"joined_name\":\"grouped3_0055\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-119,-120,125],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0062\",\"joined_name\":\"grouped3_0061\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-126,122,123],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0062\",\"joined_name\":\"grouped3_0061\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-122,-123,127],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0058\",\"right_name\":\"grouped3_0061\",\"joined_name\":\"grouped3_0059\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-128,121,126],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0058\",\"right_name\":\"grouped3_0061\",\"joined_name\":\"grouped3_0059\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-127,129],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0058\",\"right_name\":\"grouped3_0061\",\"joined_name\":\"grouped3_0059\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-121,false,128],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0055\",\"right_name\":\"grouped3_0059\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-124,-129,130],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0055\",\"right_name\":\"grouped3_0059\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-125,-128,130],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":20,\"owners\":[2,12,21,31,34,36,37,50,52,53,56,60,65,67,69,74]},{\"tag\":\"edge\",\"edge\":23,\"owners\":[14,16,29,33,35,49,51,53,55,57,59,60,64,66,70,73,74]},{\"tag\":\"edge\",\"edge\":27,\"owners\":[7,13,22,40,42,43,52,54,55,67,68]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[14,19,29,39,41,49,51,53,55,61,62,64,66,72,73,74]},{\"tag\":\"edge\",\"edge\":30,\"owners\":[8,20,30,38,44,45,46,48,56,57,61,63,69,70,72,73]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[16,20,33,39,46,49,57,59,61,64,70,72,73]},{\"tag\":\"edge\",\"edge\":35,\"owners\":[10,18,25,34,44,50,56,60,62,65,69,74]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[19,20,35,41,46,51,57,60,61,62,66,70,72,73,74]}]}"
  "p cnf 130 266\n-21 -8 0\n-23 -19 0\n-23 -21 0\n-23 -22 0\n-25 -4 0\n-25 -18 0\n-25 -20 0\n-27 -19 0\n-27 -21 0\n-28 -19 0\n-28 -21 0\n-29 -25 0\n-32 -12 0\n-33 -25 0\n-33 -27 0\n-33 -31 0\n-34 -27 0\n-34 -33 0\n-35 -23 0\n-35 -32 0\n-36 -23 0\n-38 -28 0\n-39 -21 0\n-41 -4 0\n-41 -19 0\n-41 -21 0\n-41 -26 0\n-41 -33 0\n-43 -10 0\n-43 -21 0\n-43 -39 0\n-43 -40 0\n-43 -42 0\n-44 -9 0\n-44 -39 0\n-44 -41 0\n-44 -43 0\n-45 -27 0\n-45 -44 0\n-46 -8 0\n-46 -39 0\n-46 -41 0\n-46 -43 0\n-46 -44 0\n-49 -28 0\n-53 -41 0\n-53 -44 0\n-55 -18 0\n-56 -4 0\n-56 -33 0\n-57 -25 0\n-57 -39 0\n-57 -41 0\n-57 -54 0\n-57 -56 0\n-58 -54 0\n-58 -55 0\n-58 -57 0\n-61 -25 0\n-61 -30 0\n-61 -41 0\n-61 -56 0\n-62 -61 0\n-63 -19 0\n-63 -22 0\n-63 -25 0\n-63 -29 0\n-63 -41 0\n-63 -42 0\n-63 -52 0\n-63 -56 0\n-63 -61 0\n-63 -62 0\n-5 1 3 4 18 20 21 29 30 32 0\n-34 1 3 4 18 21 29 30 32 0\n-8 -9 -42 0\n-8 -10 -45 0\n-8 -42 -45 0\n-10 -39 -45 0\n-1 -15 -55 0\n-1 -55 -56 0\n-15 -16 -54 0\n-15 -16 -55 0\n-15 -21 -54 0\n-15 -55 -59 0\n-16 -55 -56 0\n-20 -55 -56 0\n-55 -56 -59 0\n-2 8 41 43 44 47 51 0\n-23 8 41 43 44 51 0\n-27 8 41 44 47 51 0\n-28 8 41 43 44 47 51 0\n-2 15 56 58 60 0\n-15 2 23 25 27 28 60 0\n-25 15 58 0\n-3 -17 -62 0\n-3 -56 -62 0\n-17 -31 -62 0\n-17 -32 -54 0\n-31 -56 -62 0\n-5 9 43 45 46 0\n-31 9 43 45 46 0\n-33 9 45 46 0\n-34 9 43 46 0\n-6 14 39 47 48 52 0\n-35 14 39 48 52 0\n-36 14 39 47 48 52 0\n-22 62 0\n-29 60 61 0\n-35 54 61 62 0\n-36 54 60 61 62 0\n-37 54 60 0\n-7 12 41 47 51 53 0\n-25 17 0\n-35 17 56 0\n-8 15 56 58 64 0\n-15 8 41 43 44 64 0\n-41 15 58 0\n-9 16 58 59 0\n-16 9 43 45 46 0\n-43 16 59 0\n-45 16 58 0\n-46 16 58 59 0\n-59 9 43 46 0\n-13 10 21 30 40 44 46 0\n-52 10 21 44 46 0\n-53 10 21 30 40 46 0\n-10 55 57 63 64 0\n-21 63 64 0\n-40 57 64 0\n-42 55 0\n-44 55 57 63 0\n-46 55 57 63 64 0\n-55 10 42 44 46 64 0\n-57 10 40 44 46 0\n-63 10 21 44 46 0\n-11 55 61 63 0\n-24 63 0\n-40 61 0\n-48 55 0\n-50 55 61 63 0\n-41 17 0\n-53 17 56 0\n-13 57 62 63 64 0\n-32 63 64 0\n-42 62 0\n-52 57 64 0\n-53 57 62 63 0\n-62 13 42 53 64 0\n-14 61 62 63 0\n-37 63 0\n-48 62 0\n-52 61 0\n-26 57 61 0\n-61 26 57 0\n-62 30 55 0\n-54 39 63 0\n-63 39 54 0\n-47 60 0\n-60 47 0\n-51 64 0\n-64 51 0\n-2 65 0\n-7 66 0\n-8 67 0\n-12 68 0\n-15 69 0\n-17 70 0\n-65 71 0\n-71 72 0\n-72 73 0\n-66 74 0\n-67 75 0\n-75 76 0\n-74 -75 77 0\n-76 78 0\n-77 79 0\n-73 -78 80 0\n-73 -79 81 0\n-68 82 0\n-82 83 0\n-83 84 0\n-69 85 0\n-85 86 0\n-70 87 0\n-87 88 0\n-86 89 0\n-86 -88 90 0\n-89 91 0\n-90 92 0\n-84 -89 92 0\n-80 -92 93 0\n-81 -91 93 0\n-93 0\n-94 29 32 52 53 0\n-95 19 33 56 58 0\n-96 31 34 0\n-97 22 35 36 37 0\n-98 21 43 44 45 46 0\n-99 38 49 0\n-100 41 42 0\n-101 95 96 0\n-102 95 0\n-102 96 0\n-103 94 101 0\n-104 94 102 0\n-104 101 0\n-105 102 0\n-106 103 0\n-107 104 0\n-108 105 0\n-109 97 98 0\n-110 97 0\n-110 98 0\n-111 99 100 0\n-112 99 0\n-112 100 0\n-113 111 0\n-114 112 0\n-115 109 114 0\n-116 109 0\n-116 110 114 0\n-117 110 0\n-116 113 0\n-117 114 0\n-118 106 0\n-118 107 117 0\n-118 108 116 0\n-118 115 0\n118 0\n-26 119 0\n-30 119 0\n-39 119 0\n-120 54 55 57 0\n-54 120 0\n-55 120 0\n-57 120 0\n-121 61 62 63 0\n-61 121 0\n-62 121 0\n-63 121 0\n-122 47 51 0\n-47 122 0\n-51 122 0\n-123 60 64 0\n-60 123 0\n-64 123 0\n-120 124 0\n-119 124 0\n-119 -120 125 0\n-126 122 123 0\n-122 -123 127 0\n-128 121 126 0\n-127 129 0\n-121 128 0\n-124 -129 130 0\n-125 -128 130 0\n-130 0\n2 8 15 23 25 27 28 41 43 44 47 51 56 58 60 64 0\n10 11 21 24 26 40 42 44 46 48 50 51 55 57 61 63 64 0\n5 9 16 31 33 34 43 45 46 58 59 0\n10 13 21 30 32 40 42 44 46 52 53 55 57 62 63 64 0\n6 14 22 29 35 36 37 39 47 48 52 54 60 61 62 63 0\n11 14 24 30 37 40 48 50 52 55 61 62 63 0\n7 12 17 25 35 41 47 51 53 56 60 64 0\n13 14 26 32 37 42 48 51 52 53 57 61 62 63 64 0\n"
  "267 106 0 230 226 0\n268 115 0 230 229 0\n269 103 0 267 209 0\n270 124 0 248 249 235 236 237 231 232 233 158 140 156 155 138 151 139 150 153 137 141 264 0\n271 -129 0 270 258 256 0\n272 -127 0 271 254 0\n273 -123 0 272 252 243 244 160 162 245 0\n274 -60 0 273 246 0\n275 -64 0 273 247 0\n276 -47 0 274 159 0\n277 -51 0 275 161 0\n278 -122 0 277 276 242 0\n279 -126 0 278 273 251 0\n280 -41 120 0 275 277 237 130 236 140 131 26 27 36 42 61 68 137 141 138 128 260 0\n281 61 63 120 0 275 277 236 237 132 133 128 129 138 130 140 131 137 141 154 260 0\n282 63 120 0 275 237 147 130 236 131 129 145 128 133 132 281 60 63 125 127 262 0\n283 120 0 268 274 235 236 112 131 280 201 217 219 220 282 65 72 73 158 110 111 23 31 35 41 198 136 212 79 199 0\n284 -102 58 56 19 0 203 204 196 16 18 197 0\n285 53 -94 -54 56 52 41 29 25 0 275 274 277 276 195 13 20 99 113 265 0\n286 21 44 46 -54 -63 0 230 275 274 277 276 69 68 201 217 219 64 71 56 284 208 211 228 222 214 66 136 29 199 38 122 77 82 89 90 92 259 0\n287 44 46 -54 -63 0 275 274 277 276 56 71 68 66 286 1 3 9 11 30 84 89 259 0\n288 -63 39 0 230 275 274 277 276 64 66 67 68 69 70 71 158 201 56 217 219 225 227 210 284 206 285 47 287 40 43 89 90 91 92 117 259 0\n289 -46 58 25 41 56 0 275 274 277 276 40 43 44 89 90 91 92 117 259 0\n290 15 23 27 28 43 44 58 25 41 56 0 275 274 277 276 93 116 259 0\n291 23 27 56 28 43 44 58 25 41 0 276 277 274 275 194 290 94 117 167 163 165 183 169 173 184 170 174 187 171 176 189 178 193 192 179 190 191 177 188 182 175 186 181 172 185 180 164 168 166 115 143 265 0\n292 -23 43 44 46 58 41 56 63 0 275 277 230 129 151 2 4 19 21 90 284 198 208 213 211 228 221 222 212 219 199 217 78 201 0\n293 -27 43 44 46 58 41 56 21 0 277 276 230 8 15 17 38 91 284 196 199 208 214 211 223 228 227 222 210 219 207 217 202 201 197 76 102 0\n294 43 44 58 25 41 56 63 0 275 277 276 230 289 129 292 293 291 10 22 45 92 284 200 208 216 211 219 228 222 224 214 218 199 215 78 201 0\n295 40 13 32 21 30 63 42 44 46 52 53 55 57 10 0 275 262 149 0\n296 44 58 25 41 56 119 0 275 289 233 288 145 129 232 294 29 32 33 126 135 134 125 127 295 0\n297 58 25 41 56 119 0 289 296 34 37 39 101 120 124 104 102 103 261 0\n298 -58 54 0 283 57 58 234 0\n299 -25 -128 0 279 275 258 283 257 250 233 288 157 298 145 129 232 253 5 6 7 12 14 51 59 95 114 234 238 96 85 80 83 98 74 75 119 122 123 121 261 0\n300 56 -128 0 279 258 275 283 274 269 299 257 250 233 288 157 298 145 129 232 253 297 24 25 28 46 53 61 142 118 196 147 234 109 238 96 195 48 80 98 205 75 197 202 0\n301 -128 0 258 279 275 283 274 257 253 250 232 233 288 129 145 157 298 300 49 50 55 62 234 109 238 48 81 86 87 88 97 100 74 75 119 122 123 121 261 0\n302 -121 0 301 255 0\n303 -61 0 302 239 0\n304 -62 0 302 240 0\n305 -63 0 302 241 0\n306 -52 0 303 153 0\n307 -29 0 303 274 109 0\n308 -22 0 304 108 0\n309 -42 0 304 146 0\n310 -48 0 304 152 0\n311 -14 0 304 303 305 150 0\n312 -37 0 305 151 0\n313 -32 0 305 275 145 0\n314 57 0 275 305 313 303 304 277 311 310 309 312 306 154 144 148 266 0\n315 -39 0 314 52 0\n316 -54 0 314 54 0\n317 -36 0 315 311 276 310 306 107 0\n318 -6 0 315 276 311 310 306 105 0\n319 -35 0 315 311 310 306 106 0\n320 0 317 316 318 308 307 319 312 315 276 310 306 311 274 303 304 305 263 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00031.record024
