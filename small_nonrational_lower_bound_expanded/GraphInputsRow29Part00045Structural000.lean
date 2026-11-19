module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00045Data
public import GraphInputsRow29Part00045Frames
public import GraphInputsRow29Part00045Leaves
public import GraphInputsRow29Part00045Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨82, by decide⟩, ⟨86, by decide⟩, ⟨91, by decide⟩, ⟨99, by decide⟩, ⟨103, by decide⟩, ⟨107, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 14740281580383633408, 2467972597174763520, 638303007145984, 8869795332096, 79691776]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020
def vertexColumn : Fields := ⟨10, (certNat% 4)⟩
def kindColumn : Fields := ⟨3, (certNat% 5)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), 9259400833873739776, (certNat% 8)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 34829500416, (certNat% 10), 43982612594688, (certNat% 7), (certNat% 11)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 4415796805632, 69122129920, 633318697598976, (certNat% 13), (certNat% 14)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), (certNat% 11), (certNat% 13), 34493956096]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 550561120256, 206158430208, 9259400833873739776, (certNat% 18), (certNat% 19)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 7), (certNat% 21), (certNat% 10), (certNat% 11)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 10), (certNat% 23), (certNat% 7), (certNat% 13)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [70367636881408, 633319771340800, (certNat% 11), (certNat% 13), (certNat% 14)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 21), (certNat% 25), (certNat% 11), 1100048498688]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 10), (certNat% 23), 52776558133248, (certNat% 7), (certNat% 13)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 13), 309371863040, 40269613367296, (certNat% 28), 17592186044416]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 13), (certNat% 30), (certNat% 31), 275548995584, 40269613367296, 17626545782784]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c19 c4
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c21 c2
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024
def vertexColumn : Fields := ⟨10, (certNat% 32)⟩
def kindColumn : Fields := ⟨3, (certNat% 33)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨105, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1188950302162681856, (certNat% 34), (certNat% 35), (certNat% 36), 545357968703488, 15633735483392]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record024

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f43b07c3cacaaa8ea1eb86398d62d876c3a8e538ce4b8ae1b91e3c6c9aa4e91e785394d52d475c368d534cd4b4ad1b51de0ec3a8ce334cb31ce8b92d4b32e2b4acab1ae1b46f07a1d8751d2719d1725e0f23c5c0f30a1683a318a6158364384e0b81ec24590e4c5294550d50d1342d07703a0cc328c530ce0b42c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da6db4d249349249b6d34924d2492492492492492492492491249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 49), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 42), (facetIndex 50), (facetIndex 51), (facetIndex 55), (facetIndex 58), (facetIndex 75), (facetIndex 93)])))
 (.branch 3
 (.leaf ([(facetIndex 41), (facetIndex 86), (facetIndex 87), (facetIndex 88), (facetIndex 89), (facetIndex 90), (facetIndex 91)]))
 (.leaf ([(facetIndex 43), (facetIndex 45), (facetIndex 62), (facetIndex 63), (facetIndex 77), (facetIndex 78), (facetIndex 95), (facetIndex 96)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 53), (facetIndex 61), (facetIndex 69), (facetIndex 76), (facetIndex 79), (facetIndex 81), (facetIndex 94), (facetIndex 97), (facetIndex 99), (facetIndex 104)]))
 (.leaf ([(facetIndex 44), (facetIndex 46), (facetIndex 47)])))
 (.branch 7
 (.leaf ([(facetIndex 68), (facetIndex 70), (facetIndex 71), (facetIndex 72), (facetIndex 73)]))
 (.leaf ([(facetIndex 52), (facetIndex 54), (facetIndex 56), (facetIndex 57), (facetIndex 59), (facetIndex 60)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "40008237084924800208dc236da60006e7e7f3e7240b5d65z1f;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 74), (facetIndex 80)]))
 (.branch 2
 (.leaf ([(facetIndex 92), (facetIndex 98)]))
 (.leaf ([(facetIndex 82), (facetIndex 85)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 100), (facetIndex 103)]))
 (.leaf ([(facetIndex 105), (facetIndex 106)])))
 (.branch 6
 (.leaf ([(facetIndex 83), (facetIndex 84)]))
 (.leaf ([(facetIndex 101), (facetIndex 102)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1207b3040001000015a8z3d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
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
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1, 2]
def grouped3_0016 : List Nat := [1]
def grouped3_0017 : List Nat := [1, 2]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [3, 4]
def grouped3_0020 : List Nat := [3, 4, 5, 6]
def grouped3_0021 : List Nat := [5]
def grouped3_0022 : List Nat := [5, 6]
def grouped3_0023 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record007" 60

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record007" "{\"ridges\":[[15,515],[15,641],[16,515],[16,769],[27,521],[27,769],[38,522],[38,770],[44,259],[46,259],[47,259],[49,515],[49,641],[52,515],[52,521],[52,522],[56,515],[56,521],[59,515],[59,521],[59,522],[60,641],[65,515],[65,641],[66,515],[66,641],[67,641],[74,641],[75,521],[75,769],[75,776],[80,641],[83,521],[83,680],[84,521],[84,712],[92,642],[93,770],[98,642],[101,522],[101,642],[101,680],[102,522],[102,712]],\"owners\":[[44,259,[9,16,55,58,67],[5,46,47,48,51]],[46,259,[9,16,51,58,67],[5,44,47,48,55]],[47,259,[9,16,51,55,67],[5,44,46,48,58]],[15,641,[74,80,83,84],[49,60,65,66,67]],[49,641,[83,84],[15,60,65,66,67,74,80]],[60,641,[80],[15,49,65,66,67,74,83,84]],[65,641,[74,80,84],[15,49,60,66,67,83]],[66,641,[74,80,83],[15,49,60,65,67,84]],[67,641,[74,83,84],[15,49,60,65,66,80]],[74,641,[15,65,66,67],[49,60,80,83,84]],[80,641,[15,60,65,66,83,84],[49,67,74]],[92,642,[15,65,66,67],[49,60,98,101,102]],[98,642,[15,60,65,66,101,102],[49,67,92]],[101,642,[15,49,66,67,98],[60,65,92,102]],[16,769,[27,75,80],[50,67]],[27,769,[16,50,67,80],[75]],[75,769,[16,67],[27,50,80]],[38,770,[16,50,67,98],[93]],[93,770,[16,67],[38,50,98]],[75,776,[38],[27,93]],[83,680,[101],[]],[101,680,[83],[]],[84,712,[102],[]],[102,712,[84],[]]],\"edges\":[[43,[15,49,60,65,66,67,74,80,83,84,92,98,101,102]],[44,[16,27,38,50,67,75,80,93,98]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-7],[-10,-8],[-10,-9],[-12,-7],[-12,-8],[-12,-9],[-14,-6],[-14,-13],[-15,-8],[-16,-14],[-17,-6],[-17,-13],[-17,-16],[-18,-6],[-18,-9],[-18,-13],[-18,-16],[-19,-14],[-19,-17],[-19,-18],[-20,-1],[-20,-13],[-20,-16],[-20,-19],[-21,-3],[-22,-15],[-22,-18],[-22,-21],[-23,-15],[-23,-17],[-23,-18],[-23,-21],[-24,-15],[-24,-18],[-24,-20],[-24,-21],[-25,-3],[-25,-14],[-25,-17],[-25,-20],[-25,-21],[-27,-15],[-27,-18],[-29,-15],[-29,-18],[-31,-15],[-31,-18],[-32,-11],[-32,-26],[-32,-28],[-32,-30],[-33,-10],[-34,-15],[-34,-17],[-34,-18],[-35,-15],[-35,-18],[-35,-20],[-40,-20],[-7,1,3,16,19,25],[-8,1,3,13,19,25],[-9,1,3,13,16,25],[-2,-3,-14],[-2,-3,-17],[-2,-3,-20],[-3,-11,-20],[-3,-14,-23],[-3,-14,-24],[-3,-17,-24],[-3,-20,-23],[-4,-14,-34],[-4,-14,-35],[-4,-17,-35],[-4,-20,-34],[-14,-32,-34],[-14,-32,-35],[-17,-32,-35],[-20,-32,-34],[-5,-14,-39],[-5,-14,-40],[-5,-20,-39],[-2,31,33,34,35],[-11,34,35],[-21,33],[-23,31,33,35],[-24,31,33,34],[-25,31,34,35],[-31,2,23,24,25],[-33,2,21,23,24,34,35],[-36,2,23,24,25],[-38,2,21,23,24,39,40],[-39,2,11,24,25,38],[-3,4,32,33],[-4,3,12,25,33],[-32,3,25],[-5,3,12,25,38],[-37,3,25],[-32,5],[-34,39],[-39,34],[-35,40],[-40,35],[-41,10,11,22,23,24,25],[-42,6,12,13,16,19,32,37],[-43,7,8,9],[-44,26,27,28,29,30],[-45,14,15,17,18,20,21],[-46,41],[-46,42],[-47,46],[-48,43],[-49,44],[-49,45],[-50,48],[-50,49],[-51,47],[-51,50],[51],[-31,52],[-33,52],[-36,53],[-38,53],[-54,34,35],[-34,54],[-35,54],[-39,55],[-40,55],[-53,56],[-56,57],[-52,57],[-54,-55,58],[-58,59],[-57,-59,60],[-60],[2,11,21,23,24,25,31,33,34,35,36,38,39,40],[3,4,5,12,25,32,33,37,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":48,\"b\":44},{\"tag\":\"incompatible\",\"a\":48,\"b\":46},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":50,\"b\":47},{\"tag\":\"incompatible\",\"a\":52,\"b\":42},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":46},{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":42},{\"tag\":\"incompatible\",\"a\":56,\"b\":51},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":42},{\"tag\":\"incompatible\",\"a\":57,\"b\":47},{\"tag\":\"incompatible\",\"a\":57,\"b\":51},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":58,\"b\":52},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":9},{\"tag\":\"incompatible\",\"a\":59,\"b\":51},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":16},{\"tag\":\"incompatible\",\"a\":64,\"b\":54},{\"tag\":\"incompatible\",\"a\":64,\"b\":57},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":65,\"b\":54},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":65,\"b\":57},{\"tag\":\"incompatible\",\"a\":65,\"b\":60},{\"tag\":\"incompatible\",\"a\":66,\"b\":54},{\"tag\":\"incompatible\",\"a\":66,\"b\":57},{\"tag\":\"incompatible\",\"a\":66,\"b\":59},{\"tag\":\"incompatible\",\"a\":66,\"b\":60},{\"tag\":\"incompatible\",\"a\":67,\"b\":16},{\"tag\":\"incompatible\",\"a\":67,\"b\":52},{\"tag\":\"incompatible\",\"a\":67,\"b\":56},{\"tag\":\"incompatible\",\"a\":67,\"b\":59},{\"tag\":\"incompatible\",\"a\":67,\"b\":60},{\"tag\":\"incompatible\",\"a\":70,\"b\":54},{\"tag\":\"incompatible\",\"a\":70,\"b\":57},{\"tag\":\"incompatible\",\"a\":72,\"b\":54},{\"tag\":\"incompatible\",\"a\":72,\"b\":57},{\"tag\":\"incompatible\",\"a\":74,\"b\":54},{\"tag\":\"incompatible\",\"a\":74,\"b\":57},{\"tag\":\"incompatible\",\"a\":75,\"b\":49},{\"tag\":\"incompatible\",\"a\":75,\"b\":68},{\"tag\":\"incompatible\",\"a\":75,\"b\":71},{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":80,\"b\":48},{\"tag\":\"incompatible\",\"a\":83,\"b\":54},{\"tag\":\"incompatible\",\"a\":83,\"b\":56},{\"tag\":\"incompatible\",\"a\":83,\"b\":57},{\"tag\":\"incompatible\",\"a\":84,\"b\":54},{\"tag\":\"incompatible\",\"a\":84,\"b\":57},{\"tag\":\"incompatible\",\"a\":84,\"b\":59},{\"tag\":\"incompatible\",\"a\":102,\"b\":59},{\"tag\":\"mate\",\"ridge\":259,\"a\":44,\"owners\":[9,16,55,58,67]},{\"tag\":\"mate\",\"ridge\":259,\"a\":46,\"owners\":[9,16,51,58,67]},{\"tag\":\"mate\",\"ridge\":259,\"a\":47,\"owners\":[9,16,51,55,67]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[15,16,52]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[15,16,56]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[15,16,59]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[16,49,59]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[16,52,65]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[16,52,66]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[16,56,66]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[16,59,65]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[27,52,83]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[27,52,84]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[27,56,84]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[27,59,83]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[52,75,83]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[52,75,84]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[56,75,84]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[59,75,83]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[38,52,101]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[38,52,102]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[38,59,101]},{\"tag\":\"mate\",\"ridge\":641,\"a\":15,\"owners\":[74,80,83,84]},{\"tag\":\"mate\",\"ridge\":641,\"a\":49,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":641,\"a\":60,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":641,\"a\":65,\"owners\":[74,80,84]},{\"tag\":\"mate\",\"ridge\":641,\"a\":66,\"owners\":[74,80,83]},{\"tag\":\"mate\",\"ridge\":641,\"a\":67,\"owners\":[74,83,84]},{\"tag\":\"mate\",\"ridge\":641,\"a\":74,\"owners\":[15,65,66,67]},{\"tag\":\"mate\",\"ridge\":641,\"a\":80,\"owners\":[15,60,65,66,83,84]},{\"tag\":\"mate\",\"ridge\":642,\"a\":92,\"owners\":[15,65,66,67]},{\"tag\":\"mate\",\"ridge\":642,\"a\":98,\"owners\":[15,60,65,66,101,102]},{\"tag\":\"mate\",\"ridge\":642,\"a\":101,\"owners\":[15,49,66,67,98]},{\"tag\":\"mate\",\"ridge\":769,\"a\":16,\"owners\":[27,75,80]},{\"tag\":\"mate\",\"ridge\":769,\"a\":27,\"owners\":[16,50,67,80]},{\"tag\":\"mate\",\"ridge\":769,\"a\":75,\"owners\":[16,67]},{\"tag\":\"mate\",\"ridge\":770,\"a\":38,\"owners\":[16,50,67,98]},{\"tag\":\"mate\",\"ridge\":770,\"a\":93,\"owners\":[16,67]},{\"tag\":\"mate\",\"ridge\":776,\"a\":75,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":680,\"a\":83,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":680,\"a\":101,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":712,\"a\":84,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":712,\"a\":102,\"owners\":[84]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[48,49,64,65,66,67],\"full_literals\":[-41,10,11,22,23,24,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[42,50,51,55,58,75,93],\"full_literals\":[-42,6,12,13,16,19,32,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[44,46,47],\"full_literals\":[-43,7,8,9]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[68,70,71,72,73],\"full_literals\":[-44,26,27,28,29,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[52,54,56,57,59,60],\"full_literals\":[-45,14,15,17,18,20,21]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-47,46,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-50,48,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-51,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-51,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":74,\"full_literals\":[-31,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":80,\"full_literals\":[-33,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":92,\"full_literals\":[-36,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":98,\"full_literals\":[-38,53]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[83,84],\"full_literals\":[-54,34,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-34,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-35,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":101,\"full_literals\":[-39,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":102,\"full_literals\":[-40,55]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-55,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-58,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-57,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":43,\"owners\":[15,49,60,65,66,67,74,80,83,84,92,98,101,102]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[16,27,38,50,67,75,80,93,98]}]}"
  "137 47 0 118 116 0\n138 50 0 118 117 0\n139 46 0 137 110 0\n140 48 0 138 114 0\n141 49 0 138 115 0\n142 41 0 139 108 0\n143 42 0 139 109 0\n144 43 0 140 111 0\n145 44 0 141 112 0\n146 45 0 141 113 0\n147 3 12 25 57 0 129 128 122 130 120 94 95 96 97 136 0\n148 -14 -32 -3 25 57 0 98 48 130 120 84 129 128 122 121 119 67 68 75 76 79 80 63 135 0\n149 -15 -32 0 145 51 50 49 42 44 106 0\n150 -17 -32 -54 0 54 77 123 0\n151 -18 -32 0 145 51 50 49 43 45 106 0\n152 -32 -3 25 -54 57 0 146 130 120 84 129 128 122 121 119 48 98 148 149 150 151 107 35 58 59 70 78 81 65 135 0\n153 -20 -4 -3 25 57 0 130 120 84 129 128 122 121 119 35 58 59 70 74 65 66 92 135 0\n154 -34 20 -4 21 0 146 53 54 55 71 107 0\n155 -3 25 -54 57 0 146 130 120 84 152 93 153 154 123 56 57 72 73 107 0\n156 -12 0 144 4 5 6 105 0\n157 -35 -25 21 0 146 40 39 38 56 57 107 0\n158 -25 52 0 146 120 84 119 38 39 40 157 87 53 55 107 0\n159 57 0 156 129 130 128 119 120 121 122 84 158 147 155 124 125 100 86 82 102 85 83 135 0\n160 -59 0 159 134 133 0\n161 -58 0 160 132 0\n162 -14 34 35 -3 0 83 100 102 37 25 67 68 63 88 89 90 91 135 0\n163 -15 11 25 0 142 144 9 26 29 33 103 1 3 105 0\n164 -17 34 35 -3 0 83 100 102 37 25 30 69 64 88 90 89 91 135 0\n165 34 35 20 -3 0 146 142 144 37 25 83 162 163 164 107 15 27 31 34 103 1 2 105 0\n166 -34 0 161 99 124 126 131 0\n167 -39 0 166 100 0\n168 -35 0 161 101 125 127 131 0\n169 -40 0 168 102 0\n170 -11 0 168 166 83 0\n171 -3 0 169 167 168 166 170 25 37 165 35 70 65 88 90 89 91 135 0\n172 -20 0 171 144 21 22 23 24 40 60 62 61 105 0\n173 -14 25 0 171 156 143 97 95 7 8 10 18 104 0\n174 -17 25 0 171 156 143 97 95 11 12 13 19 104 0\n175 25 21 0 171 170 172 146 156 143 95 97 163 173 174 107 14 16 17 20 104 0\n176 21 0 166 168 172 146 175 38 39 87 46 47 107 0\n177 -22 0 176 28 0\n178 -23 0 176 32 0\n179 -24 0 176 36 0\n180 -25 0 176 41 0\n181 33 0 176 84 0\n182 10 0 177 142 170 178 179 180 103 0\n183 0 181 182 52 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ec1f0eaa687ae18e6c5a964d8762b91e2785e3a6991e78539715a55351d4ad4749d17783b0ce3a4e334cc73a2cab86d1b26c5bc1e8761d4749ca785c9715d0f3306c0f3123286a0e8c6199160d88e1382e07b11324690e4c5195150d48d1342d07703a0cc318e1344c3322c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9269a4d24924d349a492492492492492492492249249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 47), (facetIndex 53), (facetIndex 56), (facetIndex 61), (facetIndex 74), (facetIndex 87)]))
 (.leaf ([(facetIndex 51), (facetIndex 52), (facetIndex 59), (facetIndex 65), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 72)]))
 (.leaf ([(facetIndex 80), (facetIndex 81), (facetIndex 82), (facetIndex 85)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 48), (facetIndex 49), (facetIndex 50)]))
 (.leaf ([(facetIndex 54), (facetIndex 60), (facetIndex 71), (facetIndex 77), (facetIndex 84), (facetIndex 90), (facetIndex 93)])))
 (.branch 7
 (.leaf ([(facetIndex 58), (facetIndex 64), (facetIndex 70), (facetIndex 75), (facetIndex 79), (facetIndex 83), (facetIndex 88), (facetIndex 92), (facetIndex 94)]))
 (.leaf ([(facetIndex 55), (facetIndex 57), (facetIndex 62), (facetIndex 63)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1ae14601dcdbc28c02b9244efc53b8f41324124z21;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 73), (facetIndex 76)]))
 (.leaf ([(facetIndex 78), (facetIndex 86)])))
 (.branch 3
 (.leaf ([(facetIndex 89)]))
 (.leaf ([(facetIndex 91)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "c810001z27;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

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
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0014 : List Nat := [1]
def grouped3_0015 : List Nat := [2]
def grouped3_0016 : List Nat := [2, 3]
def grouped3_0017 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record011" 36

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record011" "{\"ridges\":[[16,769],[28,529],[40,530],[53,769],[62,529],[62,530],[74,529],[76,900],[78,529],[87,530],[91,530],[91,664]],\"owners\":[[16,769,[28,74,76],[53,66]],[53,769,[28],[16,66,74,76]],[76,900,[89],[]],[91,664,[78],[]]],\"edges\":[[44,[16,28,40,53,66,74,76,87,89]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-7,-6],[-8,-7],[-9,-6],[-9,-8],[-10,-7],[-10,-9],[-11,-7],[-11,-9],[-12,-10],[-13,-4],[-13,-5],[-14,-13],[-17,-13],[-18,-4],[-18,-5],[-18,-14],[-18,-17],[-19,-6],[-19,-8],[-19,-11],[-2,-10,-16],[-10,-14,-16],[-3,-10,-19],[-10,-17,-19],[-1,2,14,15],[-5,2],[-15,18],[-19,16],[-20,4,5,7,9,14,17],[-21,6,8,10,11],[-22,20],[-23,22],[-24,21],[-25,24],[-26,23],[-26,25],[26],[-27,13,15],[-16,28],[-29,18],[-18,29],[-30,19],[-28,31],[-32,27],[-33,29,30],[-34,30],[-29,-30,34],[-35,32,33],[-31,-34,36],[35],[-36],[1,2,3,5,12,14,15,17,18]],\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":61,\"b\":55},{\"tag\":\"incompatible\",\"a\":61,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":56},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":56},{\"tag\":\"incompatible\",\"a\":63,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":73,\"b\":47},{\"tag\":\"incompatible\",\"a\":73,\"b\":53},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":87,\"b\":73},{\"tag\":\"incompatible\",\"a\":89,\"b\":47},{\"tag\":\"incompatible\",\"a\":89,\"b\":53},{\"tag\":\"incompatible\",\"a\":89,\"b\":74},{\"tag\":\"incompatible\",\"a\":89,\"b\":87},{\"tag\":\"incompatible\",\"a\":91,\"b\":55},{\"tag\":\"incompatible\",\"a\":91,\"b\":57},{\"tag\":\"incompatible\",\"a\":91,\"b\":63},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[28,62,78]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[62,74,78]},{\"tag\":\"three\",\"ridge\":530,\"vertices\":[40,62,91]},{\"tag\":\"three\",\"ridge\":530,\"vertices\":[62,87,91]},{\"tag\":\"mate\",\"ridge\":769,\"a\":16,\"owners\":[28,74,76]},{\"tag\":\"mate\",\"ridge\":769,\"a\":53,\"owners\":[28]},{\"tag\":\"mate\",\"ridge\":900,\"a\":76,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":664,\"a\":91,\"owners\":[78]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[47,53,56,61,74,87],\"full_literals\":[-20,4,5,7,9,14,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[55,57,62,63],\"full_literals\":[-21,6,8,10,11]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-22,20,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-23,22,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-24,false,21],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-25,false,24],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-26,23,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-26,false,25],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[73,76],\"full_literals\":[-27,13,15]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-16,28]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[89],\"full_literals\":[-29,18]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":89,\"full_literals\":[-18,29]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[91],\"full_literals\":[-30,19]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-32,27,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-33,29,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-34,false,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-29,-30,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-35,32,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-31,-34,36],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":44,\"owners\":[16,28,40,53,66,74,76,87,89]}]}"
  "53 23 0 37 35 0\n54 25 0 37 36 0\n55 22 0 53 32 0\n56 24 0 54 34 0\n57 20 0 55 31 0\n58 21 0 56 33 0\n59 -34 0 51 46 49 42 43 28 39 0\n60 -30 0 59 58 42 47 18 19 20 28 41 30 27 9 21 22 23 24 25 26 52 0\n61 -9 0 58 3 4 6 8 30 0\n62 -7 0 58 1 2 5 7 30 0\n63 -18 0 62 61 57 14 15 16 17 29 0\n64 -15 0 63 27 0\n65 -29 0 63 40 0\n66 -33 0 65 60 45 0\n67 32 0 66 50 48 0\n68 27 0 67 44 0\n69 13 0 68 64 38 0\n70 -4 0 69 10 0\n71 -5 0 69 11 0\n72 -14 0 69 12 0\n73 -17 0 69 13 0\n74 0 73 72 57 71 70 61 62 29 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record015
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f43707ce48f2b2b1aa68da1eb8639996359362d876c3a8e3391e2785ee44f1b2719a64d91e78539595355352d475c368d3351d2745de0ec338f13a4d9334d332cc73c2e8b92ccb8ae1b46c9b16f07a1d8751d2729c5783d0f23c6c0f06a0e8c619916258361382e078690e4c519515254351342d07703a0cc318d1324c3382c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da6db6d349249b4926db6d349249b492492492492492492492492449249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 82), (facetIndex 86)]))
 (.leaf ([(facetIndex 102), (facetIndex 106)])))
 (.branch 3
 (.leaf ([(facetIndex 109), (facetIndex 110)]))
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 80)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 83), (facetIndex 84), (facetIndex 87)]))
 (.leaf ([(facetIndex 92), (facetIndex 93), (facetIndex 100)])))
 (.branch 7
 (.leaf ([(facetIndex 103), (facetIndex 104), (facetIndex 107)]))
 (.branch 8
 (.leaf ([(facetIndex 85)]))
 (.leaf ([(facetIndex 105)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "220618661050000005500004074400300000033z48;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0, 1]
def grouped3_0001 : List Nat := [0, 1, 2, 3]
def grouped3_0003 : List Nat := [2]
def grouped3_0004 : List Nat := [2, 3]
def grouped3_0005 : List Nat := [3]
def grouped3_0006 : List Nat := [4]
def grouped3_0007 : List Nat := [4, 5]
def grouped3_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0009 : List Nat := [5]
def grouped3_0010 : List Nat := [6]
def grouped3_0011 : List Nat := [6, 7, 8]
def grouped3_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [7, 8]
def grouped3_0014 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record015" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record015" 44

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record015" "{\"ridges\":[[9,522],[15,642],[16,769],[16,770],[41,522],[47,642],[48,769],[48,770],[52,522],[53,522],[55,521],[56,521],[56,642],[57,522],[57,769],[57,770],[63,642],[64,769],[66,641],[66,642],[67,642],[67,769],[67,770],[72,652],[73,780],[80,900],[83,664],[84,792],[87,912],[92,652],[93,780],[100,900],[103,664],[104,792],[107,912]],\"owners\":[[55,521,[72,73,83,84],[9,41,52,53,56,57,85]],[56,521,[73,84],[9,41,52,53,55,57,72,83,85]],[9,522,[92,93,103,104,105],[41,52,53,55,56,57]],[41,522,[103,104,105],[9,52,53,55,56,57,92,93]],[52,522,[92,93,105],[9,41,53,55,56,57,103,104]],[53,522,[92,93,103,104,105],[9,41,52,55,56,57]],[57,522,[92,103,105],[9,41,52,53,55,56,93,104]],[66,641,[72,80,83,87],[15,47,56,63,67,85]],[15,642,[92,100,103,105,107],[47,56,63,66,67]],[47,642,[103,105,107],[15,56,63,66,67,92,100]],[56,642,[100,107],[15,47,63,66,67,92,103,105]],[63,642,[92,100,105],[15,47,56,66,67,103,107]],[66,642,[92,100,103,107],[15,47,56,63,67,105]],[67,642,[92,103,105],[15,47,56,63,66,100,107]],[16,769,[73,80,84,87],[48,57,64,67]],[48,769,[84,87],[16,57,64,67,73,80]],[57,769,[80,87],[16,48,64,67,73,84]],[64,769,[73,80],[16,48,57,67,84,87]],[67,769,[73,84],[16,48,57,64,80,87]],[16,770,[93,100,104,107],[48,57,64,67]],[48,770,[104,107],[16,57,64,67,93,100]],[57,770,[100,107],[16,48,64,67,93,104]],[67,770,[93,104],[16,48,57,64,100,107]],[72,652,[92],[]],[92,652,[72],[]],[73,780,[93],[]],[93,780,[73],[]],[80,900,[100],[]],[100,900,[80],[]],[83,664,[103],[]],[103,664,[83],[]],[84,792,[104],[]],[104,792,[84],[]],[87,912,[107],[]],[107,912,[87],[]]],\"edges\":[[29,[9,41,52,53,55,56,57,72,73,83,84,85,92,93,103,104,105]],[43,[15,47,56,63,66,67,72,80,83,85,87,92,100,103,105,107]],[44,[16,48,57,64,67,73,80,84,87,93,100,104,107]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record015" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record015\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-23,-17],[-24,-23],[-25,-4],[-25,-16],[-25,-17],[-25,-23],[-25,-24],[-27,-12],[-27,-19],[-27,-26],[-29,-7],[-29,-19],[-29,-20],[-29,-26],[-29,-27],[-9,16,17,19,20],[-10,17,20],[-1,23,24,26,27,28],[-4,26,27,28],[-7,23,24,28],[-8,23,24,26,27,28],[-11,23,26,28],[-14,16,18,19,22],[-2,23,25,26,28,29],[-5,26,28,29],[-10,25,29],[-12,23,25,28],[-14,23,25,26,29],[-15,23,26,28],[-3,17,18,20,22],[-6,20,22],[-11,18,22],[-13,17,18],[-15,17,20],[-3,24,25,27,29],[-6,27,29],[-11,25,29],[-15,24,27],[-16,23],[-23,16],[-17,24],[-24,17],[-18,25],[-25,18],[-19,26],[-26,19],[-20,27],[-27,20],[-22,29],[-29,22],[-30,16,17,18],[-16,30],[-17,30],[-18,30],[-19,31],[-20,31],[-22,31],[-23,32],[-24,32],[-25,32],[-33,26,27,29],[-26,33],[-27,33],[-29,33],[-21,34],[-28,35],[-30,36],[-36,37],[-32,38],[-31,38],[-35,39],[-34,39],[-39,40],[-33,40],[-33,-39,41],[-38,-40,42],[-38,-41,43],[-43,44],[-37,-42,44],[-44],[1,4,7,8,9,10,11,16,17,19,20,21,23,24,26,27,28],[2,5,10,12,14,15,16,18,19,21,22,23,25,26,28,29],[3,6,11,13,15,17,18,20,22,24,25,27,29]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":92,\"b\":73},{\"tag\":\"incompatible\",\"a\":93,\"b\":92},{\"tag\":\"incompatible\",\"a\":100,\"b\":41},{\"tag\":\"incompatible\",\"a\":100,\"b\":72},{\"tag\":\"incompatible\",\"a\":100,\"b\":73},{\"tag\":\"incompatible\",\"a\":100,\"b\":92},{\"tag\":\"incompatible\",\"a\":100,\"b\":93},{\"tag\":\"incompatible\",\"a\":104,\"b\":63},{\"tag\":\"incompatible\",\"a\":104,\"b\":83},{\"tag\":\"incompatible\",\"a\":104,\"b\":103},{\"tag\":\"incompatible\",\"a\":107,\"b\":52},{\"tag\":\"incompatible\",\"a\":107,\"b\":83},{\"tag\":\"incompatible\",\"a\":107,\"b\":84},{\"tag\":\"incompatible\",\"a\":107,\"b\":103},{\"tag\":\"incompatible\",\"a\":107,\"b\":104},{\"tag\":\"mate\",\"ridge\":521,\"a\":55,\"owners\":[72,73,83,84]},{\"tag\":\"mate\",\"ridge\":521,\"a\":56,\"owners\":[73,84]},{\"tag\":\"mate\",\"ridge\":522,\"a\":9,\"owners\":[92,93,103,104,105]},{\"tag\":\"mate\",\"ridge\":522,\"a\":41,\"owners\":[103,104,105]},{\"tag\":\"mate\",\"ridge\":522,\"a\":52,\"owners\":[92,93,105]},{\"tag\":\"mate\",\"ridge\":522,\"a\":53,\"owners\":[92,93,103,104,105]},{\"tag\":\"mate\",\"ridge\":522,\"a\":57,\"owners\":[92,103,105]},{\"tag\":\"mate\",\"ridge\":641,\"a\":66,\"owners\":[72,80,83,87]},{\"tag\":\"mate\",\"ridge\":642,\"a\":15,\"owners\":[92,100,103,105,107]},{\"tag\":\"mate\",\"ridge\":642,\"a\":47,\"owners\":[103,105,107]},{\"tag\":\"mate\",\"ridge\":642,\"a\":56,\"owners\":[100,107]},{\"tag\":\"mate\",\"ridge\":642,\"a\":63,\"owners\":[92,100,105]},{\"tag\":\"mate\",\"ridge\":642,\"a\":66,\"owners\":[92,100,103,107]},{\"tag\":\"mate\",\"ridge\":642,\"a\":67,\"owners\":[92,103,105]},{\"tag\":\"mate\",\"ridge\":769,\"a\":16,\"owners\":[73,80,84,87]},{\"tag\":\"mate\",\"ridge\":769,\"a\":48,\"owners\":[84,87]},{\"tag\":\"mate\",\"ridge\":769,\"a\":57,\"owners\":[80,87]},{\"tag\":\"mate\",\"ridge\":769,\"a\":64,\"owners\":[73,80]},{\"tag\":\"mate\",\"ridge\":769,\"a\":67,\"owners\":[73,84]},{\"tag\":\"mate\",\"ridge\":770,\"a\":16,\"owners\":[93,100,104,107]},{\"tag\":\"mate\",\"ridge\":770,\"a\":48,\"owners\":[104,107]},{\"tag\":\"mate\",\"ridge\":770,\"a\":57,\"owners\":[100,107]},{\"tag\":\"mate\",\"ridge\":770,\"a\":67,\"owners\":[93,104]},{\"tag\":\"mate\",\"ridge\":652,\"a\":72,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":652,\"a\":92,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":780,\"a\":73,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":780,\"a\":93,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":900,\"a\":80,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":900,\"a\":100,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":664,\"a\":83,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":664,\"a\":103,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":792,\"a\":84,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":792,\"a\":104,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":912,\"a\":87,\"owners\":[107]},{\"tag\":\"mate\",\"ridge\":912,\"a\":107,\"owners\":[87]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[72,73,80],\"full_literals\":[-30,16,17,18]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-16,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-17,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":80,\"full_literals\":[-18,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":83,\"full_literals\":[-19,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":84,\"full_literals\":[-20,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":87,\"full_literals\":[-22,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":92,\"full_literals\":[-23,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":93,\"full_literals\":[-24,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":100,\"full_literals\":[-25,32]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[103,104,107],\"full_literals\":[-33,26,27,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":103,\"full_literals\":[-26,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":104,\"full_literals\":[-27,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":107,\"full_literals\":[-29,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":85,\"full_literals\":[-21,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":105,\"full_literals\":[-28,35]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-33,-39,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-38,-40,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-38,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-43,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-37,-42,44],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[9,41,52,53,55,56,57,72,73,83,84,85,92,93,103,104,105]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[15,47,56,63,66,67,72,80,83,85,87,92,100,103,105,107]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[16,48,57,64,67,73,80,84,87,93,100,104,107]}]}"
  "84 -43 0 80 78 0\n85 31 30 0 54 44 53 42 33 56 57 31 48 30 34 50 32 83 0\n86 27 29 30 0 54 44 37 49 53 42 33 36 47 35 38 83 0\n87 29 30 0 84 85 70 77 54 44 52 40 49 26 86 8 9 10 63 23 75 71 72 66 65 25 24 29 82 0\n88 30 0 84 52 53 40 42 85 70 77 87 11 12 13 14 15 64 16 17 75 71 72 66 65 19 18 21 22 81 0\n89 36 0 88 67 0\n90 37 0 89 68 0\n91 -42 0 90 80 79 0\n92 -29 0 91 50 64 57 74 70 76 0\n93 -22 0 92 49 0\n94 -33 27 0 91 92 61 74 46 76 55 70 0\n95 32 18 0 88 58 59 39 41 51 0\n96 23 39 15 25 26 0 92 93 71 66 25 72 65 26 43 45 39 27 24 28 82 0\n97 -23 15 25 27 0 92 93 37 43 47 36 1 2 33 30 83 0\n98 23 25 26 0 91 43 95 69 76 73 71 66 96 29 0\n99 25 27 0 94 62 47 98 1 97 34 0\n100 27 0 91 47 94 62 45 99 3 4 5 6 7 60 16 17 69 76 73 71 72 66 65 22 18 21 20 81 0\n101 20 0 100 48 0\n102 33 0 100 63 0\n103 31 0 101 56 0\n104 40 0 102 74 0\n105 38 0 103 70 0\n106 0 105 104 91 76 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record021
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ec3945b31c57332aca723cb2aaaa6ac6a5a39b16a58d6c3a8e4b8ae1ba1e4785ee8791cc6b16c5713c729aa569c65596956539595554d55352d2b46d4745dc8ea338f13a4cd38cd332cc73c2e8b8ad2b2ae1b46c5b31d2729c6745d0f23c2f07f28a8a928a86a25856139291a515254554344d28c6324c5312c2b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db4da49b6d26db4da6db6da69b6da49269269349b49b493693492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 55), (facetIndex 61), (facetIndex 62), (facetIndex 63)]))
 (.leaf ([(facetIndex 78), (facetIndex 82), (facetIndex 83), (facetIndex 100)])))
 (.branch 3
 (.leaf ([(facetIndex 80), (facetIndex 81), (facetIndex 87), (facetIndex 99)]))
 (.branch 4
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 64), (facetIndex 88), (facetIndex 98)]))
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 94)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 72), (facetIndex 93), (facetIndex 96), (facetIndex 101)]))
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 65), (facetIndex 73), (facetIndex 74)])))
 (.branch 8
 (.leaf ([(facetIndex 48), (facetIndex 67), (facetIndex 75)]))
 (.branch 9
 (.leaf ([(facetIndex 51), (facetIndex 77), (facetIndex 86)]))
 (.leaf ([(facetIndex 89), (facetIndex 97)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5123950450009328001122018076654440706300000000000080070044006600033z23;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record021" "{\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record021" 64

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record021" "{\"ridges\":[[22,530],[22,642],[22,656],[23,672],[24,800],[40,649],[47,656],[48,771],[48,784],[50,672],[65,537],[67,649],[72,561],[73,561],[73,784],[74,784],[74,897],[75,897],[82,652],[83,774],[85,530],[85,642],[85,656],[86,774],[88,600],[89,282],[89,784],[91,672],[92,800],[93,240],[94,624],[95,530],[95,656],[95,672],[96,306],[98,784],[100,900],[101,432],[101,784]],\"owners\":[[22,530,[36,45,48,78,86,88,89,94,96],[47,85,95]],[85,530,[36,45,48,88,89,94,96],[22,47,78,86,95]],[95,530,[36,48,78,86,88,89],[22,45,47,85,94,96]],[22,642,[23,40,50,82,91],[47,85]],[85,642,[23,40,50,91],[22,47,82]],[22,656,[72,74,100,101],[47,85,95]],[47,656,[100,101],[22,72,74,85,95]],[85,656,[72,74,101],[22,47,95,100]],[95,656,[74,100],[22,47,72,85,101]],[23,672,[67,72,75,101],[50,91,95]],[50,672,[101],[23,67,72,75,91,95]],[91,672,[72,75,101],[23,50,67,95]],[95,672,[67,75],[23,50,72,91,101]],[24,800,[51,73,75,96,101],[68,92]],[92,800,[73,75,101],[24,51,68,96]],[89,282,[35,77],[]],[65,537,[36],[]],[40,649,[67],[]],[67,649,[40],[]],[48,771,[41,51],[]],[96,306,[44],[]],[72,561,[45,73],[]],[73,561,[45,72],[]],[48,784,[98,100,101],[65,73,74,86,89,96]],[73,784,[86,89,98,100],[48,65,74,96,101]],[74,784,[86,89,96,98],[48,65,73,100,101]],[89,784,[73,74,100,101],[48,65,86,96,98]],[98,784,[48,73,74,96,101],[65,86,89,100]],[101,784,[48,65,86,89,98],[73,74,96,100]],[93,240,[69],[]],[101,432,[71],[]],[74,897,[75],[]],[75,897,[74],[]],[82,652,[],[]],[83,774,[86],[]],[86,774,[83],[]],[88,600,[],[]],[94,624,[],[]],[100,900,[],[]]],\"edges\":[[34,[22,36,45,47,48,65,72,73,74,78,85,86,88,89,94,95,96,98,100,101]],[43,[22,23,40,47,50,67,72,74,75,82,85,91,95,100,101]],[44,[24,41,48,51,65,68,73,74,75,83,86,89,92,96,98,100,101]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record021" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record021\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-19,-16],[-36,-19],[-1,5,9,11,24,28,29,30,34,36],[-27,5,9,11,29,30,34,36],[-35,5,11,24,28,29,30],[-1,2,6,12,25,31],[-27,2,6,12,31],[-1,19,21,38,39],[-10,38,39],[-27,19,21,39],[-35,21,38],[-2,15,19,22,39],[-12,39],[-31,19,22,39],[-35,15,22],[-3,13,20,22,36,39],[-32,20,22,39],[-30,4,23],[-14,5],[-6,15],[-15,6],[-11,7,13],[-36,8],[-19,9,20],[-20,9,19],[-11,37,38,39],[-20,28,30,37,38],[-21,28,30,36,37],[-30,20,21,38,39],[-37,11,20,21,36,39],[-39,11,14,28,30,37],[-33,17],[-39,18],[-21,22],[-22,21],[-25],[-26,28],[-28,26],[-29],[-34],[-38],[-24,40],[-26,40],[-4,41],[-5,41],[-37,41],[-8,42],[-9,42],[-17,42],[-18,42],[-43,19,33,36,39],[-19,43],[-39,43],[-6,44],[-7,44],[-14,44],[-20,44],[-21,44],[-15,45],[-22,45],[-13,46],[-23,46],[-28,46],[-30,47],[-40,48],[-42,49],[-41,49],[-41,-42,50],[-49,51],[-50,52],[-51,53],[-52,54],[-48,53],[-55,43,44],[-44,55],[-43,55],[-43,-44,56],[-47,57],[-46,57],[-46,-47,58],[-57,59],[-58,60],[-45,59],[-45,-57,60],[-60,62],[-55,61],[-55,-59,62],[-55,-60,63],[-56,62],[-56,-59,63],[-63,64],[-53,-62,64],[-54,-61,64],[-64],[1,5,9,10,11,14,19,20,21,24,27,28,29,30,34,35,36,37,38,39],[1,2,6,10,12,15,19,21,22,25,27,31,35,38,39],[3,7,11,13,14,16,20,21,22,26,28,30,32,36,37,38,39]],\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":72,\"b\":68},{\"tag\":\"incompatible\",\"a\":96,\"b\":72},{\"tag\":\"mate\",\"ridge\":530,\"a\":22,\"owners\":[36,45,48,78,86,88,89,94,96]},{\"tag\":\"mate\",\"ridge\":530,\"a\":85,\"owners\":[36,45,48,88,89,94,96]},{\"tag\":\"mate\",\"ridge\":530,\"a\":95,\"owners\":[36,48,78,86,88,89]},{\"tag\":\"mate\",\"ridge\":642,\"a\":22,\"owners\":[23,40,50,82,91]},{\"tag\":\"mate\",\"ridge\":642,\"a\":85,\"owners\":[23,40,50,91]},{\"tag\":\"mate\",\"ridge\":656,\"a\":22,\"owners\":[72,74,100,101]},{\"tag\":\"mate\",\"ridge\":656,\"a\":47,\"owners\":[100,101]},{\"tag\":\"mate\",\"ridge\":656,\"a\":85,\"owners\":[72,74,101]},{\"tag\":\"mate\",\"ridge\":656,\"a\":95,\"owners\":[74,100]},{\"tag\":\"mate\",\"ridge\":672,\"a\":23,\"owners\":[67,72,75,101]},{\"tag\":\"mate\",\"ridge\":672,\"a\":50,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":672,\"a\":91,\"owners\":[72,75,101]},{\"tag\":\"mate\",\"ridge\":672,\"a\":95,\"owners\":[67,75]},{\"tag\":\"mate\",\"ridge\":800,\"a\":24,\"owners\":[51,73,75,96,101]},{\"tag\":\"mate\",\"ridge\":800,\"a\":92,\"owners\":[73,75,101]},{\"tag\":\"mate\",\"ridge\":282,\"a\":89,\"owners\":[35,77]},{\"tag\":\"mate\",\"ridge\":537,\"a\":65,\"owners\":[36]},{\"tag\":\"mate\",\"ridge\":649,\"a\":40,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":649,\"a\":67,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":771,\"a\":48,\"owners\":[41,51]},{\"tag\":\"mate\",\"ridge\":306,\"a\":96,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":561,\"a\":72,\"owners\":[45,73]},{\"tag\":\"mate\",\"ridge\":561,\"a\":73,\"owners\":[45,72]},{\"tag\":\"mate\",\"ridge\":784,\"a\":48,\"owners\":[98,100,101]},{\"tag\":\"mate\",\"ridge\":784,\"a\":73,\"owners\":[86,89,98,100]},{\"tag\":\"mate\",\"ridge\":784,\"a\":74,\"owners\":[86,89,96,98]},{\"tag\":\"mate\",\"ridge\":784,\"a\":89,\"owners\":[73,74,100,101]},{\"tag\":\"mate\",\"ridge\":784,\"a\":98,\"owners\":[48,73,74,96,101]},{\"tag\":\"mate\",\"ridge\":784,\"a\":101,\"owners\":[48,65,86,89,98]},{\"tag\":\"mate\",\"ridge\":240,\"a\":93,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":432,\"a\":101,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":897,\"a\":74,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":897,\"a\":75,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":652,\"a\":82,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":774,\"a\":83,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":774,\"a\":86,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":600,\"a\":88,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":624,\"a\":94,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":900,\"a\":100,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-24,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-26,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":35,\"full_literals\":[-4,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":36,\"full_literals\":[-5,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":98,\"full_literals\":[-37,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":44,\"full_literals\":[-8,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":45,\"full_literals\":[-9,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":69,\"full_literals\":[-17,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":71,\"full_literals\":[-18,42]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[72,93,96,101],\"full_literals\":[-43,19,33,36,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":72,\"full_literals\":[-19,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":101,\"full_literals\":[-39,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":40,\"full_literals\":[-6,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":41,\"full_literals\":[-7,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":65,\"full_literals\":[-14,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":73,\"full_literals\":[-20,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":74,\"full_literals\":[-21,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":67,\"full_literals\":[-15,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":75,\"full_literals\":[-22,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":51,\"full_literals\":[-13,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":77,\"full_literals\":[-23,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":86,\"full_literals\":[-28,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":89,\"full_literals\":[-30,47]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-42,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-50,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,43,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-44,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-47,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-57,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-59,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-55,-60,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-59,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-53,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-61,64],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[22,36,45,47,48,65,72,73,74,78,85,86,88,89,94,95,96,98,100,101]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[22,23,40,47,50,67,72,74,75,82,85,91,95,100,101]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[24,41,48,51,65,68,73,74,75,83,86,89,92,96,98,100,101]}]}"
  "98 -63 0 94 91 0\n99 1 5 9 10 11 14 19 20 21 24 27 28 30 35 36 37 39 0 39 40 41 95 0\n100 1 2 6 10 12 15 19 21 22 27 31 35 39 0 36 41 96 0\n101 3 7 11 13 14 16 20 21 22 26 28 30 32 36 37 39 0 41 97 0\n102 55 53 0 41 71 69 66 50 33 9 67 46 26 45 19 47 23 73 65 43 38 48 42 75 76 57 58 52 29 11 8 10 99 0\n103 44 53 0 102 71 69 66 50 33 49 32 47 23 48 57 74 24 51 0\n104 -43 53 0 98 41 103 71 69 66 50 33 49 32 47 23 73 65 43 38 67 46 48 51 77 24 90 27 81 64 78 0\n105 -30 53 0 98 102 88 82 71 69 67 44 18 64 62 80 0\n106 53 0 41 40 39 71 73 69 65 66 67 42 43 47 48 50 45 46 38 23 33 19 26 9 104 52 25 105 3 28 4 5 99 0\n107 -62 0 106 94 92 0\n108 -60 0 107 85 0\n109 -56 0 107 89 0\n110 -57 0 108 107 41 81 84 87 59 60 76 20 34 15 52 53 8 10 12 14 13 9 100 0\n111 -47 0 110 78 0\n112 -46 0 110 79 0\n113 -30 0 111 64 0\n114 -13 0 112 61 0\n115 -28 0 112 63 0\n116 -26 0 115 37 0\n117 43 44 0 41 58 35 11 54 21 52 53 12 14 8 10 13 9 100 0\n118 19 39 44 0 41 9 13 58 35 11 54 21 12 14 8 10 100 0\n119 39 44 0 113 115 116 114 58 35 55 22 57 56 17 118 1 2 30 16 101 0\n120 44 0 114 94 113 115 55 56 22 117 76 86 93 72 70 119 31 33 46 50 68 0\n121 55 0 120 75 0\n122 -43 0 120 109 77 0\n123 -59 0 121 107 87 0\n124 -19 0 122 52 0\n125 -39 0 122 53 0\n126 -45 0 123 83 0\n127 -12 0 125 13 0\n128 -10 0 125 41 9 0\n129 -15 0 126 59 0\n130 -22 0 126 60 0\n131 -6 0 129 20 0\n132 -2 0 129 124 130 125 12 0\n133 -21 0 130 34 0\n134 -35 0 130 129 15 0\n135 -31 0 130 124 125 14 0\n136 -1 0 132 131 127 36 135 6 0\n137 -27 0 132 131 127 135 7 0\n138 0 136 132 131 128 127 129 124 133 130 137 135 134 125 100 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record022
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3b0e516cc715cac8f2aa8e63592e2b86e4785ee8791cc6b16c6715c4f1aa6695a71996559e15a5594e5c5695655553570da354d4b4ad1b61d4745da8ce3a4cd38cd332cc73a2e2b4acab86d1b16cc749ca719d1743c8f0bc1fca06a2585613b21a8711a47098a5291a515254554344d28c6324c5312c2b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6d369a4926db4926db6d24926934d24926d26926d2692492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 37), (facetIndex 84), (facetIndex 86)]))
 (.leaf ([(facetIndex 36), (facetIndex 48), (facetIndex 50), (facetIndex 61), (facetIndex 89)])))
 (.branch 3
 (.leaf ([(facetIndex 72), (facetIndex 81), (facetIndex 82), (facetIndex 83)]))
 (.branch 4
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 80)]))
 (.leaf ([(facetIndex 34), (facetIndex 49), (facetIndex 51)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 29), (facetIndex 41), (facetIndex 42), (facetIndex 55), (facetIndex 57), (facetIndex 73), (facetIndex 74)]))
 (.leaf ([(facetIndex 60), (facetIndex 64), (facetIndex 65)])))
 (.branch 8
 (.leaf ([(facetIndex 28), (facetIndex 32), (facetIndex 52), (facetIndex 53), (facetIndex 62), (facetIndex 63)]))
 (.branch 9
 (.leaf ([(facetIndex 30), (facetIndex 40), (facetIndex 75)]))
 (.leaf ([(facetIndex 31), (facetIndex 58)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "10000022230000855200000066771609505077414100330558000104079857z1c;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 56), (facetIndex 59)]))
 (.leaf ([(facetIndex 54), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 39), (facetIndex 47), (facetIndex 91)]))
 (.branch 4
 (.leaf ([(facetIndex 95), (facetIndex 97)]))
 (.leaf ([(facetIndex 38), (facetIndex 70), (facetIndex 71)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 35), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 87)]))
 (.leaf ([(facetIndex 88), (facetIndex 90), (facetIndex 96)])))
 (.branch 8
 (.leaf ([(facetIndex 46), (facetIndex 76), (facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 93)]))
 (.branch 9
 (.leaf ([(facetIndex 85), (facetIndex 94)]))
 (.leaf ([(facetIndex 92), (facetIndex 98)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "9363879260650800000777700004415550000000000010000002700000024005z23;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

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
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3, 4]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [3, 4]
def grouped3_0020 : List Nat := [4]
def grouped3_0021 : List Nat := [5]
def grouped3_0022 : List Nat := [5, 6]
def grouped3_0023 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0024 : List Nat := [6]
def grouped3_0025 : List Nat := [7]
def grouped3_0026 : List Nat := [7, 8, 9]
def grouped3_0027 : List Nat := [8]
def grouped3_0028 : List Nat := [8, 9]
def grouped3_0029 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record022" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record022" 92

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record022" "{\"ridges\":[[11,261],[11,268],[14,276],[17,552],[18,769],[19,656],[20,273],[20,769],[20,784],[21,672],[22,769],[27,776],[31,261],[31,268],[32,276],[35,294],[38,282],[39,538],[42,521],[46,306],[47,562],[49,656],[51,672],[53,276],[54,540],[57,268],[58,261],[58,268],[59,652],[60,261],[60,268],[62,276],[63,276],[64,656],[65,276],[66,228],[67,356],[68,420],[69,769],[69,900],[70,344],[71,600],[72,273],[74,552],[75,521],[77,368],[78,624],[80,656],[81,784],[82,784],[85,282],[87,172],[88,294],[93,562],[94,344],[95,540],[96,356],[97,784],[97,900]],\"owners\":[[11,261,[14,32,35,62,63,65,67,68,69],[31,57,58,60]],[31,261,[14,62,63,65,67,68,69],[11,32,35,57,58,60]],[58,261,[14,32,35,63,65,68,69],[11,31,57,60,62,67]],[60,261,[14,32,35,62,63,67,68],[11,31,57,58,65,69]],[11,268,[85,88,94,95,96],[31,53,57,58,60]],[31,268,[94,95,96],[11,53,57,58,60,85,88]],[57,268,[85,94,95],[11,31,53,58,60,88,96]],[58,268,[85,88,95],[11,31,53,57,60,94,96]],[60,268,[85,88,94,96],[11,31,53,57,58,95]],[20,273,[14,32,38,46,53,62,63,70,77,79],[72,81,82]],[72,273,[14,32,46,62,63,77,79],[20,38,53,70,81,82]],[14,276,[85,94,95,97],[32,53,62,63,65]],[32,276,[94,95,97],[14,53,62,63,65,85]],[53,276,[97],[14,32,62,63,65,85,94,95]],[62,276,[85,95,97],[14,32,53,63,65,94]],[63,276,[85,94,95],[14,32,53,62,65,97]],[65,276,[85,94],[14,32,53,62,63,95,97]],[42,521,[18,54,59,60,71,72],[17,39,43,74,75]],[75,521,[18,39,54,60,71,72],[17,42,43,59,74]],[17,552,[27,91],[42,74,75]],[74,552,[27,91],[17,42,75]],[27,776,[18,60,72,95],[]],[19,656,[93,97,98],[49,64,80,82]],[49,656,[97,98],[19,64,80,82,93]],[64,656,[93,98],[19,49,80,82,97]],[80,656,[97],[19,49,64,82,93,98]],[20,784,[95,97,98],[65,72,81,82]],[81,784,[95,97],[20,65,72,82,98]],[82,784,[95],[20,65,72,81,97,98]],[97,784,[20,72,81],[65,82,95,98]],[21,672,[91,93,98],[51,75,80,83]],[51,672,[98],[21,75,80,83,91,93]],[35,294,[88],[]],[88,294,[35],[]],[38,282,[85],[]],[85,282,[38],[]],[39,538,[],[]],[46,306,[],[]],[47,562,[93],[]],[93,562,[47],[]],[54,540,[95],[]],[95,540,[54],[]],[87,172,[56],[]],[59,652,[],[]],[66,228,[90],[]],[67,356,[96],[]],[96,356,[67],[]],[68,420,[],[]],[69,900,[97],[]],[97,900,[69],[]],[70,344,[94],[]],[94,344,[70],[]],[71,600,[],[]],[77,368,[],[]],[78,624,[],[]]],\"edges\":[[22,[11,14,31,32,35,53,57,58,60,62,63,65,67,68,69,85,88,94,95,96,97]],[33,[14,20,32,38,46,53,62,63,65,70,72,77,79,81,82,85,94,95,97,98]],[34,[19,20,39,47,49,54,64,65,71,72,78,80,81,82,93,95,97,98]],[38,[17,21,22,27,42,47,51,74,75,78,80,81,83,91,93,98]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record022" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record022\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-23,-11],[-23,-12],[-26,-23],[-29,-23],[-30,-23],[-32,-14],[-37,-32],[-39,-36],[-45,-36],[-46,-36],[-49,-39],[-55,-39],[-56,-10],[-56,-21],[-56,-28],[-56,-31],[-56,-32],[-58,-23],[-58,-28],[-58,-48],[-58,-56],[-59,-58],[-1,2,12,13,29,30,32,34,35,36],[-11,2,29,30,32,34,35,36],[-26,2,12,13,30,32,35,36],[-28,2,12,13,29,30,34,35],[-1,49,51,55,56,57],[-11,55,56,57],[-25,49,55,56],[-26,49,51,56],[-28,49,51,55,57],[-6,2,12,14,17,22,29,30,37,42,44],[-39,2,12,17,29,30,42,44],[-2,49,55,56,58],[-12,55,56,58],[-22,58],[-29,49,56,58],[-30,49,55,56],[-32,49,55],[-16,4,23,27,28,38,39],[-41,4,15,23,28,38,39],[-3,9,53],[-40,9,53],[-4,-6,-36],[-6,-8,-36],[-9,4,28,39,56],[-5,54,58,59],[-19,58,59],[-31,54,59],[-45,58],[-6,56,58,59],[-46,56,58],[-47,56],[-58,6,39,46],[-7,53,54,59],[-20,59],[-13,51],[-51,13],[-14,49],[-49,14],[-15],[-17],[-18,54],[-54,18],[-23,56],[-56,23],[-50,24],[-27],[-33,52],[-34,57],[-57,34],[-35],[-36,58],[-58,36],[-37,55],[-55,37],[-38],[-42],[-43],[-60,28,31,32],[-61,10,12,21,22,29,30],[-62,11,26],[-63,60],[-64,62],[-65,61,64],[-66,63,65],[-67,66],[67],[-24,68],[-36,69],[-18,70],[-53,70],[-71,56,58],[-56,71],[-58,71],[-72,14,37,38],[-14,72],[-37,72],[-73,13,33,34,35,50],[-13,73],[-34,73],[-51,74],[-52,74],[-57,74],[-44,75],[-54,75],[-49,76],[-55,76],[-59,77],[-69,78],[-68,78],[-79,71,72],[-72,79],[-71,79],[-79,80],[-70,-79,81],[-80,82],[-78,82],[-78,-81,83],[-84,73,74],[-74,84],[-73,84],[-73,-74,85],[-77,86],[-76,86],[-76,-77,87],[-86,88],[-87,89],[-75,88],[-75,-86,89],[-89,90],[-84,-88,90],[-85,-88,91],[-91,92],[-82,-90,92],[-83,92],[-92],[1,2,11,12,13,22,25,26,28,29,30,32,34,35,36,49,51,55,56,57,58],[2,6,12,14,17,22,29,30,32,37,39,42,44,46,47,49,55,56,58,59],[5,6,15,18,19,23,31,32,38,39,43,45,46,47,54,56,58,59],[3,7,8,9,16,18,20,40,41,43,45,46,48,53,54,59]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":54,\"b\":31},{\"tag\":\"incompatible\",\"a\":54,\"b\":32},{\"tag\":\"incompatible\",\"a\":58,\"b\":54},{\"tag\":\"incompatible\",\"a\":62,\"b\":54},{\"tag\":\"incompatible\",\"a\":63,\"b\":54},{\"tag\":\"incompatible\",\"a\":65,\"b\":38},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":72,\"b\":69},{\"tag\":\"incompatible\",\"a\":80,\"b\":69},{\"tag\":\"incompatible\",\"a\":81,\"b\":69},{\"tag\":\"incompatible\",\"a\":85,\"b\":72},{\"tag\":\"incompatible\",\"a\":94,\"b\":72},{\"tag\":\"incompatible\",\"a\":95,\"b\":28},{\"tag\":\"incompatible\",\"a\":95,\"b\":52},{\"tag\":\"incompatible\",\"a\":95,\"b\":60},{\"tag\":\"incompatible\",\"a\":95,\"b\":64},{\"tag\":\"incompatible\",\"a\":95,\"b\":65},{\"tag\":\"incompatible\",\"a\":97,\"b\":54},{\"tag\":\"incompatible\",\"a\":97,\"b\":60},{\"tag\":\"incompatible\",\"a\":97,\"b\":83},{\"tag\":\"incompatible\",\"a\":97,\"b\":95},{\"tag\":\"incompatible\",\"a\":98,\"b\":97},{\"tag\":\"mate\",\"ridge\":261,\"a\":11,\"owners\":[14,32,35,62,63,65,67,68,69]},{\"tag\":\"mate\",\"ridge\":261,\"a\":31,\"owners\":[14,62,63,65,67,68,69]},{\"tag\":\"mate\",\"ridge\":261,\"a\":58,\"owners\":[14,32,35,63,65,68,69]},{\"tag\":\"mate\",\"ridge\":261,\"a\":60,\"owners\":[14,32,35,62,63,67,68]},{\"tag\":\"mate\",\"ridge\":268,\"a\":11,\"owners\":[85,88,94,95,96]},{\"tag\":\"mate\",\"ridge\":268,\"a\":31,\"owners\":[94,95,96]},{\"tag\":\"mate\",\"ridge\":268,\"a\":57,\"owners\":[85,94,95]},{\"tag\":\"mate\",\"ridge\":268,\"a\":58,\"owners\":[85,88,95]},{\"tag\":\"mate\",\"ridge\":268,\"a\":60,\"owners\":[85,88,94,96]},{\"tag\":\"mate\",\"ridge\":273,\"a\":20,\"owners\":[14,32,38,46,53,62,63,70,77,79]},{\"tag\":\"mate\",\"ridge\":273,\"a\":72,\"owners\":[14,32,46,62,63,77,79]},{\"tag\":\"mate\",\"ridge\":276,\"a\":14,\"owners\":[85,94,95,97]},{\"tag\":\"mate\",\"ridge\":276,\"a\":32,\"owners\":[94,95,97]},{\"tag\":\"mate\",\"ridge\":276,\"a\":53,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":276,\"a\":62,\"owners\":[85,95,97]},{\"tag\":\"mate\",\"ridge\":276,\"a\":63,\"owners\":[85,94,95]},{\"tag\":\"mate\",\"ridge\":276,\"a\":65,\"owners\":[85,94]},{\"tag\":\"mate\",\"ridge\":521,\"a\":42,\"owners\":[18,54,59,60,71,72]},{\"tag\":\"mate\",\"ridge\":521,\"a\":75,\"owners\":[18,39,54,60,71,72]},{\"tag\":\"mate\",\"ridge\":552,\"a\":17,\"owners\":[27,91]},{\"tag\":\"mate\",\"ridge\":552,\"a\":74,\"owners\":[27,91]},{\"tag\":\"three\",\"ridge\":769,\"vertices\":[18,20,69]},{\"tag\":\"three\",\"ridge\":769,\"vertices\":[20,22,69]},{\"tag\":\"mate\",\"ridge\":776,\"a\":27,\"owners\":[18,60,72,95]},{\"tag\":\"mate\",\"ridge\":656,\"a\":19,\"owners\":[93,97,98]},{\"tag\":\"mate\",\"ridge\":656,\"a\":49,\"owners\":[97,98]},{\"tag\":\"mate\",\"ridge\":656,\"a\":64,\"owners\":[93,98]},{\"tag\":\"mate\",\"ridge\":656,\"a\":80,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":784,\"a\":20,\"owners\":[95,97,98]},{\"tag\":\"mate\",\"ridge\":784,\"a\":81,\"owners\":[95,97]},{\"tag\":\"mate\",\"ridge\":784,\"a\":82,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":784,\"a\":97,\"owners\":[20,72,81]},{\"tag\":\"mate\",\"ridge\":672,\"a\":21,\"owners\":[91,93,98]},{\"tag\":\"mate\",\"ridge\":672,\"a\":51,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":294,\"a\":35,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":294,\"a\":88,\"owners\":[35]},{\"tag\":\"mate\",\"ridge\":282,\"a\":38,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":282,\"a\":85,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":538,\"a\":39,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":306,\"a\":46,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":562,\"a\":47,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":562,\"a\":93,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":540,\"a\":54,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":540,\"a\":95,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":172,\"a\":87,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":652,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":228,\"a\":66,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":356,\"a\":67,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":356,\"a\":96,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":420,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":900,\"a\":69,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":900,\"a\":97,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":344,\"a\":70,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":344,\"a\":94,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":600,\"a\":71,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":368,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":624,\"a\":78,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[60,64,65],\"full_literals\":[-60,28,31,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[28,32,52,53,62,63],\"full_literals\":[-61,10,12,21,22,29,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[31,58],\"full_literals\":[-62,11,26]},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,61,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,63,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-67,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":56,\"full_literals\":[-24,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-36,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":47,\"full_literals\":[-18,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":91,\"full_literals\":[-53,70]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[95,97],\"full_literals\":[-71,56,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":95,\"full_literals\":[-56,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":97,\"full_literals\":[-58,71]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[38,70,71],\"full_literals\":[-72,14,37,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":38,\"full_literals\":[-14,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-37,72]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[35,66,67,68,87],\"full_literals\":[-73,13,33,34,35,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":35,\"full_literals\":[-13,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":67,\"full_literals\":[-34,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-51,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":90,\"full_literals\":[-52,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":96,\"full_literals\":[-57,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":79,\"full_literals\":[-44,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":93,\"full_literals\":[-54,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":85,\"full_literals\":[-49,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":94,\"full_literals\":[-55,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":98,\"full_literals\":[-59,77]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-79,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-70,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-80,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-78,-81,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-84,73,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-73,-74,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-77,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-86,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-87,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-75,-86,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-89,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-84,-88,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-85,-88,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-91,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-82,-90,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-83,false,92],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[11,14,31,32,35,53,57,58,60,62,63,65,67,68,69,85,88,94,95,96,97]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[14,20,32,38,46,53,62,63,65,70,72,77,79,81,82,85,94,95,97,98]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[19,20,39,47,49,54,64,65,71,72,78,80,81,82,93,95,97,98]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[17,21,22,27,42,47,51,74,75,78,80,81,83,91,93,98]}]}"
  "142 66 0 88 87 0\n143 -72 14 37 0 77 96 0\n144 -73 13 33 34 50 0 72 99 0\n145 -91 0 137 134 0\n146 -83 0 137 136 0\n147 1 2 11 12 13 22 25 26 28 29 30 32 34 36 49 51 55 56 57 58 0 72 138 0\n148 2 6 12 14 22 29 30 32 37 39 44 46 47 49 55 56 58 59 0 62 78 139 0\n149 5 6 18 19 23 31 32 39 45 46 47 54 56 58 59 0 61 77 79 140 0\n150 3 7 8 9 16 18 20 40 41 45 46 48 53 54 59 0 79 141 0\n151 84 82 0 117 115 114 94 113 97 60 98 76 38 39 95 34 29 35 36 37 118 110 90 121 122 102 104 100 101 30 28 27 31 147 0\n152 74 82 0 151 118 111 89 67 102 103 104 120 57 69 70 144 0\n153 88 79 0 78 62 114 94 113 97 60 98 76 38 39 95 34 35 52 36 37 53 127 129 124 105 109 32 33 148 0\n154 82 0 145 72 117 118 115 110 113 114 90 97 98 94 95 60 76 37 36 35 29 34 39 38 152 153 133 123 100 101 58 23 25 71 24 26 147 0\n155 -90 0 154 137 135 0\n156 -89 0 155 131 0\n157 -87 0 156 128 0\n158 49 55 56 58 0 155 75 35 93 73 36 59 37 29 34 39 38 143 112 153 132 121 122 102 104 100 101 30 28 27 31 147 0\n159 -49 56 58 0 157 156 52 65 53 50 11 60 107 6 125 126 130 109 106 48 49 51 47 63 149 0\n160 56 58 0 157 156 50 53 65 52 159 158 12 76 108 7 125 126 130 109 106 48 49 51 47 63 149 0\n161 58 0 142 36 160 13 14 15 16 17 66 80 1 2 3 4 5 83 82 81 86 84 85 0\n162 -23 0 161 18 0\n163 -28 0 161 19 0\n164 -48 0 161 20 0\n165 -56 0 161 21 0\n166 -59 0 161 22 0\n167 36 0 161 74 0\n168 71 0 161 95 0\n169 -20 0 166 56 0\n170 -39 0 167 8 0\n171 -45 0 167 9 0\n172 -46 0 167 10 0\n173 69 0 167 90 0\n174 79 0 168 114 0\n175 6 0 170 161 172 54 0\n176 78 0 173 110 0\n177 -4 0 175 167 44 0\n178 -8 0 175 167 45 0\n179 -81 0 176 146 119 0\n180 -9 0 177 163 170 165 46 0\n181 -16 0 177 162 68 163 77 170 40 0\n182 -41 0 177 61 162 163 77 170 41 0\n183 -70 0 179 174 116 0\n184 -18 0 183 91 0\n185 -53 0 183 92 0\n186 -54 0 184 64 0\n187 -7 0 185 166 186 55 0\n188 -3 0 185 180 42 0\n189 -40 0 185 180 43 0\n190 0 189 185 178 188 187 181 184 169 182 171 172 164 180 186 166 150 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record022
