module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00039Data
public import GraphInputsRow26Part00039Frames
public import GraphInputsRow26Part00039Leaves
public import GraphInputsRow26Part00039Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00039.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record003
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 2126455488118784, 17419923358669078528, (certNat% 4), 7788822528]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record003_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00039.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00039.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record011
def vertexColumn : Fields := ⟨10, (certNat% 5)⟩
def kindColumn : Fields := ⟨3, (certNat% 6)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨71, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), 422624781926400, 617401548800, 632219185971200, 81064794148306944]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record011_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00039.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00039.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record012
def vertexColumn : Fields := ⟨10, (certNat% 9)⟩
def kindColumn : Fields := ⟨3, (certNat% 10)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), (certNat% 13), (certNat% 14), 474989023199232, 8650064134144]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record012_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00039.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00039.record042
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record042
def vertexColumn : Fields := ⟨10, (certNat% 15)⟩
def kindColumn : Fields := ⟨3, (certNat% 16)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨53, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 19), (certNat% 20), (certNat% 21)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), (certNat% 24), (certNat% 25), (certNat% 26), 26940211724288]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record042_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record042_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record042_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record042_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record042_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record042_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record042_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record042_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record042_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00039.record042

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00039.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1f2d23cb8aa6a3a1e9c6358764b86e8785e0fad13c789a65998e479715953552d1b61d4745de0ec370ce3a4e5334e332cc73c2e8b62e2b4ac6b86c9b16c3b61d4731d2785c9715c3783c4f07c740f0664382ea44d11c6190e465154354342d0768360cc318e0b42c2b41c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4db6db6926d24d349b4924924934da49249369249b492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 53), (facetIndex 69), (facetIndex 72)]))
 (.leaf ([(facetIndex 27), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 34), (facetIndex 43), (facetIndex 62), (facetIndex 77)]))
 (.branch 4
 (.leaf ([(facetIndex 30), (facetIndex 61), (facetIndex 73), (facetIndex 76), (facetIndex 78), (facetIndex 87)]))
 (.leaf ([(facetIndex 37), (facetIndex 45), (facetIndex 55), (facetIndex 56), (facetIndex 57)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 38), (facetIndex 42), (facetIndex 44), (facetIndex 47)]))
 (.leaf ([(facetIndex 48), (facetIndex 63), (facetIndex 66), (facetIndex 71)])))
 (.branch 8
 (.leaf ([(facetIndex 31), (facetIndex 35), (facetIndex 36), (facetIndex 54)]))
 (.branch 9
 (.leaf ([(facetIndex 41), (facetIndex 46)]))
 (.leaf ([(facetIndex 51)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3000000003230030600016006231114447009006584525800547720073221z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 64), (facetIndex 65)]))
 (.branch 2
 (.leaf ([(facetIndex 40), (facetIndex 68), (facetIndex 70)]))
 (.leaf ([(facetIndex 79), (facetIndex 80)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 83), (facetIndex 84)]))
 (.leaf ([(facetIndex 33), (facetIndex 39), (facetIndex 49), (facetIndex 50), (facetIndex 52)])))
 (.branch 6
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 82), (facetIndex 85), (facetIndex 86)]))
 (.leaf ([(facetIndex 81)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "16b772400b4004100000000000412000000180002z19;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5, 6]
def grouped2_0011 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8, 9]
def grouped2_0014 : List Nat := [8]
def grouped2_0015 : List Nat := [8, 9]
def grouped2_0016 : List Nat := [9]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1, 2]
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [1, 2]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [3]
def grouped3_0024 : List Nat := [3, 4]
def grouped3_0025 : List Nat := [3, 4, 5, 6]
def grouped3_0026 : List Nat := [4]
def grouped3_0027 : List Nat := [5]
def grouped3_0028 : List Nat := [5, 6]
def grouped3_0029 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00039.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00039.record005" 81

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00039.record005" "{\"ridges\":[[6,522],[9,385],[10,131],[18,536],[20,193],[21,656],[29,522],[32,150],[37,131],[37,385],[41,536],[44,522],[45,385],[45,386],[46,522],[46,642],[49,131],[51,208],[52,594],[53,656],[54,193],[54,194],[55,385],[56,193],[56,194],[57,385],[57,386],[60,536],[64,404],[65,193],[65,452],[67,536],[68,408],[69,536],[69,656],[70,904],[71,193],[72,193],[72,656],[79,150],[80,194],[80,452],[83,154],[84,386],[84,642],[84,904],[85,178],[85,194],[86,194],[86,594]],\"owners\":[[6,522,[75,82,83,84],[29,41,44,46,47]],[29,522,[82,83,84],[6,41,44,46,47,75]],[44,522,[75,83,84],[6,29,41,46,47,82]],[46,522,[75,82],[6,29,41,44,47,83,84]],[54,194,[79,80,86],[8,35,51,55,56,85]],[80,194,[8,51,54,56,85,86],[35,55,79]],[86,194,[8,35,54,55,80],[51,56,79,85]],[9,385,[64,65,68,70],[37,45,55,57]],[37,385,[68,70],[9,45,55,57,64,65]],[45,385,[64,65],[9,37,55,57,68,70]],[55,385,[64,68,70],[9,37,45,57,65]],[57,385,[64,65,68],[9,37,45,55,70]],[45,386,[80],[9,37,55,57,84]],[57,386,[80],[9,37,45,55,84]],[84,386,[9,37,55,80],[45,57]],[46,642,[86],[10,53,56,57,83,84]],[84,642,[10,53,56,86],[46,57,83]],[18,536,[75,82,83],[41,60,67,69]],[41,536,[],[18,60,67,69,75,82,83]],[60,536,[82,83],[18,41,67,69,75]],[67,536,[75,83],[18,41,60,69,82]],[69,536,[75,82],[18,41,60,67,83]],[51,208,[],[20,63,71,72,79,85,86]],[21,656,[83,86],[53,69,72]],[53,656,[],[21,69,72,83,86]],[69,656,[86],[21,53,72,83]],[72,656,[83],[21,53,69,86]],[32,150,[79],[]],[79,150,[32],[]],[83,154,[40],[]],[85,178,[49],[]],[52,594,[86],[]],[86,594,[52],[]],[64,404,[],[]],[65,452,[80],[]],[80,452,[65],[]],[68,408,[],[]],[70,904,[84],[]],[84,904,[70],[]]],\"edges\":[[29,[6,18,29,41,44,46,47,60,67,69,70,75,82,83,84]],[32,[20,21,32,40,49,51,53,63,64,68,69,71,72,79,83,85,86]],[34,[18,21,33,41,50,52,53,60,67,69,72,75,82,83,86]],[42,[9,37,45,55,57,64,65,68,70,80,84]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00039.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00039.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-9],[-14,-10],[-14,-12],[-14,-13],[-15,-9],[-19,-16],[-20,-16],[-20,-19],[-23,-9],[-27,-2],[-27,-22],[-27,-25],[-28,-4],[-28,-12],[-28,-13],[-28,-27],[-29,-3],[-29,-10],[-29,-14],[-29,-16],[-29,-22],[-29,-28],[-30,-2],[-30,-16],[-30,-20],[-30,-21],[-30,-22],[-30,-27],[-34,-9],[-37,-19],[-38,-20],[-38,-30],[-38,-37],[-39,-27],[-40,-29],[-43,-10],[-43,-12],[-43,-13],[-43,-14],[-43,-28],[-43,-32],[-43,-42],[-44,-11],[-44,-23],[-44,-25],[-44,-41],[-45,-44],[-46,-19],[-46,-38],[-46,-44],[-47,-30],[-48,-27],[-49,-9],[-49,-29],[-49,-41],[-49,-44],[-49,-45],[-1,41,45,46,47],[-8,45,46,47],[-18,41,46,47],[-20,41,45],[-4,-14,-22],[-6,-27,-34],[-6,-29,-34],[-27,-34,-40],[-29,-34,-39],[-27,42,43,49],[-43,2,24,27,29,48,49],[-49,2,12,27,28,43],[-27,-43,-49],[-29,-43,-48],[-3,33,34,36,38],[-14,36,38],[-19,33,34],[-28,33,36,38],[-30,33,34,36],[-19,43],[-30,43],[-47,3,14,28,43],[-20,49],[-47,4,26,29,49],[-5,41,45,46],[-17],[-31,45,46],[-35,41,46],[-37,41,45],[-24],[-7,46,49],[-26],[-37,49],[-40,46],[-10,42],[-42,10],[-46,16],[-48,22],[-25,49],[-49,25],[-33],[-34,43],[-43,34],[-36],[-38,47],[-47,38],[-50,26,37,40],[-51,14,19,28,29,30],[-52,9,12,13,27],[-53,17,20],[-54,24],[-55,50],[-56,51],[-57,56],[-58,55,57],[-59,55],[-59,57],[-60,53,54],[-61,52,60],[-62,60],[-63,61],[-64,62],[-65,58,64],[-65,59,63],[65],[-66,10,33,34],[-10,66],[-34,66],[-67,16,36,38],[-38,67],[-68,42,43],[-42,68],[-43,68],[-69,46,47],[-70,11,15,22,23,25],[-71,44],[-72,67,68],[-68,72],[-67,72],[-73,68],[-74,66,72],[-72,74],[-75,66,73],[-66,-72,75],[-76,69],[-76,70],[-77,71],[-78,76,77],[-79,76],[-79,77],[-80,74,79],[-80,75,78],[-74,-79,81],[-75,-78,81],[80],[-81],[1,5,8,17,18,20,21,31,35,37,38,41,45,46,47],[6,7,10,16,22,24,26,32,33,36,37,39,40,42,46,48,49],[5,7,11,17,23,25,26,31,35,37,40,41,45,46,49],[3,14,19,28,30,33,34,36,38,43,47]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":33,\"b\":31},{\"tag\":\"incompatible\",\"a\":37,\"b\":32},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":39,\"b\":31},{\"tag\":\"incompatible\",\"a\":45,\"b\":40},{\"tag\":\"incompatible\",\"a\":46,\"b\":40},{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":31},{\"tag\":\"incompatible\",\"a\":54,\"b\":8},{\"tag\":\"incompatible\",\"a\":54,\"b\":49},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":55,\"b\":10},{\"tag\":\"incompatible\",\"a\":55,\"b\":35},{\"tag\":\"incompatible\",\"a\":55,\"b\":36},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":9},{\"tag\":\"incompatible\",\"a\":56,\"b\":32},{\"tag\":\"incompatible\",\"a\":56,\"b\":37},{\"tag\":\"incompatible\",\"a\":56,\"b\":40},{\"tag\":\"incompatible\",\"a\":56,\"b\":49},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":8},{\"tag\":\"incompatible\",\"a\":57,\"b\":40},{\"tag\":\"incompatible\",\"a\":57,\"b\":46},{\"tag\":\"incompatible\",\"a\":57,\"b\":47},{\"tag\":\"incompatible\",\"a\":57,\"b\":49},{\"tag\":\"incompatible\",\"a\":57,\"b\":54},{\"tag\":\"incompatible\",\"a\":65,\"b\":31},{\"tag\":\"incompatible\",\"a\":69,\"b\":45},{\"tag\":\"incompatible\",\"a\":70,\"b\":46},{\"tag\":\"incompatible\",\"a\":70,\"b\":57},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":54},{\"tag\":\"incompatible\",\"a\":72,\"b\":56},{\"tag\":\"incompatible\",\"a\":80,\"b\":32},{\"tag\":\"incompatible\",\"a\":80,\"b\":35},{\"tag\":\"incompatible\",\"a\":80,\"b\":36},{\"tag\":\"incompatible\",\"a\":80,\"b\":37},{\"tag\":\"incompatible\",\"a\":80,\"b\":55},{\"tag\":\"incompatible\",\"a\":80,\"b\":63},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"incompatible\",\"a\":81,\"b\":33},{\"tag\":\"incompatible\",\"a\":81,\"b\":50},{\"tag\":\"incompatible\",\"a\":81,\"b\":52},{\"tag\":\"incompatible\",\"a\":81,\"b\":75},{\"tag\":\"incompatible\",\"a\":82,\"b\":81},{\"tag\":\"incompatible\",\"a\":83,\"b\":45},{\"tag\":\"incompatible\",\"a\":83,\"b\":70},{\"tag\":\"incompatible\",\"a\":83,\"b\":81},{\"tag\":\"incompatible\",\"a\":84,\"b\":57},{\"tag\":\"incompatible\",\"a\":85,\"b\":54},{\"tag\":\"incompatible\",\"a\":86,\"b\":31},{\"tag\":\"incompatible\",\"a\":86,\"b\":56},{\"tag\":\"incompatible\",\"a\":86,\"b\":75},{\"tag\":\"incompatible\",\"a\":86,\"b\":81},{\"tag\":\"incompatible\",\"a\":86,\"b\":82},{\"tag\":\"mate\",\"ridge\":522,\"a\":6,\"owners\":[75,82,83,84]},{\"tag\":\"mate\",\"ridge\":522,\"a\":29,\"owners\":[82,83,84]},{\"tag\":\"mate\",\"ridge\":522,\"a\":44,\"owners\":[75,83,84]},{\"tag\":\"mate\",\"ridge\":522,\"a\":46,\"owners\":[75,82]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[10,37,49]},{\"tag\":\"three\",\"ridge\":193,\"vertices\":[20,54,65]},{\"tag\":\"three\",\"ridge\":193,\"vertices\":[20,56,65]},{\"tag\":\"three\",\"ridge\":193,\"vertices\":[54,65,72]},{\"tag\":\"three\",\"ridge\":193,\"vertices\":[56,65,71]},{\"tag\":\"mate\",\"ridge\":194,\"a\":54,\"owners\":[79,80,86]},{\"tag\":\"mate\",\"ridge\":194,\"a\":80,\"owners\":[8,51,54,56,85,86]},{\"tag\":\"mate\",\"ridge\":194,\"a\":86,\"owners\":[8,35,54,55,80]},{\"tag\":\"three\",\"ridge\":194,\"vertices\":[54,80,86]},{\"tag\":\"three\",\"ridge\":194,\"vertices\":[56,80,85]},{\"tag\":\"mate\",\"ridge\":385,\"a\":9,\"owners\":[64,65,68,70]},{\"tag\":\"mate\",\"ridge\":385,\"a\":37,\"owners\":[68,70]},{\"tag\":\"mate\",\"ridge\":385,\"a\":45,\"owners\":[64,65]},{\"tag\":\"mate\",\"ridge\":385,\"a\":55,\"owners\":[64,68,70]},{\"tag\":\"mate\",\"ridge\":385,\"a\":57,\"owners\":[64,65,68]},{\"tag\":\"mate\",\"ridge\":386,\"a\":45,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":386,\"a\":57,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":386,\"a\":84,\"owners\":[9,37,55,80]},{\"tag\":\"mate\",\"ridge\":642,\"a\":46,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":642,\"a\":84,\"owners\":[10,53,56,86]},{\"tag\":\"mate\",\"ridge\":536,\"a\":18,\"owners\":[75,82,83]},{\"tag\":\"mate\",\"ridge\":536,\"a\":41,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":536,\"a\":60,\"owners\":[82,83]},{\"tag\":\"mate\",\"ridge\":536,\"a\":67,\"owners\":[75,83]},{\"tag\":\"mate\",\"ridge\":536,\"a\":69,\"owners\":[75,82]},{\"tag\":\"mate\",\"ridge\":208,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":656,\"a\":21,\"owners\":[83,86]},{\"tag\":\"mate\",\"ridge\":656,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":656,\"a\":69,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":656,\"a\":72,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":150,\"a\":32,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":150,\"a\":79,\"owners\":[32]},{\"tag\":\"mate\",\"ridge\":154,\"a\":83,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":178,\"a\":85,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":594,\"a\":52,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":594,\"a\":86,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":404,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":452,\"a\":65,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":452,\"a\":80,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":408,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":904,\"a\":70,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":904,\"a\":84,\"owners\":[70]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[53,69,72],\"full_literals\":[-50,26,37,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[37,45,55,56,57],\"full_literals\":[-51,14,19,28,29,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[31,35,36,54],\"full_literals\":[-52,9,12,13,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[41,46],\"full_literals\":[-53,17,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[51],\"full_literals\":[-54,24]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,50,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-58,55,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-59,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,53,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,52,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-65,58,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,59,63],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[32,64,65],\"full_literals\":[-66,10,33,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":32,\"full_literals\":[-10,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":65,\"full_literals\":[-34,66]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[40,68,70],\"full_literals\":[-67,16,36,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":70,\"full_literals\":[-38,67]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[79,80],\"full_literals\":[-68,42,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":79,\"full_literals\":[-42,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":80,\"full_literals\":[-43,68]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[83,84],\"full_literals\":[-69,46,47]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[33,39,49,50,52],\"full_literals\":[-70,11,15,22,23,25]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[81],\"full_literals\":[-71,44]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,66,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-75,66,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-72,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-76,69,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-76,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-78,76,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-79,76,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-79,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-80,74,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-80,75,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-74,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-75,-78,81],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[6,18,29,41,44,46,47,60,67,69,70,75,82,83,84]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[20,21,32,40,49,51,53,63,64,68,69,71,72,79,83,85,86]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[18,21,33,41,50,52,53,60,67,69,72,75,82,83,86]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[9,37,45,55,57,64,65,68,70,80,84]}]}"
  "158 -50 37 40 0 89 104 0\n159 -53 20 0 83 107 0\n160 -54 0 87 108 0\n161 -60 53 0 160 115 0\n162 -66 10 34 0 98 123 0\n163 -67 16 38 0 101 126 0\n164 1 5 8 18 20 21 31 35 37 38 41 45 46 47 0 83 154 0\n165 6 7 10 16 22 32 37 39 40 42 46 48 49 0 87 89 98 101 155 0\n166 5 7 11 23 25 31 35 37 40 41 45 46 49 0 83 89 156 0\n167 3 14 19 28 30 34 38 43 47 0 98 101 157 0\n168 -79 0 153 146 147 150 142 144 139 133 136 50 127 131 103 0\n169 74 0 168 152 148 0\n170 -44 0 43 44 45 46 47 50 56 84 82 86 91 85 88 166 0\n171 -71 0 170 133 0\n172 -77 0 171 144 0\n173 72 0 169 135 138 129 130 92 99 162 0\n174 -20 -67 0 7 31 163 0\n175 38 34 0 101 98 100 76 74 73 75 103 72 167 0\n176 14 28 66 0 98 101 173 122 124 93 125 100 128 134 174 159 161 117 119 120 175 33 49 91 158 109 112 111 110 102 76 74 79 105 17 0\n177 -49 2 12 43 28 0 69 97 12 0\n178 -49 28 66 0 122 173 176 4 3 124 93 125 100 128 134 174 159 161 175 33 49 91 158 109 113 121 118 116 53 177 106 10 0\n179 28 -78 0 172 122 153 173 89 151 141 124 93 125 100 128 134 174 159 161 175 33 49 91 158 109 113 121 118 116 102 145 143 176 3 4 19 178 96 67 81 106 62 1 5 9 132 0\n180 -78 0 153 173 122 89 151 141 124 125 93 100 128 134 174 159 161 175 33 49 102 91 158 109 113 121 118 116 179 13 14 15 16 22 81 106 53 0\n181 75 0 180 152 149 0\n182 -28 -38 0 122 89 31 159 161 33 49 91 158 109 113 121 118 116 102 13 14 15 16 22 81 106 53 0\n183 -10 43 0 122 99 175 182 33 49 91 158 109 31 159 161 117 119 120 112 111 110 78 77 2 18 105 0\n184 43 0 181 99 183 93 162 128 140 137 0\n185 -10 0 184 36 0\n186 -12 0 184 37 0\n187 -13 0 184 38 0\n188 -14 0 184 39 0\n189 -28 0 184 40 0\n190 -32 0 184 41 0\n191 -42 0 184 42 0\n192 34 0 184 100 0\n193 -9 0 192 29 0\n194 49 57 0 193 187 186 122 192 114 121 118 80 90 159 161 117 116 119 106 120 65 112 158 109 0\n195 57 0 122 184 193 187 186 114 121 118 194 55 57 70 61 106 159 116 161 0\n196 56 0 195 111 0\n197 51 0 196 110 0\n198 -19 0 122 193 187 186 184 192 190 191 185 6 8 30 48 159 91 161 158 109 113 121 118 116 106 11 34 52 70 63 88 165 0\n199 29 0 197 188 189 198 184 87 105 23 24 25 26 27 28 32 51 94 95 68 55 57 85 60 84 82 86 58 59 164 0\n200 -16 0 199 20 0\n201 -22 0 199 21 0\n202 -40 0 199 35 0\n203 -49 0 199 54 0\n204 -6 0 199 192 64 0\n205 -39 0 199 192 66 0\n206 -48 0 199 184 71 0\n207 -46 0 200 94 0\n208 -37 0 203 90 0\n209 -7 0 203 207 88 0\n210 0 209 204 205 206 185 201 200 208 202 191 207 190 203 165 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00039.record005
