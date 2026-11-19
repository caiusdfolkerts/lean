module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00034Data
public import GraphInputsRow16Part00034Frames
public import GraphInputsRow16Part00034Leaves
public import GraphInputsRow16Part00034Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 1420569023086592, 9232397927807188992, (certNat% 3), 633318697598976]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), (certNat% 5), 301741175033823232, (certNat% 6), 142386755796992]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 1125955741417472, 4616190167810572288, (certNat% 8), (certNat% 5)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 13835058055282163712, 1974722883485696, (certNat% 10), 4123168604160]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 445856367404646400, (certNat% 12), 144860656959488, 1442602205315072, 633404596944896, 3489660928]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record002_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record016
def vertexColumn : Fields := ⟨10, (certNat% 13)⟩
def kindColumn : Fields := ⟨3, (certNat% 14)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2467990187985076224, (certNat% 15), 44534515892224, 3453162094592, 42924933948375040, 1407374917107712, 2084569088]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record016_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record019
def vertexColumn : Fields := ⟨10, (certNat% 16)⟩
def kindColumn : Fields := ⟨3, (certNat% 17)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2305913380407345152, (certNat% 18), 117093727750586368, 452611762550734848, 3865470566400, 1002754604531712, 9814671360]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record019_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record028
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record028
def vertexColumn : Fields := ⟨10, (certNat% 19)⟩
def kindColumn : Fields := ⟨3, (certNat% 20)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨67, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), 220676386036121600, 3467780509168304128, 70645249474560, 53754200064, 6116066983936]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record028_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record028_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record028_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record028_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record028_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record028_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record028_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record028_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record028_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record028

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9b15cd2a6a998b69394e8b86e4789ed266956665395552d64d5362d1b51d2745dd0ea398d6364cb3c2e4b52e2b1ae1b26e4751e2719d170de0f43c8f13c2f468a62581e9864952519294652544d0762328d1324e0b42c1b21c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6da6db49249349349269349249a4da492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 35), (facetIndex 42), (facetIndex 43)]))
 (.leaf ([(facetIndex 26), (facetIndex 62), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 32), (facetIndex 38), (facetIndex 45), (facetIndex 46)]))
 (.branch 4
 (.leaf ([(facetIndex 31), (facetIndex 55), (facetIndex 57)]))
 (.leaf ([(facetIndex 27), (facetIndex 50), (facetIndex 53), (facetIndex 63)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 39), (facetIndex 54), (facetIndex 59), (facetIndex 61)]))
 (.leaf ([(facetIndex 25), (facetIndex 48), (facetIndex 49)])))
 (.branch 8
 (.leaf ([(facetIndex 51), (facetIndex 58), (facetIndex 60)]))
 (.branch 9
 (.leaf ([(facetIndex 28), (facetIndex 36), (facetIndex 40), (facetIndex 41)]))
 (.leaf ([(facetIndex 24)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "100004157573035407466022000885208000230084169z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 56)]))
 (.branch 2
 (.leaf ([(facetIndex 66), (facetIndex 72)]))
 (.leaf ([(facetIndex 34), (facetIndex 37), (facetIndex 52)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 64), (facetIndex 65), (facetIndex 67)]))
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 73)])))
 (.branch 6
 (.leaf ([(facetIndex 44), (facetIndex 47)]))
 (.leaf ([(facetIndex 71)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "21d2065b000000002000a0500001008z19;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0002 : List Nat := [5, 6]
def grouped2_0003 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0004 : List Nat := [7]
def grouped2_0005 : List Nat := [7, 8, 9]
def grouped2_0006 : List Nat := [8]
def grouped2_0007 : List Nat := [8, 9]
def grouped2_0008 : List Nat := [9]
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record000" 66

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record000" "{\"ridges\":[[6,522],[10,545],[10,546],[12,76],[14,100],[17,321],[18,584],[19,608],[32,546],[34,582],[36,522],[38,522],[38,546],[39,321],[40,522],[40,584],[41,522],[44,354],[45,546],[45,608],[46,545],[46,546],[47,834],[48,76],[51,76],[51,100],[52,556],[53,76],[53,321],[54,76],[54,584],[57,100],[58,100],[58,608],[59,321],[60,584],[60,608],[61,321],[61,584],[70,106],[71,834]],\"owners\":[[6,522,[65,67,70,71],[28,36,38,40,41]],[36,522,[65,67,70,71],[6,28,38,40,41]],[38,522,[67,71],[6,28,36,40,41,65,70]],[40,522,[65],[6,28,36,38,41,67,70,71]],[41,522,[65,67,70],[6,28,36,38,40,71]],[10,545,[19,52,58,60],[32,38,46]],[46,545,[19,52,58,60],[10,32,38]],[10,546,[65,69,70],[32,38,45,46]],[32,546,[70],[10,38,45,46,65,69]],[38,546,[69],[10,32,45,46,65,70]],[45,546,[65],[10,32,38,46,69,70]],[46,546,[65,69,70],[10,32,38,45]],[12,76,[64,66,67,72,73],[25,48,51,53,54]],[48,76,[64,66,67,73],[12,25,51,53,54,72]],[51,76,[66,67,72],[12,25,48,53,54,64,73]],[53,76,[64,67,73],[12,25,48,51,54,66,72]],[54,76,[64,66,72],[12,25,48,51,53,67,73]],[14,100,[64,69,73],[31,51,57,58]],[51,100,[69],[14,31,57,58,64,73]],[57,100,[64,69,73],[14,31,51,58]],[58,100,[64],[14,31,51,57,69,73]],[17,321,[33,44,47,56],[39,53,59,61]],[39,321,[56],[17,33,44,47,53,59,61]],[53,321,[44,47],[17,33,39,56,59,61]],[59,321,[33,44,47],[17,39,53,56,61]],[61,321,[33,44,56],[17,39,47,53,59]],[18,584,[67,70,71,73],[40,54,60,61]],[40,584,[73],[18,54,60,61,67,70,71]],[54,584,[70,71],[18,40,60,61,67,73]],[60,584,[67,71],[18,40,54,61,70,73]],[61,584,[67,70,73],[18,40,54,60,71]],[19,608,[69,70,73],[45,58,60]],[45,608,[73],[19,58,60,69,70]],[58,608,[70],[19,45,60,69,73]],[60,608,[69],[19,45,58,70,73]],[34,582,[67,69],[]],[70,106,[37,64],[]],[44,354,[],[]],[47,834,[71],[]],[71,834,[47],[]],[52,556,[65,73],[]]],\"edges\":[[16,[6,10,28,32,34,36,38,40,41,45,46,47,65,67,69,70,71]],[20,[12,14,25,31,33,34,48,51,53,54,56,57,58,64,66,67,69,72,73]],[29,[6,18,28,36,38,40,41,52,54,60,61,65,67,70,71,73]],[38,[10,19,32,38,45,46,52,58,60,65,69,70,73]],[40,[17,33,39,44,47,53,56,59,61,66,71,72]],[41,[18,19,34,40,45,47,54,58,60,61,67,69,70,71,73]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-16,-10],[-16,-15],[-20,-16],[-24,-9],[-24,-11],[-36,-24],[-39,-24],[-39,-27],[-39,-37],[-40,-10],[-40,-24],[-40,-29],[-41,-8],[-41,-40],[-44,-10],[-44,-12],[-44,-14],[-44,-40],[-44,-41],[-1,37,39,41,42],[-15,37,39,41,42],[-17,39,42],[-19,37],[-20,37,39,41],[-2,7,27,32,34],[-23,7,27,32,34],[-2,37,40,41],[-12,41],[-17,40],[-22,37],[-23,37,40,41],[-3,36,38,39,43,44],[-25,36,38,39,44],[-26,38,39,43],[-28,36,39,44],[-29,36,38,43],[-4,36,40,44],[-26,40],[-31,36,40,44],[-32,36],[-5,13,21,24,30],[-18,30],[-28,21,24],[-33,13,21,24],[-35,13,21,30],[-6,39,41,42,44],[-19,44],[-29,41,42],[-34,39,42],[-35,39,41,44],[-7,40,41,44],[-22,44],[-32,41],[-34,40],[-14,39,40],[-41,16,36],[-21],[-24,42],[-42,24],[-27,37,44],[-45,26,32,34],[-46,10,15,19,20],[-47,8],[-48,46,47],[-49,45,48],[-50,49],[-51,50],[51],[-13,52],[-30,52],[-38,53],[-43,53],[-14,54],[-36,55],[-37,55],[-39,55],[-56,40,41,44],[-40,56],[-41,56],[-44,56],[-57,21,24],[-24,57],[-42,58],[-54,59],[-53,59],[-59,60],[-52,60],[-56,61],[-55,-56,62],[-63,57],[-57,-58,63],[-63,64],[-61,-63,65],[-62,64],[-65,66],[-60,-64,66],[-66],[1,2,10,12,14,15,17,19,20,22,23,24,37,39,40,41,42],[3,4,9,11,13,14,25,26,28,29,30,31,32,36,38,39,40,43,44],[1,6,10,15,17,19,20,27,29,34,35,37,39,41,42,44],[2,7,12,17,22,23,27,32,34,37,40,41,44],[5,13,18,21,24,28,30,33,35,38,42,43],[6,7,14,19,22,24,29,32,34,35,39,40,41,42,44]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":37,\"b\":28},{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":41,\"b\":37},{\"tag\":\"incompatible\",\"a\":47,\"b\":25},{\"tag\":\"incompatible\",\"a\":47,\"b\":31},{\"tag\":\"incompatible\",\"a\":64,\"b\":47},{\"tag\":\"incompatible\",\"a\":67,\"b\":47},{\"tag\":\"incompatible\",\"a\":67,\"b\":52},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":69,\"b\":28},{\"tag\":\"incompatible\",\"a\":69,\"b\":47},{\"tag\":\"incompatible\",\"a\":69,\"b\":54},{\"tag\":\"incompatible\",\"a\":70,\"b\":24},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":28},{\"tag\":\"incompatible\",\"a\":73,\"b\":32},{\"tag\":\"incompatible\",\"a\":73,\"b\":34},{\"tag\":\"incompatible\",\"a\":73,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"mate\",\"ridge\":522,\"a\":6,\"owners\":[65,67,70,71]},{\"tag\":\"mate\",\"ridge\":522,\"a\":36,\"owners\":[65,67,70,71]},{\"tag\":\"mate\",\"ridge\":522,\"a\":38,\"owners\":[67,71]},{\"tag\":\"mate\",\"ridge\":522,\"a\":40,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":522,\"a\":41,\"owners\":[65,67,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":10,\"owners\":[19,52,58,60]},{\"tag\":\"mate\",\"ridge\":545,\"a\":46,\"owners\":[19,52,58,60]},{\"tag\":\"mate\",\"ridge\":546,\"a\":10,\"owners\":[65,69,70]},{\"tag\":\"mate\",\"ridge\":546,\"a\":32,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":546,\"a\":38,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":546,\"a\":45,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":546,\"a\":46,\"owners\":[65,69,70]},{\"tag\":\"mate\",\"ridge\":76,\"a\":12,\"owners\":[64,66,67,72,73]},{\"tag\":\"mate\",\"ridge\":76,\"a\":48,\"owners\":[64,66,67,73]},{\"tag\":\"mate\",\"ridge\":76,\"a\":51,\"owners\":[66,67,72]},{\"tag\":\"mate\",\"ridge\":76,\"a\":53,\"owners\":[64,67,73]},{\"tag\":\"mate\",\"ridge\":76,\"a\":54,\"owners\":[64,66,72]},{\"tag\":\"mate\",\"ridge\":100,\"a\":14,\"owners\":[64,69,73]},{\"tag\":\"mate\",\"ridge\":100,\"a\":51,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":100,\"a\":57,\"owners\":[64,69,73]},{\"tag\":\"mate\",\"ridge\":100,\"a\":58,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":321,\"a\":17,\"owners\":[33,44,47,56]},{\"tag\":\"mate\",\"ridge\":321,\"a\":39,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":321,\"a\":53,\"owners\":[44,47]},{\"tag\":\"mate\",\"ridge\":321,\"a\":59,\"owners\":[33,44,47]},{\"tag\":\"mate\",\"ridge\":321,\"a\":61,\"owners\":[33,44,56]},{\"tag\":\"mate\",\"ridge\":584,\"a\":18,\"owners\":[67,70,71,73]},{\"tag\":\"mate\",\"ridge\":584,\"a\":40,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":584,\"a\":54,\"owners\":[70,71]},{\"tag\":\"mate\",\"ridge\":584,\"a\":60,\"owners\":[67,71]},{\"tag\":\"mate\",\"ridge\":584,\"a\":61,\"owners\":[67,70,73]},{\"tag\":\"mate\",\"ridge\":608,\"a\":19,\"owners\":[69,70,73]},{\"tag\":\"mate\",\"ridge\":608,\"a\":45,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":608,\"a\":58,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":608,\"a\":60,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":582,\"a\":34,\"owners\":[67,69]},{\"tag\":\"mate\",\"ridge\":106,\"a\":70,\"owners\":[37,64]},{\"tag\":\"mate\",\"ridge\":354,\"a\":44,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":834,\"a\":47,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":834,\"a\":71,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":556,\"a\":52,\"owners\":[65,73]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[51,58,60],\"full_literals\":[-45,26,32,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[28,36,40,41],\"full_literals\":[-46,10,15,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[24],\"full_literals\":[-47,8]},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,46,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0005\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,45,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-51,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":33,\"full_literals\":[-13,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":56,\"full_literals\":[-30,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-38,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":72,\"full_literals\":[-43,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":34,\"full_literals\":[-14,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":64,\"full_literals\":[-36,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":65,\"full_literals\":[-37,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-39,55]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[69,70,73],\"full_literals\":[-56,40,41,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":69,\"full_literals\":[-40,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-41,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":73,\"full_literals\":[-44,56]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[44,47],\"full_literals\":[-57,21,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":47,\"full_literals\":[-24,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":71,\"full_literals\":[-42,58]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-56,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,57,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-58,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-61,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-60,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":16,\"owners\":[6,10,28,32,34,36,38,40,41,45,46,47,65,67,69,70,71]},{\"tag\":\"edge\",\"edge\":20,\"owners\":[12,14,25,31,33,34,48,51,53,54,56,57,58,64,66,67,69,72,73]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[6,18,28,36,38,40,41,52,54,60,61,65,67,70,71,73]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[10,19,32,38,45,46,52,58,60,65,69,70,73]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[17,33,39,44,47,53,56,59,61,66,71,72]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[18,19,34,40,45,47,54,58,60,61,67,69,70,71,73]}]}"
  "104 50 0 68 67 0\n105 49 0 104 66 0\n106 -57 24 0 57 81 0\n107 -65 0 97 95 0\n108 5 13 18 24 28 30 33 35 38 42 43 0 57 102 0\n109 -63 60 0 107 86 85 72 71 84 73 87 70 69 90 93 106 88 4 5 6 7 11 80 32 33 35 36 37 40 34 39 99 0\n110 -57 63 0 106 91 58 83 0\n111 60 0 57 86 87 85 69 70 71 72 42 45 109 110 82 43 59 44 41 108 0\n112 -64 0 111 97 96 0\n113 -63 0 112 92 0\n114 -62 0 112 94 0\n115 -57 0 113 110 0\n116 -24 0 115 82 0\n117 -42 0 116 59 0\n118 39 56 0 117 116 80 52 47 79 53 48 78 54 51 46 50 55 103 0\n119 56 0 78 79 80 29 51 54 28 53 52 118 8 9 25 26 101 0\n120 -55 0 119 114 89 0\n121 -36 0 120 74 0\n122 -37 0 120 75 0\n123 -39 0 120 76 0\n124 -32 0 121 40 0\n125 -19 0 122 23 0\n126 -22 0 122 30 0\n127 -17 0 123 117 22 0\n128 -34 0 123 117 49 0\n129 40 44 0 119 128 124 121 105 125 38 77 61 13 56 65 63 1 2 3 64 62 0\n130 44 0 117 123 122 128 125 127 60 129 10 12 14 20 21 24 50 46 100 0\n131 -10 0 130 15 0\n132 -12 0 130 16 0\n133 -14 0 130 17 0\n134 -40 0 130 18 0\n135 -41 0 130 19 0\n136 -2 0 134 122 135 27 0\n137 -23 0 134 122 135 31 0\n138 -1 0 135 123 122 117 20 0\n139 -15 0 135 123 122 117 21 0\n140 -20 0 135 123 122 24 0\n141 0 136 137 131 132 133 139 127 138 125 126 140 116 122 123 134 135 117 98 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "26c9a95a99966658b69394e8b86e4789e9a559d16a599565654b59354d8b46d8751d2766358ce364d532ce4b52e2b1ad1b26c5b61e4751e2749c670de0f43c8f13c2f299162581e98649894a5454958341d50ca318d1324c4b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db49b6d24da4d24d34924924934924d2492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 62)]))
 (.branch 2
 (.leaf ([(facetIndex 68), (facetIndex 74)]))
 (.leaf ([(facetIndex 34), (facetIndex 40), (facetIndex 52)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 66), (facetIndex 67), (facetIndex 69)]))
 (.leaf ([(facetIndex 73), (facetIndex 75), (facetIndex 76)])))
 (.branch 6
 (.leaf ([(facetIndex 58), (facetIndex 61)]))
 (.leaf ([(facetIndex 72)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "48660196c002814000200000000200008z19;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [3, 4, 5, 6]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record001" 47

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record001" "{\"ridges\":[[11,321],[17,548],[18,584],[19,608],[32,548],[33,321],[40,554],[41,321],[42,74],[44,321],[47,321],[48,608],[53,548],[54,332],[58,356],[59,608],[60,548],[61,836],[62,344],[63,584],[63,608],[68,332],[72,356],[74,344]],\"owners\":[[42,74,[66,68,74],[6,25,36,39,41,69,75]],[11,321,[54,58,61,62],[33,41,44,47]],[33,321,[62],[11,41,44,47,54,58,61]],[41,321,[58,61],[11,33,44,47,54,62]],[44,321,[54,58,61],[11,33,41,47,62]],[47,321,[54,61,62],[11,33,41,44,58]],[17,548,[67,73,76],[32,53,59,60]],[32,548,[76],[17,53,59,60,67,73]],[53,548,[73],[17,32,59,60,67,76]],[60,548,[67,73,76],[17,32,53,59]],[18,584,[69,75,76],[42,55,63]],[63,584,[69],[18,42,55,75,76]],[19,608,[73,75,76],[48,59,63]],[48,608,[76],[19,59,63,73,75]],[59,608,[75],[19,48,63,73,76]],[63,608,[73],[19,48,59,75,76]],[40,554,[67,75],[]],[54,332,[68],[]],[68,332,[54],[]],[58,356,[72],[]],[72,356,[58],[]],[61,836,[],[]],[62,344,[74],[]],[74,344,[62],[]]],\"edges\":[[38,[17,19,32,40,48,53,59,60,63,67,73,75,76]],[40,[11,33,41,44,47,54,58,61,62,68,72,74]],[41,[18,19,34,42,48,55,59,61,63,69,73,75,76]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-17,-13],[-17,-16],[-18,-17],[-23,-17],[-26,-17],[-28,-17],[-31,-17],[-10,23,25,29],[-1,15,17,20,21],[-6,21],[-9,17,20],[-11,15,17,20],[-12,15,20,21],[-2,24,28,31],[-5,31],[-14,28],[-19,24,28,31],[-3,26,30,31],[-22,26],[-4,28,30,31],[-13,31],[-18,30],[-22,28],[-8,24,30],[-15,25],[-25,15],[-17,27],[-27,17],[-20],[-21,29],[-29,21],[-32,15,21],[-15,32],[-21,32],[-25,33],[-29,33],[-7,34],[-24,35],[-28,36],[-30,36],[-31,36],[-37,17,20],[-17,37],[-27,38],[-34,39],[-33,39],[-40,32,39],[-39,40],[-32,40],[-32,-39,41],[-36,42],[-35,42],[-43,37],[-37,-38,43],[-43,45],[-42,44],[-42,-43,46],[-46,47],[-40,-45,47],[-41,-44,47],[-47],[2,4,5,8,13,14,18,19,22,24,28,30,31],[1,6,9,11,12,15,17,20,21,25,27,29],[3,4,7,10,13,16,18,20,22,26,28,30,31]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":58,\"b\":48},{\"tag\":\"incompatible\",\"a\":58,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":66,\"b\":58},{\"tag\":\"incompatible\",\"a\":69,\"b\":58},{\"tag\":\"incompatible\",\"a\":73,\"b\":58},{\"tag\":\"incompatible\",\"a\":76,\"b\":58},{\"tag\":\"mate\",\"ridge\":74,\"a\":42,\"owners\":[66,68,74]},{\"tag\":\"mate\",\"ridge\":321,\"a\":11,\"owners\":[54,58,61,62]},{\"tag\":\"mate\",\"ridge\":321,\"a\":33,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":321,\"a\":41,\"owners\":[58,61]},{\"tag\":\"mate\",\"ridge\":321,\"a\":44,\"owners\":[54,58,61]},{\"tag\":\"mate\",\"ridge\":321,\"a\":47,\"owners\":[54,61,62]},{\"tag\":\"mate\",\"ridge\":548,\"a\":17,\"owners\":[67,73,76]},{\"tag\":\"mate\",\"ridge\":548,\"a\":32,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":548,\"a\":53,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":548,\"a\":60,\"owners\":[67,73,76]},{\"tag\":\"mate\",\"ridge\":584,\"a\":18,\"owners\":[69,75,76]},{\"tag\":\"mate\",\"ridge\":584,\"a\":63,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":608,\"a\":19,\"owners\":[73,75,76]},{\"tag\":\"mate\",\"ridge\":608,\"a\":48,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":608,\"a\":59,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":608,\"a\":63,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":554,\"a\":40,\"owners\":[67,75]},{\"tag\":\"mate\",\"ridge\":332,\"a\":54,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":332,\"a\":68,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":356,\"a\":58,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":356,\"a\":72,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":836,\"a\":61,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":344,\"a\":62,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":344,\"a\":74,\"owners\":[62]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[54,62],\"full_literals\":[-32,15,21]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":54,\"full_literals\":[-15,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":62,\"full_literals\":[-21,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":68,\"full_literals\":[-25,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":74,\"full_literals\":[-29,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":34,\"full_literals\":[-7,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-24,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":73,\"full_literals\":[-28,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":75,\"full_literals\":[-30,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-31,36]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[58,61],\"full_literals\":[-37,17,20]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":58,\"full_literals\":[-17,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":72,\"full_literals\":[-27,38]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-40,32,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-39,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,37,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-37,-38,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-42,-43,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-40,-45,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-44,47],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[17,19,32,40,48,53,59,60,63,67,73,75,76]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[11,33,41,44,47,54,58,61,62,68,72,74]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[18,19,34,42,48,55,59,61,63,69,73,75,76]}]}"
  "65 -37 17 0 29 42 0\n66 -46 0 61 58 0\n67 1 6 9 11 12 15 17 21 25 27 29 0 29 63 0\n68 3 4 7 10 13 16 18 22 26 28 30 31 0 29 64 0\n69 -43 39 0 66 46 36 35 45 37 53 57 65 51 1 2 3 4 5 6 7 40 8 18 19 20 68 0\n70 -37 43 0 65 54 27 44 0\n71 40 0 29 48 49 46 33 34 35 36 10 13 69 70 43 11 28 9 12 67 0\n72 -45 0 71 61 59 0\n73 -43 0 72 55 0\n74 -37 0 73 70 0\n75 -17 0 74 43 0\n76 -9 0 75 29 11 0\n77 -27 0 75 28 0\n78 39 0 71 46 47 35 36 25 30 32 0\n79 32 0 29 77 76 75 33 34 26 9 12 10 31 13 67 0\n80 41 0 79 78 50 0\n81 -44 0 80 61 60 0\n82 -42 0 81 56 0\n83 -36 0 82 51 0\n84 -35 0 82 52 0\n85 -28 0 83 39 0\n86 -30 0 83 40 0\n87 -31 0 83 41 0\n88 -24 0 84 38 0\n89 -14 0 85 16 0\n90 -4 0 85 86 87 20 0\n91 -22 0 85 23 0\n92 -18 0 86 22 0\n93 -5 0 87 15 0\n94 -13 0 87 21 0\n95 -2 0 88 85 87 14 0\n96 -19 0 88 85 87 17 0\n97 -8 0 88 86 24 0\n98 0 91 95 94 90 97 89 92 96 93 88 85 86 87 62 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00034.record001
