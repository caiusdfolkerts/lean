module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00139Data
public import GraphInputsRow24Part00139Frames
public import GraphInputsRow24Part00139Leaves
public import GraphInputsRow24Part00139Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record007
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 2161727855497576448, (certNat% 3), (certNat% 4), (certNat% 5), 34110630264832, 14777436277309440]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record007_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record008
def vertexColumn : Fields := ⟨10, (certNat% 6)⟩
def kindColumn : Fields := ⟨3, (certNat% 7)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 10), (certNat% 11), 17461189541888, 70016900456775680]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record008_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record012
def vertexColumn : Fields := ⟨10, (certNat% 12)⟩
def kindColumn : Fields := ⟨3, (certNat% 13)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨88, by decide⟩, ⟨96, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17), 8778913153024, 17979214137393152]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record012_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record013
def vertexColumn : Fields := ⟨10, (certNat% 18)⟩
def kindColumn : Fields := ⟨3, (certNat% 19)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), (certNat% 23), 32465657790464, 71494644084506624]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), (certNat% 26), (certNat% 27), 2024403216875126784, 34906272956416, 65231825852694528]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record013_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "8f13a959569394e2b86e8791e0fb51d27198e539a5655556355362d2b46d8751d0f59394d534ce4b4acab1ae1b46c3b91d4731c6785d1715e0f43c8f07cb4930b2528a6258361382e2c6495264529615254358344d0b54328d1324c3342c4b0ac8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6d249b4d36d269249349a4924d2492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 47), (facetIndex 50), (facetIndex 58), (facetIndex 61), (facetIndex 69)]))
 (.leaf ([(facetIndex 40), (facetIndex 71), (facetIndex 74), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 38), (facetIndex 45), (facetIndex 51), (facetIndex 52), (facetIndex 54)]))
 (.leaf ([(facetIndex 39), (facetIndex 57), (facetIndex 62), (facetIndex 64), (facetIndex 65)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 37), (facetIndex 41), (facetIndex 42), (facetIndex 43)])))
 (.branch 7
 (.leaf ([(facetIndex 35), (facetIndex 44), (facetIndex 48), (facetIndex 49)]))
 (.leaf ([(facetIndex 36), (facetIndex 55), (facetIndex 59), (facetIndex 60)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2424020001b0c7e18e82436016b696afd68z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 53), (facetIndex 63), (facetIndex 70)]))
 (.leaf ([(facetIndex 78), (facetIndex 79)])))
 (.branch 3
 (.leaf ([(facetIndex 46), (facetIndex 56), (facetIndex 66), (facetIndex 67), (facetIndex 68)]))
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 80), (facetIndex 81)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "f500f02a0000200002z17;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4, 5, 6, 7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1]
def grouped3_0010 : List Nat := [1]
def grouped3_0011 : List Nat := [2]
def grouped3_0012 : List Nat := [2, 3]
def grouped3_0013 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record001" 38

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record001" "{\"ridges\":[[10,273],[18,529],[38,273],[39,529],[45,273],[45,274],[51,273],[52,273],[54,273],[57,529],[57,532],[62,529],[64,529],[65,529],[66,312],[67,568],[68,792],[70,848],[72,284],[73,538],[79,594],[80,312],[81,568]],\"owners\":[[10,273,[56,63,66,68,70],[38,45,51,52,54]],[38,273,[66,68,70],[10,45,51,52,54,56,63]],[45,273,[63,70],[10,38,51,52,54,56,66,68]],[51,273,[56,63,68,70],[10,38,45,52,54,66]],[52,273,[56,66,68],[10,38,45,51,54,63,70]],[54,273,[56,63,66,68,70],[10,38,45,51,52]],[45,274,[78],[10,38,51,52,54,72,80]],[18,529,[46,53,67,68,70],[39,57,62,64,65]],[39,529,[67,68,70],[18,46,53,57,62,64,65]],[57,529,[53,70],[18,39,46,62,64,65,67,68]],[62,529,[46,53,68,70],[18,39,57,64,65,67]],[64,529,[46,67,68],[18,39,53,57,62,65,70]],[65,529,[46,53,67,68,70],[18,39,57,62,64]],[57,532,[79],[18,39,62,64,65,73,81]],[73,538,[46],[]],[79,594,[53],[]],[72,284,[56],[]],[66,312,[80],[]],[80,312,[66],[]],[67,568,[81],[]],[81,568,[67],[]],[68,792,[],[]],[70,848,[],[]]],\"edges\":[[33,[10,38,45,51,52,54,56,63,66,68,70,72,78,80]],[34,[18,39,46,53,57,62,64,65,67,68,70,73,79,81]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-6,-5],[-7,-6],[-9,-7],[-10,-6],[-10,-9],[-11,-4],[-11,-6],[-12,-11],[-13,-11],[-14,-9],[-16,-3],[-16,-11],[-17,-6],[-18,-11],[-18,-17],[-22,-17],[-26,-17],[-1,11,14,17,19,20],[-3,17,19,20],[-5,14,20],[-7,11,14,19,20],[-8,11,17,19],[-10,11,14,17,19,20],[-5,23],[-2,6,9,18,19,20],[-4,18,19,20],[-12,9,20],[-13,6,9,19,20],[-15,6,18,19],[-16,6,9,18,19,20],[-12,24],[-22,6],[-24,9],[-21,11],[-17,25],[-25,17],[-18,26],[-26,18],[-19],[-20],[-27,3,5,7,8,10],[-28,4,12,13,15,16],[-29,27],[-29,28],[-30,29],[-31,30],[31],[-9,32],[-14,32],[-23,33],[-24,33],[-17,34],[-18,34],[-25,35],[-26,35],[-33,36],[-32,36],[-34,-35,37],[-36,-37,38],[-38],[1,3,5,7,8,10,11,14,17,19,20,21,23,25],[2,4,6,9,12,13,15,16,18,19,20,22,24,26]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":51,\"b\":46},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":46},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":39},{\"tag\":\"incompatible\",\"a\":56,\"b\":46},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":62,\"b\":56},{\"tag\":\"incompatible\",\"a\":63,\"b\":53},{\"tag\":\"incompatible\",\"a\":65,\"b\":38},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":46},{\"tag\":\"incompatible\",\"a\":67,\"b\":56},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":73,\"b\":66},{\"tag\":\"incompatible\",\"a\":81,\"b\":66},{\"tag\":\"mate\",\"ridge\":273,\"a\":10,\"owners\":[56,63,66,68,70]},{\"tag\":\"mate\",\"ridge\":273,\"a\":38,\"owners\":[66,68,70]},{\"tag\":\"mate\",\"ridge\":273,\"a\":45,\"owners\":[63,70]},{\"tag\":\"mate\",\"ridge\":273,\"a\":51,\"owners\":[56,63,68,70]},{\"tag\":\"mate\",\"ridge\":273,\"a\":52,\"owners\":[56,66,68]},{\"tag\":\"mate\",\"ridge\":273,\"a\":54,\"owners\":[56,63,66,68,70]},{\"tag\":\"mate\",\"ridge\":274,\"a\":45,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":529,\"a\":18,\"owners\":[46,53,67,68,70]},{\"tag\":\"mate\",\"ridge\":529,\"a\":39,\"owners\":[67,68,70]},{\"tag\":\"mate\",\"ridge\":529,\"a\":57,\"owners\":[53,70]},{\"tag\":\"mate\",\"ridge\":529,\"a\":62,\"owners\":[46,53,68,70]},{\"tag\":\"mate\",\"ridge\":529,\"a\":64,\"owners\":[46,67,68]},{\"tag\":\"mate\",\"ridge\":529,\"a\":65,\"owners\":[46,53,67,68,70]},{\"tag\":\"mate\",\"ridge\":532,\"a\":57,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":538,\"a\":73,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":594,\"a\":79,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":284,\"a\":72,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":312,\"a\":66,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":312,\"a\":80,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":568,\"a\":67,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":568,\"a\":81,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":792,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":848,\"a\":70,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[38,45,51,52,54],\"full_literals\":[-27,3,5,7,8,10]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[39,57,62,64,65],\"full_literals\":[-28,4,12,13,15,16]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-29,27,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-29,false,28],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-30,false,29],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-31,30,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":53,\"full_literals\":[-9,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-14,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-23,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":79,\"full_literals\":[-24,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-17,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-18,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":80,\"full_literals\":[-25,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":81,\"full_literals\":[-26,35]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-34,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-36,-37,38],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[10,38,45,51,52,54,56,63,66,68,70,72,78,80]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[18,39,46,53,57,62,64,65,67,68,70,73,79,81]}]}"
  "63 30 0 47 46 0\n64 29 0 63 45 0\n65 27 0 64 43 0\n66 28 0 64 44 0\n67 1 3 5 7 8 10 11 14 17 21 23 25 0 39 40 61 0\n68 2 4 6 9 12 13 15 16 18 22 24 26 0 39 40 62 0\n69 -17 -16 9 0 40 39 13 15 30 0\n70 -16 36 0 40 39 56 50 24 57 49 48 11 12 21 34 69 36 23 18 22 67 0\n71 17 11 36 0 40 39 34 57 49 21 56 50 24 19 36 23 18 22 67 0\n72 -17 36 0 40 39 70 56 51 31 57 48 13 15 16 17 28 26 29 25 68 0\n73 36 0 66 39 56 51 31 70 72 71 6 7 9 14 42 29 0\n74 -37 0 73 60 59 0\n75 -11 0 66 39 6 7 8 9 12 14 42 29 0\n76 18 6 9 16 0 40 39 32 28 33 27 26 38 29 25 68 0\n77 -18 0 74 37 53 55 58 0\n78 -6 17 0 40 75 39 65 22 19 1 2 4 41 0\n79 -9 17 0 75 39 65 40 22 19 3 5 10 41 20 0\n80 6 9 0 77 39 40 30 76 0\n81 17 0 78 79 80 0\n82 25 0 81 35 0\n83 34 0 81 52 0\n84 35 0 82 54 0\n85 0 83 84 74 58 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "358d534cc725c5723c4f25a56a3a1ea5655a362da8e9394e8ba1e4785e0fa59565391e655555352d58d9354d4b61d4745d0f65354cb31ce4b52ccb1ae1b46c5b0ee4751e1745c9715e0f43c4f07cac94a4a2a8a6858368388e0b951524a9295150d50d2342d28c530cc8b12c2b21c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db69b69a49349b4d36d249a4d34924924da4da492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 48), (facetIndex 59), (facetIndex 75)]))
 (.leaf ([(facetIndex 31), (facetIndex 53), (facetIndex 55), (facetIndex 56), (facetIndex 58)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 32), (facetIndex 71), (facetIndex 73), (facetIndex 74)]))
 (.leaf ([(facetIndex 40), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 33), (facetIndex 47), (facetIndex 49), (facetIndex 50)]))
 (.leaf ([(facetIndex 35), (facetIndex 60), (facetIndex 61)])))
 (.branch 7
 (.leaf ([(facetIndex 36), (facetIndex 70), (facetIndex 76), (facetIndex 78)]))
 (.leaf ([(facetIndex 29), (facetIndex 39), (facetIndex 51), (facetIndex 65), (facetIndex 67), (facetIndex 82)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1c0186090580e3802d041208f208db603e06a222b8z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

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
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record004" 77

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record004" "{\"ridges\":[[3,131],[15,164],[16,137],[24,164],[25,138],[28,140],[28,164],[39,49],[44,131],[44,137],[44,138],[48,131],[56,328],[58,137],[58,140],[60,37],[61,276],[61,336],[67,52],[73,584],[74,134],[74,138],[74,140],[76,532],[78,592],[82,592],[90,792]],\"owners\":[[60,37,[2,10,15],[13,55]],[74,134,[3,24,34,75],[20]],[39,49,[13,59,60],[7,47,48,51,63,64]],[67,52,[13,59,60],[22,51,75,76,83,84]],[61,276,[69,83,87],[14,35,53,60,77,85,89]],[56,328,[81,90],[17,45,65,72,85,88]],[61,336,[81,90],[18,49,65,77,85,89]],[76,532,[54,62,86,87,89],[23,36,70,78,84]],[73,584,[66,90],[26,46,57,82,86,88]],[78,592,[66,90],[27,50,62,82,86,89]],[82,592,[62,89],[27,50,66,78,86,90]],[90,792,[87],[]]],\"edges\":[[25,[4,10,16,19,25,28,39,43,51,55,63,64,67,71,79,80,83,84]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-17,-1],[-18,-5],[-18,-12],[-18,-16],[-19,-18],[-26,-18],[-27,-1],[-27,-3],[-27,-20],[-27,-22],[-27,-26],[-28,-14],[-28,-18],[-28,-24],[-29,-15],[-29,-25],[-30,-14],[-30,-18],[-31,-30],[-33,-30],[-35,-4],[-35,-15],[-35,-30],[-36,-1],[-36,-18],[-37,-12],[-37,-16],[-37,-17],[-37,-18],[-37,-19],[-37,-33],[-37,-36],[-38,-16],[-39,-37],[-42,-20],[-42,-21],[-42,-24],[-42,-28],[-42,-30],[-42,-31],[-42,-32],[-42,-34],[-42,-38],[-42,-40],[-42,-41],[-43,-20],[-43,-42],[-44,-19],[-44,-43],[-45,-12],[-46,-20],[-46,-42],[-46,-44],[-49,-8],[-49,-14],[-50,-1],[-51,-18],[-51,-44],[-51,-47],[-51,-50],[-52,-29],[-53,-42],[-54,-42],[-55,-20],[-55,-30],[-56,-21],[-56,-25],[-56,-29],[-56,-31],[-56,-40],[-56,-41],[-56,-46],[-56,-48],[-56,-52],[-56,-53],[-56,-54],[-56,-55],[-57,-12],[-57,-42],[-57,-56],[-58,-42],[-58,-56],[-59,-42],[-60,-12],[-60,-20],[-60,-30],[-60,-42],[-60,-44],[-60,-56],[-61,-13],[-37,1,4,6],[-2,-23,-27],[-49,2,9,17,50],[-7,-23,-35],[-10,-23,-49],[-20,5,36,37],[-11,-35,-49],[-44,5,36,37],[-38,45,57,60],[-6,-9,-11],[-34,55,62],[-38,55,62],[-51,32,39,59,60,61],[-48,43,62],[-52,43,62],[-56,39,61],[-62,60],[-63,17,27,36,50],[-64,14,31,33,34,35],[-65,13,15,47,48,49],[-66,21,22,23,24,25],[-67,16,26,28,29],[-68,18,37,38],[-69,19,46,51,52],[-70,12,20,30,42,44,56],[-71,63],[-71,64],[-72,65],[-72,66],[-73,71],[-73,72],[-74,67],[-74,68],[-75,69],[-75,70],[-76,74],[-76,75],[-77,73],[-77,76],[77],[3,4,7,8,10,11,20,22,30,33,40,41,44,47,53,54,57,58]],\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":34,\"b\":2},{\"tag\":\"incompatible\",\"a\":35,\"b\":13},{\"tag\":\"incompatible\",\"a\":35,\"b\":29},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":36,\"b\":35},{\"tag\":\"incompatible\",\"a\":47,\"b\":35},{\"tag\":\"incompatible\",\"a\":48,\"b\":2},{\"tag\":\"incompatible\",\"a\":48,\"b\":4},{\"tag\":\"incompatible\",\"a\":48,\"b\":39},{\"tag\":\"incompatible\",\"a\":48,\"b\":43},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":31},{\"tag\":\"incompatible\",\"a\":49,\"b\":35},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":32},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":51,\"b\":31},{\"tag\":\"incompatible\",\"a\":51,\"b\":35},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":55,\"b\":51},{\"tag\":\"incompatible\",\"a\":58,\"b\":10},{\"tag\":\"incompatible\",\"a\":58,\"b\":32},{\"tag\":\"incompatible\",\"a\":58,\"b\":51},{\"tag\":\"incompatible\",\"a\":59,\"b\":2},{\"tag\":\"incompatible\",\"a\":59,\"b\":35},{\"tag\":\"incompatible\",\"a\":60,\"b\":29},{\"tag\":\"incompatible\",\"a\":60,\"b\":33},{\"tag\":\"incompatible\",\"a\":60,\"b\":34},{\"tag\":\"incompatible\",\"a\":60,\"b\":35},{\"tag\":\"incompatible\",\"a\":60,\"b\":36},{\"tag\":\"incompatible\",\"a\":60,\"b\":55},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":33},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":65,\"b\":39},{\"tag\":\"incompatible\",\"a\":65,\"b\":40},{\"tag\":\"incompatible\",\"a\":65,\"b\":45},{\"tag\":\"incompatible\",\"a\":65,\"b\":49},{\"tag\":\"incompatible\",\"a\":65,\"b\":51},{\"tag\":\"incompatible\",\"a\":65,\"b\":53},{\"tag\":\"incompatible\",\"a\":65,\"b\":54},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":65,\"b\":61},{\"tag\":\"incompatible\",\"a\":65,\"b\":63},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":39},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":36},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":29},{\"tag\":\"incompatible\",\"a\":70,\"b\":39},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":74,\"b\":19},{\"tag\":\"incompatible\",\"a\":74,\"b\":31},{\"tag\":\"incompatible\",\"a\":75,\"b\":2},{\"tag\":\"incompatible\",\"a\":76,\"b\":35},{\"tag\":\"incompatible\",\"a\":76,\"b\":67},{\"tag\":\"incompatible\",\"a\":76,\"b\":71},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":50},{\"tag\":\"incompatible\",\"a\":79,\"b\":65},{\"tag\":\"incompatible\",\"a\":80,\"b\":65},{\"tag\":\"incompatible\",\"a\":81,\"b\":39},{\"tag\":\"incompatible\",\"a\":81,\"b\":51},{\"tag\":\"incompatible\",\"a\":82,\"b\":40},{\"tag\":\"incompatible\",\"a\":82,\"b\":46},{\"tag\":\"incompatible\",\"a\":82,\"b\":50},{\"tag\":\"incompatible\",\"a\":82,\"b\":53},{\"tag\":\"incompatible\",\"a\":82,\"b\":63},{\"tag\":\"incompatible\",\"a\":82,\"b\":64},{\"tag\":\"incompatible\",\"a\":82,\"b\":70},{\"tag\":\"incompatible\",\"a\":82,\"b\":73},{\"tag\":\"incompatible\",\"a\":82,\"b\":78},{\"tag\":\"incompatible\",\"a\":82,\"b\":79},{\"tag\":\"incompatible\",\"a\":82,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":81},{\"tag\":\"incompatible\",\"a\":83,\"b\":29},{\"tag\":\"incompatible\",\"a\":83,\"b\":65},{\"tag\":\"incompatible\",\"a\":83,\"b\":82},{\"tag\":\"incompatible\",\"a\":84,\"b\":65},{\"tag\":\"incompatible\",\"a\":84,\"b\":82},{\"tag\":\"incompatible\",\"a\":86,\"b\":65},{\"tag\":\"incompatible\",\"a\":87,\"b\":29},{\"tag\":\"incompatible\",\"a\":87,\"b\":39},{\"tag\":\"incompatible\",\"a\":87,\"b\":51},{\"tag\":\"incompatible\",\"a\":87,\"b\":65},{\"tag\":\"incompatible\",\"a\":87,\"b\":67},{\"tag\":\"incompatible\",\"a\":87,\"b\":82},{\"tag\":\"incompatible\",\"a\":89,\"b\":30},{\"tag\":\"mate\",\"ridge\":37,\"a\":60,\"owners\":[2,10,15]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[3,44,48]},{\"tag\":\"mate\",\"ridge\":134,\"a\":74,\"owners\":[3,24,34,75]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[16,44,58]},{\"tag\":\"three\",\"ridge\":138,\"vertices\":[25,44,74]},{\"tag\":\"mate\",\"ridge\":49,\"a\":39,\"owners\":[13,59,60]},{\"tag\":\"three\",\"ridge\":140,\"vertices\":[28,58,74]},{\"tag\":\"mate\",\"ridge\":52,\"a\":67,\"owners\":[13,59,60]},{\"tag\":\"mate\",\"ridge\":276,\"a\":61,\"owners\":[69,83,87]},{\"tag\":\"three\",\"ridge\":164,\"vertices\":[15,24,28]},{\"tag\":\"mate\",\"ridge\":328,\"a\":56,\"owners\":[81,90]},{\"tag\":\"mate\",\"ridge\":336,\"a\":61,\"owners\":[81,90]},{\"tag\":\"mate\",\"ridge\":532,\"a\":76,\"owners\":[54,62,86,87,89]},{\"tag\":\"mate\",\"ridge\":584,\"a\":73,\"owners\":[66,90]},{\"tag\":\"mate\",\"ridge\":592,\"a\":78,\"owners\":[66,90]},{\"tag\":\"mate\",\"ridge\":592,\"a\":82,\"owners\":[62,89]},{\"tag\":\"mate\",\"ridge\":792,\"a\":90,\"owners\":[87]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[34,48,59,75],\"full_literals\":[-63,17,27,36,50]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[31,53,55,56,58],\"full_literals\":[-64,14,31,33,34,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[30,32,71,73,74],\"full_literals\":[-65,13,15,47,48,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[40,43,44,45,46],\"full_literals\":[-66,21,22,23,24,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[33,47,49,50],\"full_literals\":[-67,16,26,28,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[35,60,61],\"full_literals\":[-68,18,37,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[36,70,76,78],\"full_literals\":[-69,19,46,51,52]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[29,39,51,65,67,82],\"full_literals\":[-70,12,20,30,42,44,56]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-71,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-72,65,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-73,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-74,67,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-75,69,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-75,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-76,74,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-76,false,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-77,73,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-77,false,76],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"edge\",\"edge\":25,\"owners\":[4,10,16,19,25,28,39,43,51,55,63,64,67,71,79,80,83,84]}]}"
  "132 73 0 130 128 0\n133 76 0 130 129 0\n134 71 0 132 120 0\n135 72 0 132 121 0\n136 74 0 133 126 0\n137 75 0 133 127 0\n138 63 0 134 116 0\n139 64 0 134 117 0\n140 65 0 135 118 0\n141 66 0 135 119 0\n142 67 0 136 122 0\n143 68 0 136 123 0\n144 69 0 137 124 0\n145 70 0 137 125 0\n146 -1 0 138 1 7 24 56 108 0\n147 -16 18 0 143 27 33 113 0\n148 -18 0 142 145 144 2 3 4 5 6 13 18 25 29 57 112 96 98 61 68 115 114 52 0\n149 -16 0 148 147 0\n150 -42 44 60 0 148 143 144 138 149 142 140 141 139 107 35 36 37 38 39 40 41 42 43 44 45 47 52 62 63 79 81 83 113 104 105 28 30 31 32 34 114 59 60 103 108 90 8 10 11 112 15 16 110 111 54 55 95 109 21 97 94 131 0\n151 -12 60 0 148 143 26 50 78 113 99 0\n152 -20 62 0 148 143 144 138 9 46 51 64 105 102 113 28 30 32 114 108 60 0\n153 -30 62 0 139 17 19 20 23 65 109 101 0\n154 44 56 60 0 145 107 153 152 151 150 115 0\n155 -44 62 0 144 48 49 53 58 105 114 0\n156 60 0 148 143 144 138 149 142 139 141 146 140 107 152 153 155 154 66 67 68 69 70 71 72 73 74 75 76 77 80 82 101 102 113 28 30 31 32 34 114 106 59 60 90 108 8 10 11 112 12 14 109 111 21 22 94 92 91 110 93 100 54 95 131 0\n157 -12 0 156 84 0\n158 -20 0 156 85 0\n159 -30 0 156 86 0\n160 -42 0 156 87 0\n161 -44 0 156 88 0\n162 -56 0 156 89 0\n163 0 160 162 145 158 159 157 161 115 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "d525c8f25a1ea56559362da4e53a1e1783ed46598e479d1715955558d5352d68d9354d8b61d1743d94d332cc7392d4b32c6b86c5b0ed8791d4749e1725c5783d0f13c1f2b1522a8a6458362382e94551924a929615454358348d0b54328d1314c3322c4b0ad0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db4936da49b6924924d269249249a49a492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 39), (facetIndex 51), (facetIndex 61), (facetIndex 77)]))
 (.leaf ([(facetIndex 35), (facetIndex 56), (facetIndex 57), (facetIndex 59), (facetIndex 60)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 44), (facetIndex 50), (facetIndex 53), (facetIndex 71)]))
 (.leaf ([(facetIndex 52), (facetIndex 78), (facetIndex 79)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 34), (facetIndex 40), (facetIndex 42)]))
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49)])))
 (.branch 7
 (.leaf ([(facetIndex 38), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66)]))
 (.leaf ([(facetIndex 43), (facetIndex 54), (facetIndex 70), (facetIndex 72)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6c00075c01b6d812091d30adb42f04182324z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 55), (facetIndex 58), (facetIndex 67)]))
 (.leaf ([(facetIndex 45), (facetIndex 68), (facetIndex 69), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 84), (facetIndex 85)]))
 (.branch 4
 (.leaf ([(facetIndex 74), (facetIndex 81), (facetIndex 83)]))
 (.leaf ([(facetIndex 80), (facetIndex 82)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1271c0024c8009z11;8z21;"⟩
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
def grouped2_0008 : List Nat := [4, 5]
def grouped2_0009 : List Nat := [4, 5, 6, 7]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record005" 69

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record005" "{\"ridges\":[[4,262],[17,273],[18,532],[23,592],[27,274],[30,274],[34,262],[35,524],[42,262],[45,538],[52,273],[52,274],[53,592],[56,524],[56,532],[57,524],[59,524],[59,584],[60,524],[63,532],[65,592],[66,532],[69,568],[70,584],[70,592],[71,273],[71,592],[75,332],[80,82],[81,120],[82,538],[83,568],[84,92],[85,836]],\"owners\":[[4,262,[27,75,78,79],[34,39,40,42]],[34,262,[27,78,79],[4,39,40,42,75]],[42,262,[27,75,78,79],[4,34,39,40]],[80,82,[9,30,44,50,81],[36,53,73,79,82]],[35,524,[83,84],[15,56,57,59,60,74,76]],[56,524,[76],[15,35,57,59,60,74,83,84]],[57,524,[74,76,84],[15,35,56,59,60,83]],[59,524,[74,83],[15,35,56,57,60,76,84]],[60,524,[74,76,83,84],[15,35,56,57,59]],[18,532,[74,80,83,84,85],[38,56,63,65,66]],[56,532,[80,85],[18,38,63,65,66,74,83,84]],[63,532,[74,80,84,85],[18,38,56,65,66,83]],[66,532,[74,80,83,84],[18,38,56,63,65,85]],[59,584,[82],[21,49,70,76,84]],[70,584,[76],[21,49,59,82,84]],[23,592,[80,82,84,85],[53,65,70,71]],[53,592,[84,85],[23,65,70,71,80,82]],[65,592,[82],[23,53,70,71,80,84,85]],[70,592,[80,85],[23,53,65,71,82,84]],[71,592,[80,82,84],[23,53,65,70,85]],[45,538,[74,82],[]],[82,538,[45,74],[]],[84,92,[55,73],[]],[75,332,[58],[]],[85,836,[67],[]],[81,120,[68],[]],[69,568,[83],[]],[83,568,[69],[]]],\"edges\":[[22,[4,17,27,34,39,40,42,58,62,64,66,67,75,78,79,85]],[34,[18,23,38,45,53,56,63,65,66,69,70,71,74,80,82,83,84,85]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-19,-2],[-19,-12],[-19,-16],[-19,-18],[-28,-19],[-37,-32],[-40,-15],[-40,-21],[-40,-36],[-40,-38],[-42,-11],[-42,-20],[-45,-10],[-45,-13],[-45,-30],[-45,-43],[-45,-44],[-48,-15],[-48,-21],[-48,-38],[-49,-15],[-49,-21],[-49,-36],[-49,-38],[-50,-42],[-1,6,41,43,44],[-8,6,43,44],[-14,6,41,43,44],[-45,2,7,16,18,46],[-3,-19,-37],[-6,-7,-19],[-9,48,49],[-23,42],[-24,40,42,49],[-26,40,48],[-27,40,42,48,49],[-4,40,45,48,49,50],[-23,45,50],[-29,40,45,49,50],[-32,40,45,48,49],[-26,47],[-36,42],[-5,45,47,49,50],[-20,49,50],[-31,47],[-36,45,50],[-37,45,47,49],[-17,40,47],[-47,17,40],[-49,22,39],[-41,25],[-50,33],[-46,34],[-35,48],[-48,35],[-51,9,23,24,26,27],[-52,10,16,18,20,37],[-53,19,43,44],[-54,15,21,36,38],[-55,51],[-56,52],[-56,53],[-57,55],[-57,56],[-58,54],[-59,58],[-60,57],[-60,59],[60],[-22,61],[-25,61],[-33,61],[-17,62],[-34,62],[-35,62],[-39,62],[-42,63],[-49,63],[-64,40,46,48],[-48,64],[-65,45,47],[-45,65],[-47,65],[-62,66],[-61,66],[-67,64,65],[-65,67],[-64,67],[-68,67],[-63,-67,68],[-66,-68,69],[-69],[1,3,6,8,12,13,14,25,28,30,32,33,41,43,44,50],[4,5,11,17,20,23,29,31,32,35,36,37,40,45,47,48,49,50]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":52,\"b\":9},{\"tag\":\"incompatible\",\"a\":52,\"b\":39},{\"tag\":\"incompatible\",\"a\":52,\"b\":44},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":62,\"b\":52},{\"tag\":\"incompatible\",\"a\":71,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":43},{\"tag\":\"incompatible\",\"a\":74,\"b\":54},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"incompatible\",\"a\":76,\"b\":38},{\"tag\":\"incompatible\",\"a\":76,\"b\":53},{\"tag\":\"incompatible\",\"a\":80,\"b\":36},{\"tag\":\"incompatible\",\"a\":80,\"b\":40},{\"tag\":\"incompatible\",\"a\":80,\"b\":64},{\"tag\":\"incompatible\",\"a\":80,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"incompatible\",\"a\":83,\"b\":43},{\"tag\":\"incompatible\",\"a\":83,\"b\":54},{\"tag\":\"incompatible\",\"a\":83,\"b\":72},{\"tag\":\"incompatible\",\"a\":84,\"b\":43},{\"tag\":\"incompatible\",\"a\":84,\"b\":54},{\"tag\":\"incompatible\",\"a\":84,\"b\":70},{\"tag\":\"incompatible\",\"a\":84,\"b\":72},{\"tag\":\"incompatible\",\"a\":85,\"b\":76},{\"tag\":\"mate\",\"ridge\":262,\"a\":4,\"owners\":[27,75,78,79]},{\"tag\":\"mate\",\"ridge\":262,\"a\":34,\"owners\":[27,78,79]},{\"tag\":\"mate\",\"ridge\":262,\"a\":42,\"owners\":[27,75,78,79]},{\"tag\":\"mate\",\"ridge\":82,\"a\":80,\"owners\":[9,30,44,50,81]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[17,52,71]},{\"tag\":\"three\",\"ridge\":274,\"vertices\":[27,30,52]},{\"tag\":\"mate\",\"ridge\":524,\"a\":35,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":524,\"a\":56,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":524,\"a\":57,\"owners\":[74,76,84]},{\"tag\":\"mate\",\"ridge\":524,\"a\":59,\"owners\":[74,83]},{\"tag\":\"mate\",\"ridge\":524,\"a\":60,\"owners\":[74,76,83,84]},{\"tag\":\"mate\",\"ridge\":532,\"a\":18,\"owners\":[74,80,83,84,85]},{\"tag\":\"mate\",\"ridge\":532,\"a\":56,\"owners\":[80,85]},{\"tag\":\"mate\",\"ridge\":532,\"a\":63,\"owners\":[74,80,84,85]},{\"tag\":\"mate\",\"ridge\":532,\"a\":66,\"owners\":[74,80,83,84]},{\"tag\":\"mate\",\"ridge\":584,\"a\":59,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":584,\"a\":70,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":592,\"a\":23,\"owners\":[80,82,84,85]},{\"tag\":\"mate\",\"ridge\":592,\"a\":53,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":592,\"a\":65,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":592,\"a\":70,\"owners\":[80,85]},{\"tag\":\"mate\",\"ridge\":592,\"a\":71,\"owners\":[80,82,84]},{\"tag\":\"mate\",\"ridge\":538,\"a\":45,\"owners\":[74,82]},{\"tag\":\"mate\",\"ridge\":538,\"a\":82,\"owners\":[45,74]},{\"tag\":\"mate\",\"ridge\":92,\"a\":84,\"owners\":[55,73]},{\"tag\":\"mate\",\"ridge\":332,\"a\":75,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":836,\"a\":85,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":120,\"a\":81,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":568,\"a\":69,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":568,\"a\":83,\"owners\":[69]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[35,56,57,59,60],\"full_literals\":[-51,9,23,24,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[36,44,50,53,71],\"full_literals\":[-52,10,16,18,20,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[52,78,79],\"full_literals\":[-53,19,43,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[43,54,70,72],\"full_literals\":[-54,15,21,36,38]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-57,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-60,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-60,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":55,\"full_literals\":[-22,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":58,\"full_literals\":[-25,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":67,\"full_literals\":[-33,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":45,\"full_literals\":[-17,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":68,\"full_literals\":[-34,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-35,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-39,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":76,\"full_literals\":[-42,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":84,\"full_literals\":[-49,63]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[74,81,83],\"full_literals\":[-64,40,46,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-48,64]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[80,82],\"full_literals\":[-65,45,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-45,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":82,\"full_literals\":[-47,65]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-66,-68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[4,17,27,34,39,40,42,58,62,64,66,67,75,78,79,85]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[18,23,38,45,53,56,63,65,66,69,70,71,74,80,82,83,84,85]}]}"
  "95 57 0 69 67 0\n96 59 0 69 68 0\n97 55 0 95 63 0\n98 56 0 95 64 0\n99 58 0 96 66 0\n100 51 0 97 60 0\n101 52 0 98 61 0\n102 53 0 98 62 0\n103 54 0 99 65 0\n104 -40 0 103 7 8 9 10 59 0\n105 -68 0 92 104 102 101 89 91 84 85 73 74 75 76 70 71 72 49 53 55 50 51 52 79 44 86 81 13 14 15 16 17 58 1 2 3 4 5 29 57 31 6 30 26 28 27 93 0\n106 48 63 0 104 100 78 77 34 33 32 35 36 56 0\n107 63 0 103 77 42 106 18 19 20 59 0\n108 -67 0 107 105 90 0\n109 -65 0 108 87 0\n110 -64 0 108 88 0\n111 -45 0 109 82 0\n112 -47 0 109 83 0\n113 -48 0 110 80 0\n114 -26 0 112 41 0\n115 -31 0 112 45 0\n116 -17 0 112 104 48 0\n117 -35 0 113 54 0\n118 42 49 0 113 104 114 100 32 33 34 36 56 0\n119 49 0 113 112 111 104 117 115 116 47 40 118 11 12 25 38 46 43 37 39 94 0\n120 -15 0 119 21 0\n121 -21 0 119 22 0\n122 -36 0 119 23 0\n123 -38 0 119 24 0\n124 0 121 123 103 120 122 59 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "35296a3a1e9564d8b653a1e1783ed46598e479555352d54d8745d0f743c4e334ccb31ce8b52ccb8ac6b86c5b0ed8751d2785c9715e0f43c4f07cac94952928aa299160d88e0ba51546492a4a5454352342d90d4328e1344c530ce0b22c4b0ad0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "24da49b6926d24db492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 40), (facetIndex 42), (facetIndex 54), (facetIndex 63), (facetIndex 74)]))
 (.leaf ([(facetIndex 39), (facetIndex 57), (facetIndex 65), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 46), (facetIndex 58), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 43), (facetIndex 44)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 45), (facetIndex 47), (facetIndex 59), (facetIndex 68), (facetIndex 70)]))
 (.leaf ([(facetIndex 55), (facetIndex 75), (facetIndex 76)])))
 (.branch 7
 (.leaf ([(facetIndex 38), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52)]))
 (.branch 8
 (.leaf ([(facetIndex 41), (facetIndex 53), (facetIndex 56)]))
 (.leaf ([(facetIndex 64)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "2200550000414001800004217507666664243307016333z23;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 60), (facetIndex 62)]))
 (.leaf ([(facetIndex 71), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 61), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 72), (facetIndex 77), (facetIndex 78)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "3c0740a008z1e;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record006" 73

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record006" "{\"ridges\":[[17,13],[26,14],[44,133],[44,134],[59,13],[62,13],[70,14],[72,540],[73,14],[77,120],[78,568]],\"owners\":[[44,133,[17,20,63],[3,40]],[44,134,[26,29,74],[3,40]],[72,540,[61],[]],[77,120,[66],[]],[78,568,[67],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-13,-8],[-13,-10],[-15,-8],[-15,-10],[-16,-13],[-16,-15],[-17,-13],[-17,-15],[-18,-13],[-18,-15],[-20,-13],[-20,-15],[-21,-13],[-21,-15],[-23,-13],[-23,-15],[-26,-2],[-26,-5],[-27,-13],[-27,-15],[-27,-26],[-28,-13],[-28,-15],[-28,-26],[-29,-6],[-29,-7],[-29,-9],[-29,-11],[-29,-19],[-30,-26],[-31,-9],[-31,-10],[-31,-22],[-31,-26],[-31,-27],[-31,-28],[-32,-29],[-32,-31],[-33,-13],[-33,-15],[-33,-26],[-34,-13],[-34,-15],[-34,-23],[-34,-26],[-35,-14],[-35,-25],[-35,-27],[-35,-28],[-35,-33],[-35,-34],[-36,-21],[-36,-33],[-36,-35],[-37,-4],[-37,-5],[-37,-27],[-37,-28],[-37,-33],[-37,-34],[-38,-37],[-41,-37],[-42,-31],[-42,-37],[-43,-24],[-43,-29],[-46,-35],[-47,-24],[-1,-26,-29],[-3,-37,-40],[-12,1,2,30],[-12,3,4,41],[-39,28],[-44,33],[-45,34],[-48,9,24,32,36],[-49,14,25,46,47],[-50,5,6,7,11,12],[-51,13,15,26,35,37],[-52,22,42,43],[-53,8,16,17,18,19,20],[-54,10,21,23],[-55,31],[-56,48],[-57,49],[-57,50],[-58,56],[-58,57],[-59,51,52],[-60,51],[-60,52],[-61,54],[-61,55],[-62,53,61],[-63,61],[-64,59],[-64,60,63],[-65,60],[-64,62],[-65,63],[-66,58,65],[-66,64],[66],[-67,27,29],[-68,38,40],[-69,28,33,34],[-28,69],[-33,69],[-34,69],[-70,39,44,45],[-71,67],[-71,68],[-72,69,70],[-73,71,72],[73]],\"atoms\":[{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":45,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":41},{\"tag\":\"incompatible\",\"a\":47,\"b\":38},{\"tag\":\"incompatible\",\"a\":47,\"b\":41},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":47},{\"tag\":\"incompatible\",\"a\":52,\"b\":45},{\"tag\":\"incompatible\",\"a\":52,\"b\":47},{\"tag\":\"incompatible\",\"a\":53,\"b\":45},{\"tag\":\"incompatible\",\"a\":53,\"b\":47},{\"tag\":\"incompatible\",\"a\":56,\"b\":45},{\"tag\":\"incompatible\",\"a\":56,\"b\":47},{\"tag\":\"incompatible\",\"a\":59,\"b\":20},{\"tag\":\"incompatible\",\"a\":59,\"b\":35},{\"tag\":\"incompatible\",\"a\":60,\"b\":45},{\"tag\":\"incompatible\",\"a\":60,\"b\":47},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":45},{\"tag\":\"incompatible\",\"a\":61,\"b\":47},{\"tag\":\"incompatible\",\"a\":61,\"b\":59},{\"tag\":\"incompatible\",\"a\":62,\"b\":36},{\"tag\":\"incompatible\",\"a\":62,\"b\":37},{\"tag\":\"incompatible\",\"a\":62,\"b\":39},{\"tag\":\"incompatible\",\"a\":62,\"b\":43},{\"tag\":\"incompatible\",\"a\":62,\"b\":51},{\"tag\":\"incompatible\",\"a\":63,\"b\":59},{\"tag\":\"incompatible\",\"a\":64,\"b\":39},{\"tag\":\"incompatible\",\"a\":64,\"b\":41},{\"tag\":\"incompatible\",\"a\":64,\"b\":55},{\"tag\":\"incompatible\",\"a\":64,\"b\":59},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":65,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":45},{\"tag\":\"incompatible\",\"a\":66,\"b\":47},{\"tag\":\"incompatible\",\"a\":66,\"b\":59},{\"tag\":\"incompatible\",\"a\":67,\"b\":45},{\"tag\":\"incompatible\",\"a\":67,\"b\":47},{\"tag\":\"incompatible\",\"a\":67,\"b\":56},{\"tag\":\"incompatible\",\"a\":67,\"b\":59},{\"tag\":\"incompatible\",\"a\":68,\"b\":46},{\"tag\":\"incompatible\",\"a\":68,\"b\":58},{\"tag\":\"incompatible\",\"a\":68,\"b\":60},{\"tag\":\"incompatible\",\"a\":68,\"b\":61},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":53},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":29},{\"tag\":\"incompatible\",\"a\":70,\"b\":35},{\"tag\":\"incompatible\",\"a\":70,\"b\":60},{\"tag\":\"incompatible\",\"a\":70,\"b\":61},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":75,\"b\":64},{\"tag\":\"incompatible\",\"a\":75,\"b\":70},{\"tag\":\"incompatible\",\"a\":76,\"b\":57},{\"tag\":\"incompatible\",\"a\":76,\"b\":62},{\"tag\":\"incompatible\",\"a\":79,\"b\":68},{\"tag\":\"incompatible\",\"a\":80,\"b\":57},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[17,59,62]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[26,70,73]},{\"tag\":\"mate\",\"ridge\":133,\"a\":44,\"owners\":[17,20,63]},{\"tag\":\"mate\",\"ridge\":134,\"a\":44,\"owners\":[26,29,74]},{\"tag\":\"mate\",\"ridge\":540,\"a\":72,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":120,\"a\":77,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":568,\"a\":78,\"owners\":[67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[39,57,65,69],\"full_literals\":[-48,9,24,32,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[46,58,79,80],\"full_literals\":[-49,14,25,46,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[35,36,37,43,44],\"full_literals\":[-50,5,6,7,11,12]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[45,47,59,68,70],\"full_literals\":[-51,13,15,26,35,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[55,75,76],\"full_literals\":[-52,22,42,43]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[38,48,49,50,51,52],\"full_literals\":[-53,8,16,17,18,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[41,53,56],\"full_literals\":[-54,10,21,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[64],\"full_literals\":[-55,31]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-58,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,51,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,53,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-64,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-64,60,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-65,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-66,58,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-66,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[60,62],\"full_literals\":[-67,27,29]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[71,73],\"full_literals\":[-68,38,40]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[61,66,67],\"full_literals\":[-69,28,33,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":61,\"full_literals\":[-28,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-33,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-34,69]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[72,77,78],\"full_literals\":[-70,39,44,45]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,67,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-71,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "116 64 0 103 102 0\n117 59 0 116 96 0\n118 62 0 116 99 0\n119 -36 -61 -69 0 93 83 36 32 92 52 53 82 106 44 0\n120 -34 -65 0 100 95 93 83 34 98 90 42 43 51 60 79 0\n121 -65 -69 0 98 100 90 95 93 83 34 36 120 106 39 40 50 59 79 0\n122 -13 34 -69 0 22 39 106 0\n123 -15 34 -69 0 23 40 106 0\n124 -26 34 -69 0 24 41 106 0\n125 -35 34 -69 0 49 50 106 0\n126 -37 34 -69 0 58 59 106 0\n127 51 -69 0 103 117 116 121 101 87 84 89 90 97 95 93 119 83 31 33 38 63 76 80 65 0\n128 -13 -69 0 42 122 0\n129 -15 -69 0 43 123 0\n130 -26 -69 0 45 124 0\n131 -35 -69 0 51 125 0\n132 -69 0 127 128 129 130 131 79 60 126 0\n133 -28 0 132 107 0\n134 -33 0 132 108 0\n135 -34 0 132 109 0\n136 -39 0 133 73 0\n137 -44 0 134 74 0\n138 -45 0 135 75 0\n139 -70 0 137 136 138 110 0\n140 -72 0 139 132 113 0\n141 71 0 140 115 114 0\n142 67 0 141 111 0\n143 68 0 141 112 0\n144 -37 0 142 143 103 55 56 57 61 62 64 104 105 25 26 28 66 70 72 78 86 88 101 98 100 91 95 80 93 33 83 0\n145 -13 0 142 118 1 2 5 7 9 11 13 15 19 82 104 92 29 94 81 0\n146 -15 0 142 118 3 4 6 8 10 12 14 16 20 82 104 92 29 94 81 0\n147 -26 0 142 103 17 18 21 30 34 104 83 25 26 28 69 93 71 95 78 100 86 101 88 0\n148 -58 -35 0 142 48 104 37 27 67 54 47 46 87 88 84 85 76 77 68 0\n149 -35 0 142 103 48 104 66 148 101 98 100 91 95 93 83 33 63 80 0\n150 -51 0 149 145 147 144 146 79 0\n151 52 0 150 117 89 0\n152 -60 0 150 90 0\n153 63 0 152 116 97 0\n154 61 0 153 95 0\n155 55 0 154 93 0\n156 31 0 155 83 0\n157 -22 0 156 33 0\n158 -27 0 156 35 0\n159 -42 0 156 63 0\n160 29 0 158 142 104 0\n161 43 0 159 157 151 80 0\n162 0 161 160 66 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00139.record006
