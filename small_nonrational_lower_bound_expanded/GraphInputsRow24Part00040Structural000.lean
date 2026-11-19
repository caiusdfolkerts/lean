module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00040Data
public import GraphInputsRow24Part00040Frames
public import GraphInputsRow24Part00040Leaves
public import GraphInputsRow24Part00040Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 37154834364760064, (certNat% 4), (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10), (certNat% 5), (certNat% 11)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 14), 63050394783186944, 2040693581152256]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), (certNat% 17), 2049489674174464, (certNat% 18), (certNat% 19)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 63059190876209152, (certNat% 21), (certNat% 16), (certNat% 22), 2040693581152256]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), 2075877953241088, 65302194596872192, 4503599627370496]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), 2084674046263296, (certNat% 26), (certNat% 27), 33776997205278720, (certNat% 18)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), 2225420124553216, (certNat% 18), 29273603736338432, (certNat% 30), (certNat% 31)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006
def vertexColumn : Fields := ⟨10, (certNat% 32)⟩
def kindColumn : Fields := ⟨3, (certNat% 33)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨87, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), (certNat% 36), 17042430230528, 8725724278030336]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), 17076789968896, 8743316464074752, (certNat% 39)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), (certNat% 42), (certNat% 43), 3975834046038016, 17111149707264]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 45), (certNat% 46), 17317308137472, (certNat% 47)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 49), (certNat% 36), 8514618045497344, (certNat% 50), (certNat% 51)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 53), (certNat% 54), 16698832846848, (certNat% 55), (certNat% 56)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), (certNat% 53), (certNat% 50), (certNat% 59), (certNat% 60)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 62), 12103217840128, 8444249301319680, (certNat% 56), (certNat% 63)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), (certNat% 50), 12610023981056, (certNat% 65), (certNat% 66), (certNat% 67)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 69), (certNat% 49), (certNat% 59), (certNat% 50), (certNat% 67)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), (certNat% 56), 8532210231541760, (certNat% 72)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), 10101763080192, 8655355533852672, (certNat% 50), (certNat% 49), (certNat% 67)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 75), (certNat% 76), 564065034305536, (certNat% 77), (certNat% 78), 8022036836253696]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c16 c7
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c19 c4
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1f25a8e87ac59564d8b61db0e3386e8785e0fa598e479c55554d4b51d70d3346d8745d0f65354e334ccb31cf0ba2e4b32e2b1ae1b16c3bc1d8751cc749c6785c9783d0f07cacc48aa29916158362384e0bb112a4a5454550d48d1342dc0ca384d1314c3382c8b12c2b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6d249349a4db4924d2692492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 61), (facetIndex 62), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 39), (facetIndex 67), (facetIndex 69), (facetIndex 70), (facetIndex 71)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 45)]))
 (.leaf ([(facetIndex 56), (facetIndex 68), (facetIndex 82)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 81), (facetIndex 83), (facetIndex 84), (facetIndex 85)])))
 (.branch 7
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 55), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60)]))
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 78), (facetIndex 79)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2dae8fc7e0024b200006db3d24924d92492292z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 63), (facetIndex 66)]))
 (.leaf ([(facetIndex 77), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 74)]))
 (.branch 4
 (.leaf ([(facetIndex 86), (facetIndex 87), (facetIndex 88)]))
 (.leaf ([(facetIndex 89)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "236c0001008092z36;"⟩
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
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0017 : List Nat := [1]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record003" 85

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record003" "{\"ridges\":[[5,259],[5,261],[9,522],[15,259],[15,769],[21,261],[21,273],[24,273],[24,529],[30,262],[30,274],[33,274],[33,530],[36,261],[37,522],[40,67],[41,259],[42,67],[43,259],[43,261],[44,259],[44,261],[45,769],[48,522],[50,522],[52,67],[52,515],[52,522],[53,522],[54,259],[54,522],[55,49],[55,50],[57,49],[57,259],[57,273],[57,274],[58,529],[58,530],[59,67],[59,81],[59,259],[64,73],[65,73],[67,49],[67,81],[68,49],[69,49],[69,261],[70,81],[70,261],[70,273],[71,529],[73,49],[73,521],[73,568],[74,81],[74,529],[74,600],[77,540],[81,52],[81,84],[82,50],[83,52],[83,262],[83,276],[84,84],[84,262],[84,274],[84,276],[85,276],[85,530],[87,50],[87,568],[88,530],[88,600]],\"owners\":[[5,261,[21,66,69,70,71],[36,41,43,44,45]],[21,261,[5,36,41,43,44,45,66],[69,70,71]],[36,261,[21,69,70,71],[5,41,43,44,45,66]],[43,261,[21,66,69,71],[5,36,41,44,45,70]],[44,261,[21,66,69,70,71],[5,36,41,43,45]],[69,261,[5,36,43,44,45,66],[21,41,70,71]],[70,261,[5,36,41,44,45,66],[21,43,69,71]],[30,262,[5,36,41,43,44,45,80],[83,84,85]],[83,262,[5,36,43,44,45,80],[30,41,84,85]],[84,262,[5,36,41,44,45,80],[30,43,83,85]],[64,73,[7,47,51,52,74],[17,49,62,65,72]],[65,73,[7,47,49,52,72,74],[17,51,62,64]],[52,515,[13,15,39,45,58],[9,37,50,53,60]],[73,521,[9,37,52,53,54,66],[48,50,63,74]],[9,522,[77,80,87,88],[37,48,50,52,53,54]],[37,522,[87,88],[9,48,50,52,53,54,77,80]],[48,522,[80],[9,37,50,52,53,54,77,87,88]],[50,522,[77,80,88],[9,37,48,52,53,54,87]],[52,522,[77,80,87],[9,37,48,50,53,54,88]],[53,522,[77,80,87,88],[9,37,48,50,52,54]],[54,522,[77,87,88],[9,37,48,50,52,53,80]],[69,49,[10,46,55,56,58,72,73],[19,57,61,67,68]],[70,81,[11,47,55,60,72,74],[20,59,62,67]],[74,529,[13,24,39,58,71],[48,60,63,73]],[88,530,[13,33,39,58,85],[48,60,77,87]],[15,769,[24,66,71],[45,54]],[45,769,[24],[15,54,66,71]],[81,52,[19,61,68,69],[28,67,75,82,83,89]],[83,52,[19,61,67,68,89],[28,69,75,81,82]],[81,84,[20,62,70],[29,67,76,84,89]],[84,84,[20,62,67,89],[29,70,76,81]],[83,276,[21,70,71],[30,69,84,85]],[84,276,[21,69,71],[30,70,83,85]],[85,276,[21,69,70],[30,71,83,84]],[77,540,[63],[]],[73,568,[87],[]],[87,568,[73],[]],[74,600,[88],[]],[88,600,[74],[]]],\"edges\":[[22,[5,21,30,36,41,43,44,45,66,69,70,71,80,83,84,85]],[29,[9,37,48,50,52,53,54,63,66,73,74,77,80,87,88]],[44,[15,24,33,45,54,66,71,80,85]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-18,-15],[-18,-16],[-18,-17],[-19,-18],[-20,-18],[-21,-18],[-22,-18],[-23,-18],[-24,-18],[-28,-3],[-28,-16],[-30,-3],[-30,-16],[-31,-15],[-31,-16],[-32,-2],[-32,-28],[-32,-30],[-33,-15],[-33,-18],[-33,-24],[-35,-34],[-36,-5],[-36,-6],[-36,-18],[-36,-20],[-36,-24],[-36,-35],[-37,-33],[-38,-4],[-38,-6],[-38,-17],[-38,-18],[-38,-22],[-38,-24],[-38,-34],[-38,-35],[-39,-31],[-39,-33],[-43,-34],[-46,-10],[-48,-9],[-48,-36],[-48,-41],[-48,-42],[-48,-46],[-49,-8],[-49,-38],[-49,-40],[-49,-42],[-49,-46],[-49,-47],[-49,-48],[-50,-36],[-50,-38],[-50,-42],[-50,-45],[-56,-50],[-57,-34],[-58,-44],[-59,-50],[-60,-46],[-62,-36],[-62,-48],[-63,-38],[-63,-49],[-64,-36],[-64,-38],[-64,-45],[-64,-59],[-65,-14],[-65,-25],[-65,-26],[-65,-37],[-65,-40],[-65,-41],[-65,-51],[-66,-14],[-66,-25],[-66,-26],[-66,-39],[-66,-40],[-66,-41],[-66,-51],[-66,-52],[-66,-54],[-66,-55],[-67,-14],[-67,-40],[-67,-41],[-67,-43],[-67,-54],[-67,-55],[-67,-57],[-19,-31,-38],[-21,-31,-38],[-1,-33,-36],[-1,-33,-38],[-7,-20,-38],[-7,-23,-38],[-20,-33,-38],[-22,-33,-36],[-23,-33,-36],[-23,-33,-38],[-1,10,45,48,49,50],[-10,1,15,20,22,23,24,45],[-15,10,48,49,50],[-22,10,45,48,50],[-23,10,45,48,49,50],[-48,1,15,22,23,24,45],[-49,1,15,20,23,24,45],[-12,1,15,20,22,23,24,59],[-62,1,15,22,23,24,59],[-63,1,15,20,23,24,59],[-43,2,26,30,31,53],[-44,2,26,28,31,51,53],[-31,6,7,18,24,37],[-52,3,16,31,32,33,45],[-3,56,59,65,66],[-16,65,66],[-27,59],[-29,56,59,66],[-31,56,59,65],[-32,56,59,65,66],[-33,56,65,66],[-48,4,25,34,35,37,51,52],[-34,-47,-52],[-36,-46,-52],[-34,-61,-65],[-49,5,26,34,39,51,53],[-38,-46,-53],[-10,-11,-36],[-11,-36,-49],[-12,-13,-36],[-13,-36,-63],[-53,6,11,18,37,50],[-11,-37,-53],[-37,-50,-53],[-66,6,13,18,37,64],[-13,-37,-66],[-37,-64,-66],[-7,11,45,50],[-24,11],[-60,8,40,47,48],[-62,8,40,46,47,67],[-60,9,41,49],[-63,9,41,46,67],[-62,10,49,50],[-63,10,48,50],[-64,10,48,49],[-56,42],[-52,65],[-65,52],[-53,66],[-66,53],[-68,14,40,41,43,44],[-69,18,46,48,49,50],[-70,15,16,17,19,20,21,22,23,24],[-71,35,47,61],[-72,27,28,29,30,31,32,33],[-73,60,62,63,64],[-74,25,26,34,36,37,38,39],[-75,54,55,57,58],[-76,68],[-76,69],[-77,70],[-77,71],[-78,76],[-78,77],[-79,72],[-79,73],[-80,74],[-80,75],[-81,79],[-81,80],[-82,78],[-82,81],[82],[-83,42,45],[-42,83],[-45,83],[-84,56,59],[-56,84],[-59,84],[-85,83,84],[-84,85],[-83,85],[1,10,12,15,20,22,23,24,45,48,49,50,59,62,63,64],[3,16,27,29,31,32,33,42,45,52,53,56,59,65,66],[7,11,13,24,33,45,50,59,64]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":39,\"b\":36},{\"tag\":\"incompatible\",\"a\":39,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":41,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":44,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":39},{\"tag\":\"incompatible\",\"a\":49,\"b\":9},{\"tag\":\"incompatible\",\"a\":49,\"b\":37},{\"tag\":\"incompatible\",\"a\":51,\"b\":9},{\"tag\":\"incompatible\",\"a\":51,\"b\":37},{\"tag\":\"incompatible\",\"a\":52,\"b\":36},{\"tag\":\"incompatible\",\"a\":52,\"b\":37},{\"tag\":\"incompatible\",\"a\":53,\"b\":7},{\"tag\":\"incompatible\",\"a\":53,\"b\":49},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":36},{\"tag\":\"incompatible\",\"a\":54,\"b\":39},{\"tag\":\"incompatible\",\"a\":54,\"b\":45},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":11},{\"tag\":\"incompatible\",\"a\":57,\"b\":13},{\"tag\":\"incompatible\",\"a\":57,\"b\":39},{\"tag\":\"incompatible\",\"a\":57,\"b\":41},{\"tag\":\"incompatible\",\"a\":57,\"b\":45},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":54},{\"tag\":\"incompatible\",\"a\":59,\"b\":10},{\"tag\":\"incompatible\",\"a\":59,\"b\":13},{\"tag\":\"incompatible\",\"a\":59,\"b\":38},{\"tag\":\"incompatible\",\"a\":59,\"b\":39},{\"tag\":\"incompatible\",\"a\":59,\"b\":43},{\"tag\":\"incompatible\",\"a\":59,\"b\":45},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":56},{\"tag\":\"incompatible\",\"a\":60,\"b\":52},{\"tag\":\"incompatible\",\"a\":60,\"b\":54},{\"tag\":\"incompatible\",\"a\":64,\"b\":55},{\"tag\":\"incompatible\",\"a\":67,\"b\":21},{\"tag\":\"incompatible\",\"a\":69,\"b\":20},{\"tag\":\"incompatible\",\"a\":69,\"b\":57},{\"tag\":\"incompatible\",\"a\":69,\"b\":62},{\"tag\":\"incompatible\",\"a\":69,\"b\":63},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":19},{\"tag\":\"incompatible\",\"a\":70,\"b\":59},{\"tag\":\"incompatible\",\"a\":70,\"b\":61},{\"tag\":\"incompatible\",\"a\":70,\"b\":63},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":57},{\"tag\":\"incompatible\",\"a\":71,\"b\":59},{\"tag\":\"incompatible\",\"a\":71,\"b\":63},{\"tag\":\"incompatible\",\"a\":71,\"b\":66},{\"tag\":\"incompatible\",\"a\":77,\"b\":71},{\"tag\":\"incompatible\",\"a\":78,\"b\":55},{\"tag\":\"incompatible\",\"a\":79,\"b\":65},{\"tag\":\"incompatible\",\"a\":80,\"b\":71},{\"tag\":\"incompatible\",\"a\":81,\"b\":67},{\"tag\":\"incompatible\",\"a\":83,\"b\":57},{\"tag\":\"incompatible\",\"a\":83,\"b\":69},{\"tag\":\"incompatible\",\"a\":84,\"b\":59},{\"tag\":\"incompatible\",\"a\":84,\"b\":70},{\"tag\":\"incompatible\",\"a\":85,\"b\":57},{\"tag\":\"incompatible\",\"a\":85,\"b\":59},{\"tag\":\"incompatible\",\"a\":85,\"b\":66},{\"tag\":\"incompatible\",\"a\":85,\"b\":80},{\"tag\":\"incompatible\",\"a\":87,\"b\":35},{\"tag\":\"incompatible\",\"a\":87,\"b\":46},{\"tag\":\"incompatible\",\"a\":87,\"b\":47},{\"tag\":\"incompatible\",\"a\":87,\"b\":58},{\"tag\":\"incompatible\",\"a\":87,\"b\":61},{\"tag\":\"incompatible\",\"a\":87,\"b\":62},{\"tag\":\"incompatible\",\"a\":87,\"b\":72},{\"tag\":\"incompatible\",\"a\":88,\"b\":35},{\"tag\":\"incompatible\",\"a\":88,\"b\":46},{\"tag\":\"incompatible\",\"a\":88,\"b\":47},{\"tag\":\"incompatible\",\"a\":88,\"b\":60},{\"tag\":\"incompatible\",\"a\":88,\"b\":61},{\"tag\":\"incompatible\",\"a\":88,\"b\":62},{\"tag\":\"incompatible\",\"a\":88,\"b\":72},{\"tag\":\"incompatible\",\"a\":88,\"b\":73},{\"tag\":\"incompatible\",\"a\":88,\"b\":75},{\"tag\":\"incompatible\",\"a\":88,\"b\":76},{\"tag\":\"incompatible\",\"a\":89,\"b\":35},{\"tag\":\"incompatible\",\"a\":89,\"b\":61},{\"tag\":\"incompatible\",\"a\":89,\"b\":62},{\"tag\":\"incompatible\",\"a\":89,\"b\":64},{\"tag\":\"incompatible\",\"a\":89,\"b\":75},{\"tag\":\"incompatible\",\"a\":89,\"b\":76},{\"tag\":\"incompatible\",\"a\":89,\"b\":78},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[40,52,59]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[42,52,59]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[5,54,57]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[5,54,59]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[15,41,59]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[15,44,59]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[41,54,59]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[43,54,57]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[44,54,57]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[44,54,59]},{\"tag\":\"mate\",\"ridge\":261,\"a\":5,\"owners\":[21,66,69,70,71]},{\"tag\":\"mate\",\"ridge\":261,\"a\":21,\"owners\":[5,36,41,43,44,45,66]},{\"tag\":\"mate\",\"ridge\":261,\"a\":36,\"owners\":[21,69,70,71]},{\"tag\":\"mate\",\"ridge\":261,\"a\":43,\"owners\":[21,66,69,71]},{\"tag\":\"mate\",\"ridge\":261,\"a\":44,\"owners\":[21,66,69,70,71]},{\"tag\":\"mate\",\"ridge\":261,\"a\":69,\"owners\":[5,36,43,44,45,66]},{\"tag\":\"mate\",\"ridge\":261,\"a\":70,\"owners\":[5,36,41,44,45,66]},{\"tag\":\"mate\",\"ridge\":262,\"a\":30,\"owners\":[5,36,41,43,44,45,80]},{\"tag\":\"mate\",\"ridge\":262,\"a\":83,\"owners\":[5,36,43,44,45,80]},{\"tag\":\"mate\",\"ridge\":262,\"a\":84,\"owners\":[5,36,41,44,45,80]},{\"tag\":\"mate\",\"ridge\":73,\"a\":64,\"owners\":[7,47,51,52,74]},{\"tag\":\"mate\",\"ridge\":73,\"a\":65,\"owners\":[7,47,49,52,72,74]},{\"tag\":\"mate\",\"ridge\":515,\"a\":52,\"owners\":[13,15,39,45,58]},{\"tag\":\"mate\",\"ridge\":521,\"a\":73,\"owners\":[9,37,52,53,54,66]},{\"tag\":\"mate\",\"ridge\":522,\"a\":9,\"owners\":[77,80,87,88]},{\"tag\":\"mate\",\"ridge\":522,\"a\":37,\"owners\":[87,88]},{\"tag\":\"mate\",\"ridge\":522,\"a\":48,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":522,\"a\":50,\"owners\":[77,80,88]},{\"tag\":\"mate\",\"ridge\":522,\"a\":52,\"owners\":[77,80,87]},{\"tag\":\"mate\",\"ridge\":522,\"a\":53,\"owners\":[77,80,87,88]},{\"tag\":\"mate\",\"ridge\":522,\"a\":54,\"owners\":[77,87,88]},{\"tag\":\"mate\",\"ridge\":49,\"a\":69,\"owners\":[10,46,55,56,58,72,73]},{\"tag\":\"three\",\"ridge\":49,\"vertices\":[55,68,73]},{\"tag\":\"three\",\"ridge\":49,\"vertices\":[57,67,73]},{\"tag\":\"three\",\"ridge\":50,\"vertices\":[55,82,87]},{\"tag\":\"mate\",\"ridge\":81,\"a\":70,\"owners\":[11,47,55,60,72,74]},{\"tag\":\"three\",\"ridge\":81,\"vertices\":[59,67,74]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[21,24,57]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[24,57,70]},{\"tag\":\"three\",\"ridge\":274,\"vertices\":[30,33,57]},{\"tag\":\"three\",\"ridge\":274,\"vertices\":[33,57,84]},{\"tag\":\"mate\",\"ridge\":529,\"a\":74,\"owners\":[13,24,39,58,71]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[24,58,74]},{\"tag\":\"three\",\"ridge\":529,\"vertices\":[58,71,74]},{\"tag\":\"mate\",\"ridge\":530,\"a\":88,\"owners\":[13,33,39,58,85]},{\"tag\":\"three\",\"ridge\":530,\"vertices\":[33,58,88]},{\"tag\":\"three\",\"ridge\":530,\"vertices\":[58,85,88]},{\"tag\":\"mate\",\"ridge\":769,\"a\":15,\"owners\":[24,66,71]},{\"tag\":\"mate\",\"ridge\":769,\"a\":45,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":52,\"a\":81,\"owners\":[19,61,68,69]},{\"tag\":\"mate\",\"ridge\":52,\"a\":83,\"owners\":[19,61,67,68,89]},{\"tag\":\"mate\",\"ridge\":84,\"a\":81,\"owners\":[20,62,70]},{\"tag\":\"mate\",\"ridge\":84,\"a\":84,\"owners\":[20,62,67,89]},{\"tag\":\"mate\",\"ridge\":276,\"a\":83,\"owners\":[21,70,71]},{\"tag\":\"mate\",\"ridge\":276,\"a\":84,\"owners\":[21,69,71]},{\"tag\":\"mate\",\"ridge\":276,\"a\":85,\"owners\":[21,69,70]},{\"tag\":\"mate\",\"ridge\":540,\"a\":77,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":568,\"a\":73,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":568,\"a\":87,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":600,\"a\":74,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":600,\"a\":88,\"owners\":[74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[35,61,62,64,65],\"full_literals\":[-68,14,40,41,43,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[39,67,69,70,71],\"full_literals\":[-69,18,46,48,49,50]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[36,37,38,40,41,42,43,44,45],\"full_literals\":[-70,15,16,17,19,20,21,22,23,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[56,68,82],\"full_literals\":[-71,35,47,61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[48,49,50,51,52,53,54],\"full_literals\":[-72,27,28,29,30,31,32,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[81,83,84,85],\"full_literals\":[-73,60,62,63,64]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[46,47,55,57,58,59,60],\"full_literals\":[-74,25,26,34,36,37,38,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[75,76,78,79],\"full_literals\":[-75,54,55,57,58]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-76,68,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-76,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-77,70,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,false,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-78,76,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-78,false,77],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-79,72,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,false,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-80,74,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,false,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-81,79,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-81,false,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-82,78,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-82,false,81],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[63,66],\"full_literals\":[-83,42,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-42,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-45,83]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[77,80],\"full_literals\":[-84,56,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-56,84]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-59,84]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,83,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-84,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-83,false,85],\"grouped\":true,\"kind\":3},{\"tag\":\"edge\",\"edge\":22,\"owners\":[5,21,30,36,41,43,44,45,66,69,70,71,80,83,84,85]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[9,37,48,50,52,53,54,63,66,73,74,77,80,87,88]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[15,24,33,45,54,66,71,80,85]}]}"
  "191 78 0 178 176 0\n192 81 0 178 177 0\n193 76 0 191 168 0\n194 77 0 191 169 0\n195 79 0 192 174 0\n196 80 0 192 175 0\n197 68 0 193 164 0\n198 69 0 193 165 0\n199 70 0 194 166 0\n200 71 0 194 167 0\n201 72 0 195 170 0\n202 73 0 195 171 0\n203 74 0 196 172 0\n204 75 0 196 173 0\n205 -67 0 197 204 88 89 90 91 92 93 94 156 163 60 0\n206 65 66 85 0 186 183 184 122 154 121 187 181 180 120 152 119 123 124 125 189 0\n207 -3 31 32 33 29 27 0 201 10 12 160 0\n208 31 32 33 66 85 0 201 206 153 186 183 184 122 121 187 181 207 118 11 13 160 0\n209 -35 39 -65 0 203 74 73 72 22 28 37 162 0\n210 -34 35 -65 0 200 153 129 127 159 0\n211 -36 34 39 -52 51 26 53 0 198 23 25 43 54 128 130 157 0\n212 -31 -65 53 0 203 199 153 77 74 73 72 14 15 38 209 210 211 162 31 32 33 34 35 95 96 117 99 100 158 0\n213 -32 31 51 41 40 26 14 53 0 197 16 17 18 116 115 156 0\n214 66 85 0 203 187 181 186 184 154 206 71 72 73 74 75 76 77 153 212 213 208 19 21 39 209 210 211 162 34 48 55 65 68 98 101 104 112 106 113 110 188 0\n215 -38 35 -33 -66 0 198 29 20 155 85 84 79 30 36 48 55 131 126 157 0\n216 -36 -33 85 0 21 19 187 181 186 184 26 43 54 63 67 97 102 103 112 106 114 111 188 0\n217 -34 -66 0 197 204 87 86 83 82 78 40 59 156 163 60 0\n218 -33 85 0 203 214 217 81 80 79 29 216 162 37 215 0\n219 -38 37 -66 0 198 217 155 85 84 79 30 33 37 48 55 131 126 157 0\n220 37 85 0 203 214 217 155 81 80 79 187 181 186 184 219 162 24 25 26 27 43 54 63 67 136 139 132 133 134 135 105 108 109 107 188 0\n221 85 0 186 187 184 181 214 155 218 220 137 138 140 141 142 143 190 0\n222 -50 0 221 56 57 58 61 179 182 185 0\n223 -18 0 199 1 2 3 4 5 6 7 8 9 158 0\n224 48 49 0 202 222 198 223 157 41 62 148 149 150 161 0\n225 49 0 205 202 221 224 42 44 45 46 64 147 146 151 161 69 70 179 182 185 0\n226 -8 0 225 47 0\n227 -40 0 225 49 0\n228 -42 0 225 50 0\n229 -46 0 225 51 0\n230 -47 0 225 52 0\n231 -48 0 225 53 0\n232 -63 0 225 66 0\n233 -62 0 226 227 229 230 205 145 0\n234 -60 0 226 227 230 231 144 0\n235 -56 0 228 151 0\n236 64 0 234 202 232 233 161 0\n237 -45 0 236 69 0\n238 -59 0 236 70 0\n239 -83 0 237 228 179 0\n240 -84 0 238 235 182 0\n241 0 239 240 221 185 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "bc1f31a2e87aa5a5635a362d876c394e4b8ae1ba1e2785e0fb192e479a5655356352d475c354d4b4ad1b61d2745d0f713a4e5334e331cf0b52d2b2ac6b86d1b26e8761e4751cc789d2719e1725c570de0f23c1f2c85a0eb062990e1382e2c4590e7052950d1342dc0ca384c9314c3342c4b0ac1b81d0721c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db49b6d34924da4d26db4d2493692492492492492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 40), (facetIndex 43), (facetIndex 45), (facetIndex 54), (facetIndex 69), (facetIndex 87)]))
 (.leaf ([(facetIndex 33), (facetIndex 35), (facetIndex 47), (facetIndex 51), (facetIndex 66), (facetIndex 77), (facetIndex 84), (facetIndex 95)])))
 (.branch 3
 (.leaf ([(facetIndex 32), (facetIndex 52), (facetIndex 67), (facetIndex 85)]))
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 61), (facetIndex 62), (facetIndex 71), (facetIndex 79), (facetIndex 80), (facetIndex 89)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 39), (facetIndex 50), (facetIndex 55), (facetIndex 65), (facetIndex 76), (facetIndex 83), (facetIndex 94)]))
 (.leaf ([(facetIndex 48), (facetIndex 49), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60)])))
 (.branch 7
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 44), (facetIndex 46)]))
 (.leaf ([(facetIndex 53), (facetIndex 68), (facetIndex 86)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "3000181d180360c0006074600ddb6d83a32d3861b08db20az18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 64), (facetIndex 78)]))
 (.leaf ([(facetIndex 82), (facetIndex 96)])))
 (.branch 3
 (.leaf ([(facetIndex 63), (facetIndex 70), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 75)]))
 (.branch 4
 (.leaf ([(facetIndex 81), (facetIndex 88), (facetIndex 90), (facetIndex 91), (facetIndex 92), (facetIndex 93)]))
 (.leaf ([(facetIndex 97), (facetIndex 98)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12101b6c30000580004920800004z2f;"⟩
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
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [2]
def grouped3_0020 : List Nat := [2, 3, 4]
def grouped3_0021 : List Nat := [3]
def grouped3_0022 : List Nat := [3, 4]
def grouped3_0023 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record005" 79

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record005" "{\"ridges\":[[13,530],[22,81],[23,145],[30,82],[31,146],[38,530],[49,530],[56,530],[58,530],[59,530],[60,530],[62,81],[71,145],[72,564],[74,596],[75,660],[77,145],[78,792],[80,82],[89,146],[95,146],[96,530],[96,792]],\"owners\":[[22,81,[11,36,55,57,58,70,73,74],[62,76]],[62,81,[11,55,57,58],[22,36,70,73,74,76]],[30,82,[11,36,55,57,58,88,91,92],[80,94]],[80,82,[11,55,57,58],[30,36,88,91,92,94]],[23,145,[12,37,47,57,59,63,73,75],[71,77]],[71,145,[12,47,57,59],[23,37,63,73,75,77]],[77,145,[12,37,57,59,73,75],[23,47,63,71]],[31,146,[12,37,47,57,59,81,91,93],[89,95]],[89,146,[12,47,57,59],[31,37,81,91,93,95]],[95,146,[12,37,57,59,91,93],[31,47,81,89]],[13,530,[82,90,92,93,96],[38,49,56,58,59,60]],[38,530,[96],[13,49,56,58,59,60,82,90,92,93]],[49,530,[90,92,93],[13,38,56,58,59,60,82,96]],[56,530,[82,92,93,96],[13,38,49,58,59,60,90]],[58,530,[82,90,93,96],[13,38,49,56,59,60,92]],[59,530,[82,90,92,96],[13,38,49,56,58,60,93]],[60,530,[82,90,92,93],[13,38,49,56,58,59,96]],[96,530,[13,38,56,58,59,90,92,93],[49,60,82]],[72,564,[90],[]],[74,596,[92],[]],[75,660,[93],[]],[78,792,[96],[]],[96,792,[78],[]]],\"edges\":[[31,[11,22,30,36,55,57,58,62,70,73,74,76,80,88,91,92,94,97]],[32,[12,23,31,37,47,57,59,63,71,73,75,77,81,89,91,93,95,98]],[34,[13,38,49,56,58,59,60,64,72,74,75,78,82,90,92,93,96]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-12,-11],[-13,-9],[-13,-10],[-14,-9],[-14,-10],[-15,-11],[-16,-9],[-16,-10],[-17,-11],[-18,-9],[-18,-10],[-24,-1],[-24,-23],[-25,-3],[-25,-24],[-26,-2],[-26,-19],[-26,-25],[-27,-1],[-27,-23],[-27,-25],[-27,-26],[-32,-29],[-32,-30],[-35,-32],[-42,-40],[-43,-32],[-44,-32],[-46,-29],[-46,-30],[-46,-35],[-46,-43],[-46,-44],[-49,-30],[-49,-32],[-49,-44],[-49,-46],[-50,-9],[-50,-10],[-50,-29],[-50,-30],[-50,-35],[-50,-43],[-50,-44],[-50,-49],[-52,-9],[-52,-10],[-52,-29],[-52,-30],[-52,-35],[-52,-43],[-52,-44],[-52,-49],[-53,-9],[-53,-10],[-53,-29],[-53,-30],[-53,-35],[-53,-43],[-53,-44],[-53,-49],[-56,-8],[-56,-20],[-56,-21],[-56,-22],[-56,-28],[-56,-33],[-56,-47],[-56,-54],[-4,1,9,23,25,26,34,37,38],[-30,1,23,25,26],[-6,1,9,23,25,26,48,51,52],[-44,1,23,25,26],[-5,2,10,19,25,27,31,37,39],[-35,2,19,25,27],[-41,2,10,25,27,37,39],[-7,2,10,19,25,27,45,51,53],[-49,2,19,25,27],[-55,2,10,25,27,51,53],[-3,46,50,52,53,56],[-11,56],[-21,50,52,53],[-24,46,52,53,56],[-26,46,50,53,56],[-27,46,50,52,56],[-28,46,50,52,53],[-56,3,11,24,26,27,50,52,53],[-36,50],[-38,52],[-39,53],[-42,56],[-56,42],[-59,8,12,15,17,22,33,47],[-60,9,10,11,29,30,35,43,44,49],[-61,20,21,24,25,26,27,28],[-62,13,14,16,18],[-63,59],[-64,60],[-65,63],[-65,64],[-66,61],[-67,62],[-68,66],[-68,67],[-69,65],[-69,68],[69],[-70,32,42],[-32,70],[-42,70],[-71,46,56],[-46,71],[-56,71],[-31,72],[-34,72],[-37,72],[-38,72],[-39,72],[-45,73],[-48,73],[-50,73],[-51,73],[-52,73],[-53,73],[-57,74],[-58,74],[-75,70,71],[-71,75],[-70,75],[-70,-71,76],[-74,77],[-73,77],[-77,78],[-72,78],[-76,-78,79],[-79],[1,4,6,9,23,25,26,30,34,37,38,40,44,48,51,52,54,57],[2,5,7,10,19,25,27,31,35,37,39,41,45,49,51,53,55,58],[3,11,21,24,26,27,28,32,36,38,39,42,46,50,52,53,56]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":40,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":36},{\"tag\":\"incompatible\",\"a\":41,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":36},{\"tag\":\"incompatible\",\"a\":42,\"b\":37},{\"tag\":\"incompatible\",\"a\":43,\"b\":38},{\"tag\":\"incompatible\",\"a\":44,\"b\":36},{\"tag\":\"incompatible\",\"a\":44,\"b\":37},{\"tag\":\"incompatible\",\"a\":45,\"b\":38},{\"tag\":\"incompatible\",\"a\":46,\"b\":36},{\"tag\":\"incompatible\",\"a\":46,\"b\":37},{\"tag\":\"incompatible\",\"a\":56,\"b\":11},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":13},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":12},{\"tag\":\"incompatible\",\"a\":58,\"b\":47},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":11},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":71,\"b\":64},{\"tag\":\"incompatible\",\"a\":78,\"b\":76},{\"tag\":\"incompatible\",\"a\":79,\"b\":64},{\"tag\":\"incompatible\",\"a\":80,\"b\":64},{\"tag\":\"incompatible\",\"a\":82,\"b\":61},{\"tag\":\"incompatible\",\"a\":82,\"b\":62},{\"tag\":\"incompatible\",\"a\":82,\"b\":71},{\"tag\":\"incompatible\",\"a\":82,\"b\":79},{\"tag\":\"incompatible\",\"a\":82,\"b\":80},{\"tag\":\"incompatible\",\"a\":89,\"b\":62},{\"tag\":\"incompatible\",\"a\":89,\"b\":64},{\"tag\":\"incompatible\",\"a\":89,\"b\":80},{\"tag\":\"incompatible\",\"a\":89,\"b\":82},{\"tag\":\"incompatible\",\"a\":90,\"b\":36},{\"tag\":\"incompatible\",\"a\":90,\"b\":37},{\"tag\":\"incompatible\",\"a\":90,\"b\":61},{\"tag\":\"incompatible\",\"a\":90,\"b\":62},{\"tag\":\"incompatible\",\"a\":90,\"b\":71},{\"tag\":\"incompatible\",\"a\":90,\"b\":79},{\"tag\":\"incompatible\",\"a\":90,\"b\":80},{\"tag\":\"incompatible\",\"a\":90,\"b\":89},{\"tag\":\"incompatible\",\"a\":92,\"b\":36},{\"tag\":\"incompatible\",\"a\":92,\"b\":37},{\"tag\":\"incompatible\",\"a\":92,\"b\":61},{\"tag\":\"incompatible\",\"a\":92,\"b\":62},{\"tag\":\"incompatible\",\"a\":92,\"b\":71},{\"tag\":\"incompatible\",\"a\":92,\"b\":79},{\"tag\":\"incompatible\",\"a\":92,\"b\":80},{\"tag\":\"incompatible\",\"a\":92,\"b\":89},{\"tag\":\"incompatible\",\"a\":93,\"b\":36},{\"tag\":\"incompatible\",\"a\":93,\"b\":37},{\"tag\":\"incompatible\",\"a\":93,\"b\":61},{\"tag\":\"incompatible\",\"a\":93,\"b\":62},{\"tag\":\"incompatible\",\"a\":93,\"b\":71},{\"tag\":\"incompatible\",\"a\":93,\"b\":79},{\"tag\":\"incompatible\",\"a\":93,\"b\":80},{\"tag\":\"incompatible\",\"a\":93,\"b\":89},{\"tag\":\"incompatible\",\"a\":96,\"b\":34},{\"tag\":\"incompatible\",\"a\":96,\"b\":48},{\"tag\":\"incompatible\",\"a\":96,\"b\":49},{\"tag\":\"incompatible\",\"a\":96,\"b\":54},{\"tag\":\"incompatible\",\"a\":96,\"b\":60},{\"tag\":\"incompatible\",\"a\":96,\"b\":69},{\"tag\":\"incompatible\",\"a\":96,\"b\":87},{\"tag\":\"incompatible\",\"a\":96,\"b\":94},{\"tag\":\"mate\",\"ridge\":81,\"a\":22,\"owners\":[11,36,55,57,58,70,73,74]},{\"tag\":\"mate\",\"ridge\":81,\"a\":62,\"owners\":[11,55,57,58]},{\"tag\":\"mate\",\"ridge\":82,\"a\":30,\"owners\":[11,36,55,57,58,88,91,92]},{\"tag\":\"mate\",\"ridge\":82,\"a\":80,\"owners\":[11,55,57,58]},{\"tag\":\"mate\",\"ridge\":145,\"a\":23,\"owners\":[12,37,47,57,59,63,73,75]},{\"tag\":\"mate\",\"ridge\":145,\"a\":71,\"owners\":[12,47,57,59]},{\"tag\":\"mate\",\"ridge\":145,\"a\":77,\"owners\":[12,37,57,59,73,75]},{\"tag\":\"mate\",\"ridge\":146,\"a\":31,\"owners\":[12,37,47,57,59,81,91,93]},{\"tag\":\"mate\",\"ridge\":146,\"a\":89,\"owners\":[12,47,57,59]},{\"tag\":\"mate\",\"ridge\":146,\"a\":95,\"owners\":[12,37,57,59,91,93]},{\"tag\":\"mate\",\"ridge\":530,\"a\":13,\"owners\":[82,90,92,93,96]},{\"tag\":\"mate\",\"ridge\":530,\"a\":38,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":530,\"a\":49,\"owners\":[90,92,93]},{\"tag\":\"mate\",\"ridge\":530,\"a\":56,\"owners\":[82,92,93,96]},{\"tag\":\"mate\",\"ridge\":530,\"a\":58,\"owners\":[82,90,93,96]},{\"tag\":\"mate\",\"ridge\":530,\"a\":59,\"owners\":[82,90,92,96]},{\"tag\":\"mate\",\"ridge\":530,\"a\":60,\"owners\":[82,90,92,93]},{\"tag\":\"mate\",\"ridge\":530,\"a\":96,\"owners\":[13,38,56,58,59,90,92,93]},{\"tag\":\"mate\",\"ridge\":564,\"a\":72,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":596,\"a\":74,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":660,\"a\":75,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":792,\"a\":78,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":792,\"a\":96,\"owners\":[78]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[34,40,43,45,54,69,87],\"full_literals\":[-59,8,12,15,17,22,33,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[36,37,38,61,62,71,79,80,89],\"full_literals\":[-60,9,10,11,29,30,35,43,44,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[48,49,56,57,58,59,60],\"full_literals\":[-61,20,21,24,25,26,27,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[41,42,44,46],\"full_literals\":[-62,13,14,16,18]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-66,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-68,66,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-69,65,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-69,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[64,78],\"full_literals\":[-70,32,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":64,\"full_literals\":[-32,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":78,\"full_literals\":[-42,70]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[82,96],\"full_literals\":[-71,46,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-46,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":96,\"full_literals\":[-56,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":63,\"full_literals\":[-31,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":70,\"full_literals\":[-34,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":73,\"full_literals\":[-37,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":74,\"full_literals\":[-38,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-39,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":81,\"full_literals\":[-45,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":88,\"full_literals\":[-48,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":90,\"full_literals\":[-50,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":91,\"full_literals\":[-51,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":92,\"full_literals\":[-52,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":93,\"full_literals\":[-53,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":97,\"full_literals\":[-57,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":98,\"full_literals\":[-58,74]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-75,70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-70,-71,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-78,79],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":31,\"owners\":[11,22,30,36,55,57,58,62,70,73,74,76,80,88,91,92,94,97]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[12,23,31,37,47,57,59,63,71,73,75,77,81,89,91,93,95,98]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[13,38,49,56,58,59,60,64,72,74,75,78,82,90,92,93,96]}]}"
  "140 65 0 107 105 0\n141 68 0 107 106 0\n142 63 0 140 99 0\n143 64 0 140 100 0\n144 66 0 141 103 0\n145 67 0 141 104 0\n146 59 0 142 97 0\n147 60 0 143 98 0\n148 61 0 144 101 0\n149 62 0 145 102 0\n150 50 52 53 75 0 128 113 112 83 89 90 81 129 110 109 82 88 80 84 85 86 139 0\n151 -50 11 0 147 38 39 40 41 42 43 44 45 94 0\n152 -52 11 0 147 46 47 48 49 50 51 52 53 94 0\n153 75 0 147 128 113 81 151 152 150 54 55 56 57 58 59 60 61 94 0\n154 -9 0 149 2 4 7 10 96 0\n155 -10 0 149 3 5 8 11 96 0\n156 -29 56 0 153 91 23 29 108 111 127 0\n157 -30 56 0 153 91 24 30 108 111 127 0\n158 -35 56 0 153 91 25 31 108 111 127 0\n159 -43 56 0 153 91 27 32 108 111 127 0\n160 -44 56 0 153 91 28 33 108 111 127 0\n161 56 0 155 154 147 153 81 91 156 157 158 159 160 94 35 37 108 111 127 0\n162 -8 0 161 62 0\n163 -20 0 161 63 0\n164 -21 0 161 64 0\n165 -22 0 161 65 0\n166 -28 0 161 66 0\n167 -33 0 161 67 0\n168 -47 0 161 68 0\n169 -54 0 161 69 0\n170 42 0 161 92 0\n171 71 0 161 113 0\n172 -40 0 170 26 0\n173 70 0 170 110 0\n174 76 0 173 171 130 0\n175 -78 0 174 136 135 0\n176 -77 0 175 133 0\n177 -72 0 175 134 0\n178 -74 0 176 131 0\n179 -73 0 176 132 0\n180 -31 0 177 114 0\n181 -34 0 177 115 0\n182 -37 0 177 116 0\n183 -38 0 177 117 0\n184 -39 0 177 118 0\n185 -57 0 178 125 0\n186 -58 0 178 126 0\n187 -45 0 179 119 0\n188 -48 0 179 120 0\n189 -50 0 179 121 0\n190 -51 0 179 122 0\n191 -52 0 179 123 0\n192 -53 0 179 124 0\n193 24 26 27 11 0 166 164 163 148 192 191 189 161 95 87 14 0\n194 26 27 -49 11 0 185 169 191 190 188 172 183 182 181 154 36 34 193 12 13 15 70 72 137 0\n195 27 -49 11 0 194 16 17 18 78 0\n196 -49 11 0 185 169 191 190 188 172 183 182 181 154 34 36 195 19 20 21 22 70 72 137 0\n197 1 26 23 25 0 154 181 182 183 172 188 190 191 169 185 70 72 71 73 137 0\n198 -27 0 19 20 21 22 197 0\n199 26 11 0 198 193 12 13 15 197 0\n200 11 0 186 192 190 187 184 182 180 198 155 196 199 16 17 18 74 76 77 79 75 138 0\n201 -12 0 200 1 0\n202 -15 0 200 6 0\n203 -17 0 200 9 0\n204 0 201 202 146 162 167 168 203 165 93 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record005
