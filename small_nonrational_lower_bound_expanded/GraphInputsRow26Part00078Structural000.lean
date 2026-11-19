module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00078Data
public import GraphInputsRow26Part00078Frames
public import GraphInputsRow26Part00078Leaves
public import GraphInputsRow26Part00078Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩, ⟨82, by decide⟩, ⟨92, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 35218731827200, 101334384640, 103766409871360]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), (certNat% 3), 35218731827200, 101602820096, 104041287778304]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), 4647714815580569600, 130996502528, (certNat% 7)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 10), 131941395333120, (certNat% 11)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), 64424509440, 4647714815580569600, (certNat% 14)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 9), (certNat% 10), 63771674411008, (certNat% 16)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 9), 4647714815580569600, 128849018880, (certNat% 18)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), 61572651155456, (certNat% 21), (certNat% 22)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 3), (certNat% 24), (certNat% 25)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), (certNat% 28), (certNat% 29), 4611686018427387904]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), (certNat% 32), (certNat% 29), (certNat% 33), (certNat% 34)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c16 c3
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c17 c2
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010
def vertexColumn : Fields := ⟨10, (certNat% 35)⟩
def kindColumn : Fields := ⟨3, (certNat% 36)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩, ⟨84, by decide⟩, ⟨90, by decide⟩, ⟨94, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), (certNat% 40), (certNat% 41)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), (certNat% 44), (certNat% 45), 255550554112]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 43), (certNat% 44), (certNat% 47), 255550554112]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 43), (certNat% 44), (certNat% 45), 1046735069642752]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 43), (certNat% 44), (certNat% 47), 1046735069642752]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 51), (certNat% 52), 74785044299776, (certNat% 41)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 54), (certNat% 55), (certNat% 56), 1117103813820416]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), (certNat% 59), (certNat% 52), (certNat% 60)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 62), 255550554112, (certNat% 63), 1047009947549696]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), 273804165120, (certNat% 65), (certNat% 66), 1121501860331520, (certNat% 52)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c13 c5
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c14 c4
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c15 c3
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c16 c2
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c17 c1
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c18 c0
  c19
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2729ab1aa699a8e93a2e996558d64d8b61d98e9392e2b86e9c669c6699666394e4b965555355352d4756364d4b4ad1b663c4e9364d5334e334ccb3c2e8b62e4b8ad2b2ac6b86d1b26c3b61e4751cc749ca745c9715c3783c4f948721990e2382e944711950d2342d90c6384d1324c530ce0b42c8b0ad0721c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9b6db6db6d26924db6db6db693492492492492492492492492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 47), (facetIndex 54), (facetIndex 60), (facetIndex 79), (facetIndex 98)]))
 (.branch 2
 (.leaf ([(facetIndex 28), (facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 65)]))
 (.leaf ([(facetIndex 80), (facetIndex 81), (facetIndex 82), (facetIndex 84)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 33), (facetIndex 66), (facetIndex 85)]))
 (.leaf ([(facetIndex 29), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 39)])))
 (.branch 6
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51)]))
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a0920000000000c8248db6c36b6d16ddb692491b6e1z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 64), (facetIndex 78)]))
 (.branch 2
 (.leaf ([(facetIndex 83), (facetIndex 97)]))
 (.leaf ([(facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 70), (facetIndex 71)]))))
 (.branch 4
 (.leaf ([(facetIndex 86), (facetIndex 87), (facetIndex 88), (facetIndex 89), (facetIndex 90)]))
 (.branch 5
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 75), (facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 91), (facetIndex 92), (facetIndex 93), (facetIndex 94), (facetIndex 95), (facetIndex 96)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6dadb6c02000249244924z32;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [1, 2]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [3]
def grouped2_0007 : List Nat := [3, 4]
def grouped2_0008 : List Nat := [3, 4, 5, 6]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1, 2]
def grouped3_0016 : List Nat := [1]
def grouped3_0017 : List Nat := [1, 2]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [3]
def grouped3_0020 : List Nat := [3, 4, 5]
def grouped3_0021 : List Nat := [4, 5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record004" 91

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record004" "{\"ridges\":[[3,7],[4,7],[6,137],[7,265],[11,19],[12,19],[17,133],[18,261],[32,7],[32,19],[33,7],[33,19],[38,7],[40,19],[41,145],[42,273],[62,133],[63,261],[65,133],[65,261],[86,180],[87,308],[88,212],[89,340],[90,404]],\"owners\":[[17,133,[3,32,34,36,39,67,69,71],[62,65]],[62,133,[3,32,36,39,69,71],[17,34,65,67]],[65,133,[3,32,34,36,67,69],[17,39,62,71]],[18,261,[4,33,35,37,39,68,70,71],[63,65]],[63,261,[4,33,37,39,70,71],[18,35,65,68]],[65,261,[4,33,35,37,68,70],[18,39,63,71]],[6,137,[17,62,65,72,75,76],[41,45,49,50]],[7,265,[18,63,65,73,75,77],[42,46,49,51]],[41,145,[67,69,71],[11,32,52,55,57,58,72,75,76]],[42,273,[68,70,71],[12,33,53,56,57,59,73,75,77]],[86,180,[67],[]],[87,308,[68],[]],[88,212,[69],[]],[89,340,[70],[]],[90,404,[71],[]]],\"edges\":[[6,[3,6,11,17,32,34,36,39,41,45,49,50,52,55,57,58,62,65,67,69,71,72,75,76]],[7,[4,7,12,18,33,35,37,39,42,46,49,51,53,56,57,59,63,65,68,70,71,73,75,77]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-13],[-15,-11],[-15,-12],[-15,-13],[-15,-14],[-16,-11],[-16,-12],[-16,-13],[-16,-14],[-17,-11],[-17,-12],[-17,-13],[-17,-14],[-18,-11],[-18,-12],[-18,-13],[-18,-14],[-19,-12],[-20,-11],[-20,-12],[-20,-13],[-20,-14],[-21,-10],[-21,-11],[-24,-10],[-24,-19],[-25,-21],[-26,-21],[-27,-10],[-28,-13],[-28,-14],[-29,-21],[-30,-21],[-31,-11],[-31,-13],[-31,-14],[-32,-11],[-32,-13],[-32,-14],[-33,-12],[-34,-11],[-34,-13],[-34,-14],[-35,-11],[-35,-13],[-35,-14],[-36,-11],[-36,-13],[-36,-14],[-37,-11],[-37,-13],[-37,-14],[-38,-11],[-38,-13],[-38,-14],[-39,-12],[-43,-9],[-43,-41],[-43,-42],[-44,-43],[-45,-40],[-46,-11],[-46,-12],[-46,-13],[-46,-14],[-46,-45],[-47,-11],[-47,-12],[-47,-13],[-47,-14],[-47,-45],[-48,-11],[-48,-12],[-48,-13],[-48,-14],[-48,-45],[-49,-11],[-49,-12],[-49,-13],[-49,-14],[-49,-45],[-50,-11],[-50,-12],[-50,-13],[-50,-14],[-50,-45],[-51,-21],[-52,-21],[-53,-21],[-54,-21],[-55,-21],[-56,-45],[-57,-12],[-61,-59],[-61,-60],[-62,-61],[-63,-46],[-63,-47],[-63,-48],[-63,-49],[-63,-50],[-63,-58],[-69,-63],[-70,-12],[-1,-14,-19],[-2,-13,-19],[-7,1,13,15,17,20,46,48,50],[-41,1,13,17,20,48,50],[-44,1,13,15,17,46,48],[-8,2,14,16,18,20,47,49,50],[-42,2,14,18,20,49,50],[-44,2,14,16,18,47,49],[-3,7,41,44,51,53,54],[-4,8,42,44,52,53,55],[-5,-14,-21],[-6,-13,-21],[-22,46,48,50],[-23,47,49,50],[-64,46],[-65,47],[-66,48],[-67,49],[-68,50],[-71,27,33,39,57,70],[-72,9,40,41,42,44],[-73,58,59,60,62],[-74,11,12,13,14,45,63],[-75,10,15,16,17,18,19,20],[-76,21,22,23,24,31,32,34,35,36,37,38],[-77,72],[-77,73],[-78,71],[-78,77],[-79,74],[-79,75],[-80,76],[-81,79],[-81,80],[-82,78],[-82,81],[82],[-83,43,56],[-84,61,69],[-85,46,47,48,49,50],[-46,85],[-47,85],[-48,85],[-49,85],[-50,85],[-86,64,65,66,67,68],[-87,84,85],[-88,85],[-89,83,88],[-89,87],[-90,86],[-91,89,90],[91],[1,3,5,7,13,15,17,20,22,25,28,29,31,34,36,37,41,44,46,48,50,51,53,54],[2,4,6,8,14,16,18,20,23,26,28,30,32,35,36,38,42,44,47,49,50,52,53,55]],\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":33,\"b\":32},{\"tag\":\"incompatible\",\"a\":34,\"b\":30},{\"tag\":\"incompatible\",\"a\":34,\"b\":31},{\"tag\":\"incompatible\",\"a\":34,\"b\":32},{\"tag\":\"incompatible\",\"a\":34,\"b\":33},{\"tag\":\"incompatible\",\"a\":35,\"b\":30},{\"tag\":\"incompatible\",\"a\":35,\"b\":31},{\"tag\":\"incompatible\",\"a\":35,\"b\":32},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":36,\"b\":30},{\"tag\":\"incompatible\",\"a\":36,\"b\":31},{\"tag\":\"incompatible\",\"a\":36,\"b\":32},{\"tag\":\"incompatible\",\"a\":36,\"b\":33},{\"tag\":\"incompatible\",\"a\":37,\"b\":30},{\"tag\":\"incompatible\",\"a\":37,\"b\":31},{\"tag\":\"incompatible\",\"a\":37,\"b\":32},{\"tag\":\"incompatible\",\"a\":37,\"b\":33},{\"tag\":\"incompatible\",\"a\":38,\"b\":31},{\"tag\":\"incompatible\",\"a\":39,\"b\":30},{\"tag\":\"incompatible\",\"a\":39,\"b\":31},{\"tag\":\"incompatible\",\"a\":39,\"b\":32},{\"tag\":\"incompatible\",\"a\":39,\"b\":33},{\"tag\":\"incompatible\",\"a\":40,\"b\":29},{\"tag\":\"incompatible\",\"a\":40,\"b\":30},{\"tag\":\"incompatible\",\"a\":43,\"b\":29},{\"tag\":\"incompatible\",\"a\":43,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":40},{\"tag\":\"incompatible\",\"a\":46,\"b\":40},{\"tag\":\"incompatible\",\"a\":47,\"b\":29},{\"tag\":\"incompatible\",\"a\":49,\"b\":32},{\"tag\":\"incompatible\",\"a\":49,\"b\":33},{\"tag\":\"incompatible\",\"a\":50,\"b\":40},{\"tag\":\"incompatible\",\"a\":51,\"b\":40},{\"tag\":\"incompatible\",\"a\":52,\"b\":30},{\"tag\":\"incompatible\",\"a\":52,\"b\":32},{\"tag\":\"incompatible\",\"a\":52,\"b\":33},{\"tag\":\"incompatible\",\"a\":53,\"b\":30},{\"tag\":\"incompatible\",\"a\":53,\"b\":32},{\"tag\":\"incompatible\",\"a\":53,\"b\":33},{\"tag\":\"incompatible\",\"a\":54,\"b\":31},{\"tag\":\"incompatible\",\"a\":55,\"b\":30},{\"tag\":\"incompatible\",\"a\":55,\"b\":32},{\"tag\":\"incompatible\",\"a\":55,\"b\":33},{\"tag\":\"incompatible\",\"a\":56,\"b\":30},{\"tag\":\"incompatible\",\"a\":56,\"b\":32},{\"tag\":\"incompatible\",\"a\":56,\"b\":33},{\"tag\":\"incompatible\",\"a\":57,\"b\":30},{\"tag\":\"incompatible\",\"a\":57,\"b\":32},{\"tag\":\"incompatible\",\"a\":57,\"b\":33},{\"tag\":\"incompatible\",\"a\":58,\"b\":30},{\"tag\":\"incompatible\",\"a\":58,\"b\":32},{\"tag\":\"incompatible\",\"a\":58,\"b\":33},{\"tag\":\"incompatible\",\"a\":59,\"b\":30},{\"tag\":\"incompatible\",\"a\":59,\"b\":32},{\"tag\":\"incompatible\",\"a\":59,\"b\":33},{\"tag\":\"incompatible\",\"a\":60,\"b\":31},{\"tag\":\"incompatible\",\"a\":64,\"b\":28},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":61},{\"tag\":\"incompatible\",\"a\":67,\"b\":30},{\"tag\":\"incompatible\",\"a\":67,\"b\":31},{\"tag\":\"incompatible\",\"a\":67,\"b\":32},{\"tag\":\"incompatible\",\"a\":67,\"b\":33},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":30},{\"tag\":\"incompatible\",\"a\":68,\"b\":31},{\"tag\":\"incompatible\",\"a\":68,\"b\":32},{\"tag\":\"incompatible\",\"a\":68,\"b\":33},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":30},{\"tag\":\"incompatible\",\"a\":69,\"b\":31},{\"tag\":\"incompatible\",\"a\":69,\"b\":32},{\"tag\":\"incompatible\",\"a\":69,\"b\":33},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":30},{\"tag\":\"incompatible\",\"a\":70,\"b\":31},{\"tag\":\"incompatible\",\"a\":70,\"b\":32},{\"tag\":\"incompatible\",\"a\":70,\"b\":33},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":30},{\"tag\":\"incompatible\",\"a\":71,\"b\":31},{\"tag\":\"incompatible\",\"a\":71,\"b\":32},{\"tag\":\"incompatible\",\"a\":71,\"b\":33},{\"tag\":\"incompatible\",\"a\":71,\"b\":66},{\"tag\":\"incompatible\",\"a\":72,\"b\":40},{\"tag\":\"incompatible\",\"a\":73,\"b\":40},{\"tag\":\"incompatible\",\"a\":75,\"b\":40},{\"tag\":\"incompatible\",\"a\":76,\"b\":40},{\"tag\":\"incompatible\",\"a\":77,\"b\":40},{\"tag\":\"incompatible\",\"a\":78,\"b\":66},{\"tag\":\"incompatible\",\"a\":79,\"b\":31},{\"tag\":\"incompatible\",\"a\":83,\"b\":81},{\"tag\":\"incompatible\",\"a\":83,\"b\":82},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"incompatible\",\"a\":85,\"b\":67},{\"tag\":\"incompatible\",\"a\":85,\"b\":68},{\"tag\":\"incompatible\",\"a\":85,\"b\":69},{\"tag\":\"incompatible\",\"a\":85,\"b\":70},{\"tag\":\"incompatible\",\"a\":85,\"b\":71},{\"tag\":\"incompatible\",\"a\":85,\"b\":80},{\"tag\":\"incompatible\",\"a\":97,\"b\":85},{\"tag\":\"incompatible\",\"a\":98,\"b\":31},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[3,33,38]},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[4,32,38]},{\"tag\":\"mate\",\"ridge\":133,\"a\":17,\"owners\":[3,32,34,36,39,67,69,71]},{\"tag\":\"mate\",\"ridge\":133,\"a\":62,\"owners\":[3,32,36,39,69,71]},{\"tag\":\"mate\",\"ridge\":133,\"a\":65,\"owners\":[3,32,34,36,67,69]},{\"tag\":\"mate\",\"ridge\":261,\"a\":18,\"owners\":[4,33,35,37,39,68,70,71]},{\"tag\":\"mate\",\"ridge\":261,\"a\":63,\"owners\":[4,33,37,39,70,71]},{\"tag\":\"mate\",\"ridge\":261,\"a\":65,\"owners\":[4,33,35,37,68,70]},{\"tag\":\"mate\",\"ridge\":137,\"a\":6,\"owners\":[17,62,65,72,75,76]},{\"tag\":\"mate\",\"ridge\":265,\"a\":7,\"owners\":[18,63,65,73,75,77]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[11,33,40]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[12,32,40]},{\"tag\":\"mate\",\"ridge\":145,\"a\":41,\"owners\":[67,69,71]},{\"tag\":\"mate\",\"ridge\":273,\"a\":42,\"owners\":[68,70,71]},{\"tag\":\"mate\",\"ridge\":180,\"a\":86,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":308,\"a\":87,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":212,\"a\":88,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":340,\"a\":89,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":404,\"a\":90,\"owners\":[71]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[47,54,60,79,98],\"full_literals\":[-71,27,33,39,57,70]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[28,61,62,63,65],\"full_literals\":[-72,9,40,41,42,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[80,81,82,84],\"full_literals\":[-73,58,59,60,62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[30,31,32,33,66,85],\"full_literals\":[-74,11,12,13,14,45,63]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[29,34,35,36,37,38,39],\"full_literals\":[-75,10,15,16,17,18,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[40,41,42,43,52,53,55,56,57,58,59],\"full_literals\":[-76,21,22,23,24,31,32,34,35,36,37,38]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-77,72,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,false,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-78,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-78,false,77],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-79,74,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,false,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,false,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-81,79,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-81,false,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-82,78,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-82,false,81],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[64,78],\"full_literals\":[-83,43,56]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[83,97],\"full_literals\":[-84,61,69]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[67,68,69,70,71],\"full_literals\":[-85,46,47,48,49,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-46,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":68,\"full_literals\":[-47,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-48,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":70,\"full_literals\":[-49,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":71,\"full_literals\":[-50,85]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[86,87,88,89,90],\"full_literals\":[-86,64,65,66,67,68]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-87,84,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-88,false,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-89,83,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-89,false,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-90,86,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-91,89,90],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":6,\"owners\":[3,6,11,17,32,34,36,39,41,45,49,50,52,55,57,58,62,65,67,69,71,72,75,76]},{\"tag\":\"edge\",\"edge\":7,\"owners\":[4,7,12,18,33,35,37,39,42,46,49,51,53,56,57,59,63,65,68,70,71,73,75,77]}]}"
  "160 78 0 141 139 0\n161 81 0 141 140 0\n162 71 0 160 132 0\n163 77 0 160 133 0\n164 79 0 161 137 0\n165 80 0 161 138 0\n166 72 0 163 130 0\n167 73 0 163 131 0\n168 74 0 164 134 0\n169 75 0 164 135 0\n170 76 0 165 136 0\n171 -45 -85 0 66 71 76 81 86 144 0\n172 -63 -85 0 97 98 99 100 101 144 0\n173 -11 -85 0 62 67 72 77 82 144 0\n174 -13 -85 0 64 69 74 79 84 144 0\n175 -14 -85 0 65 70 75 80 85 144 0\n176 -85 0 168 171 172 173 174 175 127 63 68 73 78 83 144 0\n177 -46 0 176 145 0\n178 -47 0 176 146 0\n179 -48 0 176 147 0\n180 -49 0 176 148 0\n181 -50 0 176 149 0\n182 -22 0 177 179 181 117 0\n183 -64 0 177 119 0\n184 -23 0 178 180 181 118 0\n185 -65 0 178 120 0\n186 -66 0 179 121 0\n187 -67 0 180 122 0\n188 -68 0 181 123 0\n189 -86 0 187 186 183 185 188 150 0\n190 -88 0 176 152 0\n191 -90 0 189 155 0\n192 89 0 191 157 156 0\n193 83 0 192 190 153 0\n194 87 0 192 154 0\n195 84 0 194 176 151 0\n196 -12 0 169 162 3 7 11 15 18 20 40 56 93 104 128 124 29 0\n197 -63 0 195 167 102 103 143 94 95 96 126 0\n198 -11 0 182 184 170 169 2 6 10 14 19 24 34 37 41 44 47 50 53 129 25 26 128 0\n199 -19 -13 14 0 182 170 181 180 178 184 54 51 48 45 42 38 35 30 21 16 8 26 106 129 112 110 111 28 33 88 89 91 116 114 159 0\n200 14 45 0 170 184 182 169 168 196 198 197 127 4 8 12 16 21 35 38 42 45 48 51 54 199 128 23 25 129 0\n201 -10 -14 0 182 184 170 55 52 49 46 43 39 36 23 25 129 0\n202 -14 0 169 184 170 181 179 177 182 1 5 9 13 17 22 31 36 39 43 46 49 52 55 201 128 26 105 129 109 107 108 27 32 87 89 90 115 113 158 0\n203 45 0 202 200 0\n204 -40 0 203 61 0\n205 -56 0 203 92 0\n206 43 0 205 193 142 0\n207 -9 0 206 57 0\n208 -41 0 206 58 0\n209 -42 0 206 59 0\n210 -44 0 206 60 0\n211 0 209 208 166 207 204 210 125 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9d2726693a2e87a99b16a599695a364d8b61d98e9392e2b86e9c599564d94e4b91e665c569565655554d58d5352d4756364d534cd4b4ad98f13a4d9394e334ccb31cd8b92d2b2ac6b46c9b16c3bc1e8761e4789d2729c6785d1725c570de0f13c6c4388e0ba511c469914654348d1342d84d1324c3342c8b0ae0741c8709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6db69a4936db49b69b6da49249a49249269249a492492493491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 25), (facetIndex 26), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 63)]))
 (.leaf ([(facetIndex 64), (facetIndex 74), (facetIndex 75), (facetIndex 81)])))
 (.branch 3
 (.leaf ([(facetIndex 82), (facetIndex 83), (facetIndex 84), (facetIndex 86)]))
 (.leaf ([(facetIndex 40), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 48)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 27), (facetIndex 29), (facetIndex 30), (facetIndex 31), (facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 37), (facetIndex 38), (facetIndex 39)]))
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 54), (facetIndex 55), (facetIndex 56)])))
 (.branch 7
 (.leaf ([(facetIndex 36), (facetIndex 53), (facetIndex 70)]))
 (.leaf ([(facetIndex 32), (facetIndex 49)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "82488000240180001000005b75b7b0dbb439269279208z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 41), (facetIndex 47), (facetIndex 57)]))
 (.branch 2
 (.leaf ([(facetIndex 85), (facetIndex 87), (facetIndex 95), (facetIndex 96)]))
 (.leaf ([(facetIndex 76), (facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 80)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 97), (facetIndex 98), (facetIndex 99)]))
 (.leaf ([(facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 71), (facetIndex 72), (facetIndex 73), (facetIndex 91)])))
 (.branch 6
 (.leaf ([(facetIndex 88), (facetIndex 89), (facetIndex 90), (facetIndex 92), (facetIndex 93), (facetIndex 94)]))
 (.leaf ([(facetIndex 100), (facetIndex 101)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "366d936d96d20800249202482492z31;"⟩
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
def grouped3_0019 : List Nat := [3]
def grouped3_0020 : List Nat := [3, 4]
def grouped3_0021 : List Nat := [3, 4, 5, 6]
def grouped3_0022 : List Nat := [4]
def grouped3_0023 : List Nat := [5]
def grouped3_0024 : List Nat := [5, 6]
def grouped3_0025 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record005" 79

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record005" "{\"ridges\":[[36,580],[41,90],[42,145],[43,273],[47,586],[49,112],[52,530],[53,592],[64,112],[68,212],[69,340],[70,580],[78,216],[79,344],[81,112],[81,592],[85,586],[88,180],[89,308],[92,404],[93,660],[94,788],[97,184],[98,312],[99,408],[100,610]],\"owners\":[[42,145,[65,68,71,72],[9,29,50,54,55,76,78,80]],[43,273,[66,69,71,73],[10,30,51,54,56,77,79,80]],[52,530,[91,93,94],[11,31,53,55,56,90,100]],[36,580,[101],[17,62,70,74,85,91,95]],[70,580,[85,95],[17,36,62,74,91,101]],[49,112,[101],[19,64,75,81,87,96,100]],[64,112,[96,100],[19,49,75,81,87,101]],[81,112,[87,96],[19,49,64,75,100,101]],[53,592,[101],[20,70,81,91,100]],[81,592,[91],[20,53,70,100,101]],[41,90,[96],[]],[47,586,[85],[]],[85,586,[47],[]],[100,610,[57,95],[]],[88,180,[65],[]],[89,308,[66],[]],[68,212,[],[]],[69,340,[],[]],[92,404,[71],[]],[93,660,[72],[]],[94,788,[73],[]],[97,184,[76],[]],[98,312,[77],[]],[78,216,[],[]],[79,344,[],[]],[99,408,[80],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-3,-1],[-3,-2],[-8,-3],[-12,-1],[-12,-2],[-12,-8],[-12,-9],[-12,-10],[-13,-12],[-14,-12],[-15,-12],[-16,-2],[-16,-3],[-16,-8],[-16,-12],[-23,-7],[-23,-16],[-23,-17],[-23,-18],[-23,-19],[-24,-23],[-25,-23],[-26,-23],[-27,-2],[-28,-2],[-28,-8],[-29,-28],[-30,-28],[-33,-28],[-35,-2],[-35,-3],[-35,-8],[-35,-12],[-36,-2],[-44,-1],[-44,-2],[-44,-3],[-44,-4],[-44,-7],[-44,-8],[-44,-12],[-44,-20],[-44,-27],[-44,-39],[-44,-40],[-45,-2],[-45,-3],[-45,-8],[-45,-12],[-50,-1],[-50,-27],[-50,-34],[-50,-36],[-5,18,21,24,25],[-6,19,22,24,26],[-11,40,42,43],[-3,50],[-23,35,44],[-8,50],[-17,45,49],[-34,36,45],[-12,50],[-34,40],[-4,45],[-7,35],[-35,7],[-49,16,44],[-37,18],[-38,19],[-21],[-22],[-41,24],[-42,25],[-43,26],[-46,29],[-47,30],[-31],[-32],[-48,33],[-51,17,27,28,34],[-52,5,6,9,10,11,13,14,15],[-53,3,12,23],[-54,2,8],[-55,51],[-56,55],[-57,52],[-58,53,54],[-59,53],[-59,54],[-60,57,59],[-60,58],[-61,59],[-62,56,61],[-62,60],[62],[-63,1,4,7,16],[-64,35,36,44,45],[-35,64],[-44,64],[-45,64],[-65,29,30,31,32,33],[-29,65],[-30,65],[-33,65],[-66,46,47,48],[-67,18,19,20,21,22,24,25,26,40],[-18,67],[-19,67],[-24,67],[-25,67],[-26,67],[-40,67],[-68,37,38,39,41,42,43],[-69,49,50],[-50,69],[-70,64,65],[-65,70],[-64,70],[-71,65],[-72,63,70],[-70,72],[-73,63,71],[-74,66],[-74,67],[-75,68],[-76,74,75],[-77,74],[-78,72,77],[-78,73,76],[-72,-77,79],[78],[-79]],\"atoms\":[{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":36,\"b\":28},{\"tag\":\"incompatible\",\"a\":36,\"b\":32},{\"tag\":\"incompatible\",\"a\":49,\"b\":36},{\"tag\":\"incompatible\",\"a\":53,\"b\":28},{\"tag\":\"incompatible\",\"a\":53,\"b\":32},{\"tag\":\"incompatible\",\"a\":53,\"b\":49},{\"tag\":\"incompatible\",\"a\":53,\"b\":50},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":55,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":32},{\"tag\":\"incompatible\",\"a\":57,\"b\":36},{\"tag\":\"incompatible\",\"a\":57,\"b\":49},{\"tag\":\"incompatible\",\"a\":57,\"b\":53},{\"tag\":\"incompatible\",\"a\":70,\"b\":47},{\"tag\":\"incompatible\",\"a\":70,\"b\":57},{\"tag\":\"incompatible\",\"a\":70,\"b\":64},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":32},{\"tag\":\"incompatible\",\"a\":75,\"b\":32},{\"tag\":\"incompatible\",\"a\":75,\"b\":49},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":80,\"b\":75},{\"tag\":\"incompatible\",\"a\":85,\"b\":32},{\"tag\":\"incompatible\",\"a\":85,\"b\":36},{\"tag\":\"incompatible\",\"a\":85,\"b\":49},{\"tag\":\"incompatible\",\"a\":85,\"b\":53},{\"tag\":\"incompatible\",\"a\":87,\"b\":32},{\"tag\":\"incompatible\",\"a\":95,\"b\":28},{\"tag\":\"incompatible\",\"a\":95,\"b\":32},{\"tag\":\"incompatible\",\"a\":95,\"b\":36},{\"tag\":\"incompatible\",\"a\":95,\"b\":41},{\"tag\":\"incompatible\",\"a\":95,\"b\":47},{\"tag\":\"incompatible\",\"a\":95,\"b\":49},{\"tag\":\"incompatible\",\"a\":95,\"b\":53},{\"tag\":\"incompatible\",\"a\":95,\"b\":67},{\"tag\":\"incompatible\",\"a\":95,\"b\":74},{\"tag\":\"incompatible\",\"a\":95,\"b\":90},{\"tag\":\"incompatible\",\"a\":95,\"b\":91},{\"tag\":\"incompatible\",\"a\":96,\"b\":32},{\"tag\":\"incompatible\",\"a\":96,\"b\":36},{\"tag\":\"incompatible\",\"a\":96,\"b\":49},{\"tag\":\"incompatible\",\"a\":96,\"b\":53},{\"tag\":\"incompatible\",\"a\":101,\"b\":28},{\"tag\":\"incompatible\",\"a\":101,\"b\":74},{\"tag\":\"incompatible\",\"a\":101,\"b\":81},{\"tag\":\"incompatible\",\"a\":101,\"b\":87},{\"tag\":\"mate\",\"ridge\":145,\"a\":42,\"owners\":[65,68,71,72]},{\"tag\":\"mate\",\"ridge\":273,\"a\":43,\"owners\":[66,69,71,73]},{\"tag\":\"mate\",\"ridge\":530,\"a\":52,\"owners\":[91,93,94]},{\"tag\":\"mate\",\"ridge\":580,\"a\":36,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":580,\"a\":70,\"owners\":[85,95]},{\"tag\":\"mate\",\"ridge\":112,\"a\":49,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":112,\"a\":64,\"owners\":[96,100]},{\"tag\":\"mate\",\"ridge\":112,\"a\":81,\"owners\":[87,96]},{\"tag\":\"mate\",\"ridge\":592,\"a\":53,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":592,\"a\":81,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":90,\"a\":41,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":586,\"a\":47,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":586,\"a\":85,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":610,\"a\":100,\"owners\":[57,95]},{\"tag\":\"mate\",\"ridge\":180,\"a\":88,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":308,\"a\":89,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":212,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":340,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":404,\"a\":92,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":660,\"a\":93,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":788,\"a\":94,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":184,\"a\":97,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":312,\"a\":98,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":216,\"a\":78,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":344,\"a\":79,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":408,\"a\":99,\"owners\":[80]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[64,74,75,81],\"full_literals\":[-51,17,27,28,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[42,43,50,51,52,54,55,56],\"full_literals\":[-52,5,6,9,10,11,13,14,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[36,53,70],\"full_literals\":[-53,3,12,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[32,49],\"full_literals\":[-54,2,8]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-56,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,53,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,57,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-62,56,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-62,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[28,41,47,57],\"full_literals\":[-63,1,4,7,16]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[85,87,95,96],\"full_literals\":[-64,35,36,44,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-35,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":95,\"full_literals\":[-44,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":96,\"full_literals\":[-45,64]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[76,77,78,79,80],\"full_literals\":[-65,29,30,31,32,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":76,\"full_literals\":[-29,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":77,\"full_literals\":[-30,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":80,\"full_literals\":[-33,65]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[97,98,99],\"full_literals\":[-66,46,47,48]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[65,66,67,68,69,71,72,73,91],\"full_literals\":[-67,18,19,20,21,22,24,25,26,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":65,\"full_literals\":[-18,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":66,\"full_literals\":[-19,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":71,\"full_literals\":[-24,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":72,\"full_literals\":[-25,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":73,\"full_literals\":[-26,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":91,\"full_literals\":[-40,67]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[88,89,90,92,93,94],\"full_literals\":[-68,37,38,39,41,42,43]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[100,101],\"full_literals\":[-69,49,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":101,\"full_literals\":[-50,69]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-70,64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-71,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,63,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,63,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-74,66,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-75,68,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-76,74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-77,74,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-78,72,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-78,73,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-72,-77,79],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true}]}"
  "133 60 0 95 94 0\n134 58 0 133 91 0\n135 -65 29 30 33 0 77 78 101 0\n136 -67 18 19 20 24 25 26 40 0 70 71 106 0\n137 -77 0 132 127 130 123 121 117 102 103 104 75 76 79 105 0\n138 72 0 137 131 128 0\n139 -3 70 0 138 118 100 64 98 65 120 1 13 96 0\n140 -12 70 0 138 118 100 64 98 65 120 4 15 96 0\n141 16 70 -69 0 138 118 100 64 98 65 99 120 67 96 114 50 0\n142 70 -69 0 134 118 98 99 58 139 140 82 87 141 12 14 83 0\n143 53 34 27 17 0 134 95 87 88 92 93 85 84 80 25 26 83 0\n144 -2 -53 23 0 2 5 82 0\n145 -8 -53 23 0 3 6 82 0\n146 44 35 45 16 -69 0 95 142 58 67 114 60 51 52 53 97 116 143 144 145 83 89 92 93 85 84 80 27 28 29 135 0\n147 -44 -53 -67 0 37 41 42 45 82 19 20 21 22 23 136 0\n148 -23 44 0 16 58 66 0\n149 -35 23 -53 0 31 33 82 0\n150 -3 35 44 0 13 47 57 146 115 0\n151 -53 -67 0 147 148 149 150 82 15 49 62 146 115 0\n152 16 45 35 44 53 0 134 87 67 146 60 115 59 83 24 34 143 61 0\n153 -16 -54 0 12 14 83 0\n154 -45 -54 0 46 48 83 0\n155 -35 -54 0 30 32 83 0\n156 53 0 134 87 153 154 155 152 36 40 83 0\n157 -67 0 156 151 0\n158 -18 0 157 107 0\n159 -19 0 157 108 0\n160 -24 0 157 109 0\n161 -25 0 157 110 0\n162 -26 0 157 111 0\n163 -40 0 157 112 0\n164 -74 0 157 124 0\n165 -37 0 158 68 0\n166 -38 0 159 69 0\n167 -41 0 160 72 0\n168 -5 0 160 70 158 161 54 0\n169 -6 0 160 71 159 162 55 0\n170 -42 0 161 73 0\n171 -43 0 162 74 0\n172 -34 0 163 63 0\n173 -11 0 170 163 171 56 0\n174 -44 0 156 171 170 167 165 166 164 95 131 172 35 36 37 38 39 40 41 43 44 83 82 113 89 17 18 125 92 96 126 93 129 85 122 84 119 80 27 28 29 135 0\n175 -23 0 174 148 0\n176 -2 0 175 156 144 0\n177 -8 0 175 156 145 0\n178 -35 0 175 156 149 0\n179 -54 0 177 176 83 0\n180 -3 0 178 174 150 0\n181 -59 0 179 89 0\n182 12 0 180 175 156 82 0\n183 57 0 181 133 90 0\n184 -9 0 182 7 0\n185 -10 0 182 8 0\n186 -13 0 182 9 0\n187 -14 0 182 10 0\n188 -15 0 182 11 0\n189 52 0 183 86 0\n190 0 185 186 184 168 169 173 189 187 188 81 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2746713c2f07c6693a2ea66c5a9665a364d8b66394e3392e2b86e4789e0fa71666594e4b91e665c5695656558d5352d4756354d3352d2b46d4749d1743d98f13a4d938cd332cd8b92d4b32d2b2ae1b46c9b0ef07a1d8751cc789d2729e1745c970dd0f23c4f0bc1f1aa4619869464990e64519615454950d64318d0b22c4b0ae0741c8711c27"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db69b6db6db69b6d34924924926db6926936db692493492492492492493249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 26), (facetIndex 57), (facetIndex 86), (facetIndex 98)]))
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50)])))
 (.branch 3
 (.leaf ([(facetIndex 41), (facetIndex 58), (facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 81)]))
 (.leaf ([(facetIndex 60), (facetIndex 61), (facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 73), (facetIndex 74), (facetIndex 75)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 42), (facetIndex 43)]))
 (.leaf ([(facetIndex 25), (facetIndex 27), (facetIndex 28), (facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 39), (facetIndex 40)])))
 (.branch 7
 (.leaf ([(facetIndex 68), (facetIndex 72), (facetIndex 76)]))
 (.leaf ([(facetIndex 62)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "104966de6de0001db080000049248915b6db6c925a28z12;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 59), (facetIndex 80), (facetIndex 82)]))
 (.leaf ([(facetIndex 24), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 102)])))
 (.branch 3
 (.leaf ([(facetIndex 83), (facetIndex 87), (facetIndex 88), (facetIndex 89), (facetIndex 90), (facetIndex 91)]))
 (.leaf ([(facetIndex 44), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 84)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 85), (facetIndex 92), (facetIndex 93), (facetIndex 94), (facetIndex 95), (facetIndex 96), (facetIndex 97)]))
 (.leaf ([(facetIndex 106)])))
 (.branch 7
 (.leaf ([(facetIndex 103), (facetIndex 104), (facetIndex 105)]))
 (.leaf ([(facetIndex 99), (facetIndex 100), (facetIndex 101)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "176c7fe249244924234000000000002492000036db600003000000000000001z12;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7]
def grouped2_0008 : List Nat := [7]
def grouped3_0009 : List Nat := [0]
def grouped3_0010 : List Nat := [0, 1]
def grouped3_0011 : List Nat := [0, 1, 2, 3]
def grouped3_0013 : List Nat := [1]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [2, 3]
def grouped3_0016 : List Nat := [3]
def grouped3_0017 : List Nat := [4]
def grouped3_0018 : List Nat := [4, 5]
def grouped3_0019 : List Nat := [4, 5, 6, 7]
def grouped3_0020 : List Nat := [5]
def grouped3_0021 : List Nat := [6]
def grouped3_0022 : List Nat := [6, 7]
def grouped3_0023 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record008" 80

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record008" "{\"ridges\":[[14,532],[30,134],[30,148],[31,262],[31,276],[32,532],[42,138],[42,152],[43,266],[43,280],[44,538],[71,529],[72,529],[74,532],[75,532],[80,600],[82,624],[94,562],[96,658],[97,786],[103,172],[104,300],[105,396],[106,624]],\"owners\":[[30,134,[87,89,91],[2,27,33,36,38,39,84,92,95,96]],[31,262,[88,90,91],[3,28,34,37,38,40,85,93,95,97]],[42,138,[87,89,91],[7,27,45,47,50,84,99,101]],[43,266,[88,90,91],[8,28,46,48,50,85,100,101]],[30,148,[103,105],[12,60,69,73,74,84,92,95,96]],[31,276,[104,105],[13,61,70,73,75,85,93,95,97]],[71,529,[44,55,56,80],[14,32,53,72,74,75,82]],[72,529,[44,53,55,56],[14,32,71,74,75,80,82]],[14,532,[94,96,97,106],[32,71,72,74,75]],[32,532,[106],[14,71,72,74,75,94,96,97]],[74,532,[94,97,106],[14,32,71,72,75,96]],[75,532,[94,96,106],[14,32,71,72,74,97]],[42,152,[103,105],[18,60,78,81,84,99,101]],[43,280,[104,105],[19,61,79,81,85,100,101]],[44,538,[],[]],[94,562,[53],[]],[96,658,[55],[]],[97,786,[56],[]],[103,172,[63,87],[]],[104,300,[64,88],[]],[105,396,[67,91],[]],[80,600,[],[]],[82,624,[106],[]],[106,624,[82],[]]],\"edges\":[[34,[14,32,44,53,55,56,71,72,74,75,80,82,94,96,97,106]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-7],[-10,-8],[-11,-7],[-11,-8],[-12,-7],[-12,-8],[-13,-7],[-13,-8],[-14,-7],[-14,-8],[-15,-7],[-15,-8],[-16,-7],[-16,-8],[-17,-7],[-17,-8],[-21,-6],[-21,-18],[-21,-19],[-22,-6],[-22,-18],[-22,-19],[-23,-6],[-23,-18],[-23,-19],[-24,-6],[-24,-18],[-24,-19],[-25,-6],[-25,-18],[-25,-19],[-26,-6],[-26,-18],[-26,-19],[-28,-2],[-28,-27],[-29,-28],[-30,-28],[-31,-28],[-32,-28],[-33,-28],[-41,-28],[-42,-28],[-43,-6],[-44,-3],[-44,-4],[-44,-5],[-44,-10],[-44,-21],[-44,-28],[-44,-43],[-45,-3],[-45,-4],[-45,-5],[-45,-11],[-45,-22],[-45,-28],[-45,-43],[-45,-44],[-46,-28],[-46,-45],[-47,-28],[-47,-44],[-47,-46],[-48,-3],[-48,-4],[-48,-5],[-48,-15],[-48,-24],[-48,-28],[-48,-43],[-52,-28],[-53,-46],[-54,-47],[-55,-46],[-55,-47],[-56,-34],[-56,-36],[-56,-39],[-7,44,46,48],[-8,45,47,48],[-18,44,46,48],[-19,45,47,48],[-7,53,55],[-8,54,55],[-35,20,25,26,40],[-36,20,23,25,26],[-1,49,50,51,56],[-9,56],[-37,49,51,56],[-38,49,50,56],[-18,53,55],[-19,54,55],[-20],[-49,23],[-50,25],[-51,26],[-53,29,44],[-54,30,45],[-55,33,48],[-40],[-41,56],[-56,41],[-57,6,7,8,9,18,19],[-58,3,4,5,10,11,12,13,14,15,16,17],[-59,34,36,39],[-60,28],[-61,57],[-61,58],[-62,59,60],[-63,60],[-64,61,63],[-64,62],[-65,64],[65],[-66,27,40,41],[-41,66],[-67,2,29,30,31,32,33,52],[-29,67],[-30,67],[-33,67],[-68,42,44,45,46,47,48],[-44,68],[-45,68],[-48,68],[-69,20,21,22,23,24,25,26,43],[-23,69],[-25,69],[-26,69],[-70,56],[-71,53,54,55],[-72,66,67],[-67,72],[-66,72],[-69,73],[-74,68],[-68,-69,74],[-75,72,74],[-74,75],[-72,-73,75],[-76,70],[-77,71],[-78,76,77],[-79,75,78],[-75,-78,80],[79],[-80],[1,9,20,23,25,26,35,36,37,38,40,41,49,50,51,56]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":33,\"b\":30},{\"tag\":\"incompatible\",\"a\":33,\"b\":31},{\"tag\":\"incompatible\",\"a\":34,\"b\":30},{\"tag\":\"incompatible\",\"a\":34,\"b\":31},{\"tag\":\"incompatible\",\"a\":35,\"b\":30},{\"tag\":\"incompatible\",\"a\":35,\"b\":31},{\"tag\":\"incompatible\",\"a\":36,\"b\":30},{\"tag\":\"incompatible\",\"a\":36,\"b\":31},{\"tag\":\"incompatible\",\"a\":37,\"b\":30},{\"tag\":\"incompatible\",\"a\":37,\"b\":31},{\"tag\":\"incompatible\",\"a\":38,\"b\":30},{\"tag\":\"incompatible\",\"a\":38,\"b\":31},{\"tag\":\"incompatible\",\"a\":39,\"b\":30},{\"tag\":\"incompatible\",\"a\":39,\"b\":31},{\"tag\":\"incompatible\",\"a\":40,\"b\":30},{\"tag\":\"incompatible\",\"a\":40,\"b\":31},{\"tag\":\"incompatible\",\"a\":51,\"b\":29},{\"tag\":\"incompatible\",\"a\":51,\"b\":42},{\"tag\":\"incompatible\",\"a\":51,\"b\":43},{\"tag\":\"incompatible\",\"a\":52,\"b\":29},{\"tag\":\"incompatible\",\"a\":52,\"b\":42},{\"tag\":\"incompatible\",\"a\":52,\"b\":43},{\"tag\":\"incompatible\",\"a\":53,\"b\":29},{\"tag\":\"incompatible\",\"a\":53,\"b\":42},{\"tag\":\"incompatible\",\"a\":53,\"b\":43},{\"tag\":\"incompatible\",\"a\":54,\"b\":29},{\"tag\":\"incompatible\",\"a\":54,\"b\":42},{\"tag\":\"incompatible\",\"a\":54,\"b\":43},{\"tag\":\"incompatible\",\"a\":55,\"b\":29},{\"tag\":\"incompatible\",\"a\":55,\"b\":42},{\"tag\":\"incompatible\",\"a\":55,\"b\":43},{\"tag\":\"incompatible\",\"a\":56,\"b\":29},{\"tag\":\"incompatible\",\"a\":56,\"b\":42},{\"tag\":\"incompatible\",\"a\":56,\"b\":43},{\"tag\":\"incompatible\",\"a\":62,\"b\":24},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":62},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":67,\"b\":62},{\"tag\":\"incompatible\",\"a\":82,\"b\":62},{\"tag\":\"incompatible\",\"a\":83,\"b\":62},{\"tag\":\"incompatible\",\"a\":84,\"b\":29},{\"tag\":\"incompatible\",\"a\":87,\"b\":25},{\"tag\":\"incompatible\",\"a\":87,\"b\":27},{\"tag\":\"incompatible\",\"a\":87,\"b\":28},{\"tag\":\"incompatible\",\"a\":87,\"b\":33},{\"tag\":\"incompatible\",\"a\":87,\"b\":51},{\"tag\":\"incompatible\",\"a\":87,\"b\":62},{\"tag\":\"incompatible\",\"a\":87,\"b\":84},{\"tag\":\"incompatible\",\"a\":88,\"b\":25},{\"tag\":\"incompatible\",\"a\":88,\"b\":27},{\"tag\":\"incompatible\",\"a\":88,\"b\":28},{\"tag\":\"incompatible\",\"a\":88,\"b\":34},{\"tag\":\"incompatible\",\"a\":88,\"b\":52},{\"tag\":\"incompatible\",\"a\":88,\"b\":62},{\"tag\":\"incompatible\",\"a\":88,\"b\":84},{\"tag\":\"incompatible\",\"a\":88,\"b\":87},{\"tag\":\"incompatible\",\"a\":89,\"b\":62},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":90,\"b\":62},{\"tag\":\"incompatible\",\"a\":90,\"b\":87},{\"tag\":\"incompatible\",\"a\":90,\"b\":89},{\"tag\":\"incompatible\",\"a\":91,\"b\":25},{\"tag\":\"incompatible\",\"a\":91,\"b\":27},{\"tag\":\"incompatible\",\"a\":91,\"b\":28},{\"tag\":\"incompatible\",\"a\":91,\"b\":38},{\"tag\":\"incompatible\",\"a\":91,\"b\":54},{\"tag\":\"incompatible\",\"a\":91,\"b\":62},{\"tag\":\"incompatible\",\"a\":91,\"b\":84},{\"tag\":\"incompatible\",\"a\":102,\"b\":62},{\"tag\":\"incompatible\",\"a\":103,\"b\":89},{\"tag\":\"incompatible\",\"a\":104,\"b\":90},{\"tag\":\"incompatible\",\"a\":105,\"b\":89},{\"tag\":\"incompatible\",\"a\":105,\"b\":90},{\"tag\":\"incompatible\",\"a\":106,\"b\":68},{\"tag\":\"incompatible\",\"a\":106,\"b\":72},{\"tag\":\"incompatible\",\"a\":106,\"b\":76},{\"tag\":\"mate\",\"ridge\":134,\"a\":30,\"owners\":[87,89,91]},{\"tag\":\"mate\",\"ridge\":262,\"a\":31,\"owners\":[88,90,91]},{\"tag\":\"mate\",\"ridge\":138,\"a\":42,\"owners\":[87,89,91]},{\"tag\":\"mate\",\"ridge\":266,\"a\":43,\"owners\":[88,90,91]},{\"tag\":\"mate\",\"ridge\":148,\"a\":30,\"owners\":[103,105]},{\"tag\":\"mate\",\"ridge\":276,\"a\":31,\"owners\":[104,105]},{\"tag\":\"mate\",\"ridge\":529,\"a\":71,\"owners\":[44,55,56,80]},{\"tag\":\"mate\",\"ridge\":529,\"a\":72,\"owners\":[44,53,55,56]},{\"tag\":\"mate\",\"ridge\":532,\"a\":14,\"owners\":[94,96,97,106]},{\"tag\":\"mate\",\"ridge\":532,\"a\":32,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":532,\"a\":74,\"owners\":[94,97,106]},{\"tag\":\"mate\",\"ridge\":532,\"a\":75,\"owners\":[94,96,106]},{\"tag\":\"mate\",\"ridge\":152,\"a\":42,\"owners\":[103,105]},{\"tag\":\"mate\",\"ridge\":280,\"a\":43,\"owners\":[104,105]},{\"tag\":\"mate\",\"ridge\":538,\"a\":44,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":562,\"a\":94,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":658,\"a\":96,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":786,\"a\":97,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":172,\"a\":103,\"owners\":[63,87]},{\"tag\":\"mate\",\"ridge\":300,\"a\":104,\"owners\":[64,88]},{\"tag\":\"mate\",\"ridge\":396,\"a\":105,\"owners\":[67,91]},{\"tag\":\"mate\",\"ridge\":600,\"a\":80,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":624,\"a\":82,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":624,\"a\":106,\"owners\":[82]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[29,30,31,32,42,43],\"full_literals\":[-57,6,7,8,9,18,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[25,27,28,33,34,35,36,37,38,39,40],\"full_literals\":[-58,3,4,5,10,11,12,13,14,15,16,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[68,72,76],\"full_literals\":[-59,34,36,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[62],\"full_literals\":[-60,28]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,59,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,61,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[59,80,82],\"full_literals\":[-66,27,40,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":82,\"full_literals\":[-41,66]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[24,63,64,65,66,67,102],\"full_literals\":[-67,2,29,30,31,32,33,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":63,\"full_literals\":[-29,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":64,\"full_literals\":[-30,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-33,67]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[83,87,88,89,90,91],\"full_literals\":[-68,42,44,45,46,47,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":87,\"full_literals\":[-44,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":88,\"full_literals\":[-45,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":91,\"full_literals\":[-48,68]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[44,51,52,53,54,55,56,84],\"full_literals\":[-69,20,21,22,23,24,25,26,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":53,\"full_literals\":[-23,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":55,\"full_literals\":[-25,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":56,\"full_literals\":[-26,69]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[106],\"full_literals\":[-70,56]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[103,104,105],\"full_literals\":[-71,53,54,55]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,66,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-74,68,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-69,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-75,72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-72,-73,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-76,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-77,71,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-78,76,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-79,75,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-75,-78,80],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[14,32,44,53,55,56,71,72,74,75,80,82,94,96,97,106]}]}"
  "149 64 0 115 114 0\n150 62 0 149 113 0\n151 -66 27 41 0 101 116 0\n152 -69 21 22 23 24 25 26 43 0 94 126 0\n153 1 9 23 25 26 35 36 37 38 41 49 50 51 56 0 94 101 148 0\n154 -56 36 0 150 77 79 103 106 42 110 107 0\n155 69 0 101 94 127 128 129 95 86 96 87 97 154 89 102 88 90 91 153 0\n156 73 0 155 135 0\n157 -78 0 147 155 156 145 139 137 140 123 124 125 133 134 119 120 121 117 98 99 100 103 131 130 142 141 143 0\n158 75 0 157 146 144 0\n159 -28 41 0 158 35 36 37 38 39 40 41 43 50 57 60 62 70 72 151 118 122 132 136 138 0\n160 -6 0 155 17 20 23 26 29 32 44 152 0\n161 44 19 8 46 48 56 0 149 160 102 159 107 111 112 108 89 80 82 104 0\n162 -7 -44 -58 0 48 47 46 45 3 5 7 9 11 13 15 105 0\n163 45 46 47 48 56 0 149 160 155 102 159 107 111 112 109 108 89 81 83 161 49 51 162 104 21 24 27 30 33 152 0\n164 -8 -45 -58 0 55 54 53 52 2 6 8 10 12 14 16 105 0\n165 46 47 48 56 0 149 155 102 159 107 111 112 109 163 56 58 59 164 161 19 25 28 31 34 152 0\n166 47 48 56 0 149 160 102 159 107 111 112 108 89 165 61 73 75 81 83 84 92 104 0\n167 48 56 0 166 63 64 74 76 85 93 161 0\n168 -7 56 0 149 167 68 67 66 65 102 159 107 111 112 109 1 3 5 7 9 13 15 105 0\n169 -18 -48 0 155 71 69 18 21 24 30 33 152 0\n170 -8 56 0 149 167 68 67 66 65 102 159 107 111 112 109 2 4 6 8 10 14 16 105 0\n171 56 0 149 160 155 89 102 159 107 111 112 108 167 69 71 168 169 170 104 19 22 25 31 34 152 0\n172 -36 0 171 78 0\n173 0 171 172 154 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2746713c2f2726693a2ea66c5a9665a568d9362d87663a4e538ce4b8ae1b91e2783e9c5994e4b999715a5595956354d4b51d58d9354d3352d2b51d2743d98f13a4d9394e334ccb31cd8b92d4b32d2b2ad1b26c3bc1e8761e4751cc789d2729c6785d1725c570de0f43c8f13c2f07c6c1a8699146585515254354348d1342d90c6384d1324c3342c8b12c2b"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6db6db6db6db4db6db4924924924924924924924924926da6db6924d3492649249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 24), (facetIndex 25), (facetIndex 26), (facetIndex 27), (facetIndex 29), (facetIndex 31), (facetIndex 32), (facetIndex 33), (facetIndex 34), (facetIndex 40), (facetIndex 87)]))
 (.branch 2
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 61)]))
 (.leaf ([(facetIndex 69), (facetIndex 71), (facetIndex 75), (facetIndex 79)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60)]))
 (.leaf ([(facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 70)])))
 (.branch 6
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 76), (facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 52)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "56d56d51492490b6db6de24edb6z21;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [1, 2]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [3]
def grouped2_0007 : List Nat := [3, 4]
def grouped2_0008 : List Nat := [3, 4, 5, 6]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record009" 64

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record009" "{\"ridges\":[[17,529],[26,131],[27,259],[28,515],[29,35],[31,131],[33,530],[45,138],[46,266],[48,35],[56,530],[57,578],[59,515],[60,515],[61,35],[61,515],[61,578],[75,529],[77,529],[78,529],[87,74],[92,526],[98,530],[100,530],[101,530]],\"owners\":[[87,74,[1,49,50,51],[21,25,90,91,92]],[26,131,[5,54,58,59],[2,31,35,38,41,42,47,49,52]],[31,131,[2,47,49,52],[5,26,35,38,41,42,54,58,59]],[45,138,[88,90,93],[2,26,47,49,52,85,103,105]],[27,259,[6,55,58,60],[3,32,36,39,41,43,48,50,52]],[46,266,[89,91,93],[3,27,48,50,52,86,104,105]],[17,529,[7,56,57,59,60,83],[74,75,77,78]],[75,529,[7,56,59,60],[17,57,74,77,78,83]],[77,529,[7,56,57,60,83],[17,59,74,75,78]],[78,529,[7,56,57,59,83],[17,60,74,75,77]],[33,530,[106],[7,56,57,59,60,97,98,100,101]],[56,530,[98,100,101],[7,33,57,59,60,97,106]],[98,530,[7,56,59,60],[33,57,97,100,101,106]],[100,530,[7,56,57,60,106],[33,59,97,98,101]],[101,530,[7,56,57,59,106],[33,60,97,98,100]],[57,578,[92,102],[9,40,51,61,98,106]],[61,578,[92,98],[9,40,51,57,102,106]],[92,526,[28],[]]],\"edges\":[[34,[7,17,33,56,57,59,60,74,75,77,78,83,97,98,100,101,106,110]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-22,-1],[-22,-2],[-22,-7],[-22,-8],[-22,-9],[-22,-10],[-22,-11],[-22,-21],[-23,-18],[-23,-19],[-23,-20],[-23,-21],[-23,-22],[-24,-18],[-24,-19],[-24,-20],[-24,-21],[-24,-22],[-25,-21],[-25,-22],[-26,-22],[-26,-23],[-26,-24],[-26,-25],[-27,-18],[-27,-25],[-28,-5],[-28,-18],[-28,-19],[-28,-20],[-29,-5],[-29,-18],[-29,-19],[-29,-20],[-30,-18],[-30,-19],[-30,-20],[-31,-25],[-32,-5],[-32,-18],[-32,-19],[-32,-20],[-33,-4],[-33,-12],[-33,-13],[-33,-14],[-33,-18],[-33,-19],[-33,-20],[-33,-29],[-33,-32],[-34,-3],[-34,-12],[-34,-13],[-34,-14],[-34,-18],[-34,-19],[-34,-20],[-34,-28],[-34,-32],[-34,-33],[-35,-8],[-35,-16],[-35,-17],[-35,-18],[-35,-27],[-35,-30],[-35,-31],[-36,-35],[-40,-35],[-42,-41],[-43,-41],[-44,-41],[-45,-41],[-46,-41],[-47,-41],[-48,-35],[-49,-7],[-49,-9],[-49,-10],[-49,-14],[-49,-41],[-50,-41],[-51,-41],[-52,-41],[-53,-35],[-54,-35],[-12,-22,-35],[-41,1,23,24,25],[-9,3,28,32,33],[-13,2,21,23,26],[-19,42,44,47],[-10,4,29,32,34],[-20,43,45,47],[-11,-33,-35],[-11,-34,-35],[-6,5,30,31,33,34,40],[-37,5,30,33,34],[-38,5,30,31,34,40],[-39,5,30,31,33,40],[-15,53],[-30,49,50,51],[-49,5,30,33,34],[-50,5,30,31,34,53],[-51,5,30,31,33,53],[-31,46,52],[-35,46,49],[-46,11],[-55,7,8,9,10,12,13,14,15,16,17,41],[-56,23,24,25,35],[-57,27,28,29,30,31,32,33,34],[-58,18,19,20,21,22,26],[-59,56],[-60,55],[-60,59],[-61,57],[-62,58],[-63,61],[-63,62],[-64,60],[-64,63],[64],[5,6,15,30,31,33,34,36,37,38,39,40,48,49,50,51,53,54]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":48,\"b\":1},{\"tag\":\"incompatible\",\"a\":48,\"b\":2},{\"tag\":\"incompatible\",\"a\":48,\"b\":24},{\"tag\":\"incompatible\",\"a\":48,\"b\":25},{\"tag\":\"incompatible\",\"a\":48,\"b\":26},{\"tag\":\"incompatible\",\"a\":48,\"b\":27},{\"tag\":\"incompatible\",\"a\":48,\"b\":28},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":50,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":47},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":44},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":7},{\"tag\":\"incompatible\",\"a\":54,\"b\":44},{\"tag\":\"incompatible\",\"a\":54,\"b\":45},{\"tag\":\"incompatible\",\"a\":54,\"b\":46},{\"tag\":\"incompatible\",\"a\":55,\"b\":7},{\"tag\":\"incompatible\",\"a\":55,\"b\":44},{\"tag\":\"incompatible\",\"a\":55,\"b\":45},{\"tag\":\"incompatible\",\"a\":55,\"b\":46},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":56,\"b\":45},{\"tag\":\"incompatible\",\"a\":56,\"b\":46},{\"tag\":\"incompatible\",\"a\":57,\"b\":51},{\"tag\":\"incompatible\",\"a\":58,\"b\":7},{\"tag\":\"incompatible\",\"a\":58,\"b\":44},{\"tag\":\"incompatible\",\"a\":58,\"b\":45},{\"tag\":\"incompatible\",\"a\":58,\"b\":46},{\"tag\":\"incompatible\",\"a\":59,\"b\":6},{\"tag\":\"incompatible\",\"a\":59,\"b\":29},{\"tag\":\"incompatible\",\"a\":59,\"b\":31},{\"tag\":\"incompatible\",\"a\":59,\"b\":32},{\"tag\":\"incompatible\",\"a\":59,\"b\":44},{\"tag\":\"incompatible\",\"a\":59,\"b\":45},{\"tag\":\"incompatible\",\"a\":59,\"b\":46},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":5},{\"tag\":\"incompatible\",\"a\":60,\"b\":29},{\"tag\":\"incompatible\",\"a\":60,\"b\":31},{\"tag\":\"incompatible\",\"a\":60,\"b\":32},{\"tag\":\"incompatible\",\"a\":60,\"b\":44},{\"tag\":\"incompatible\",\"a\":60,\"b\":45},{\"tag\":\"incompatible\",\"a\":60,\"b\":46},{\"tag\":\"incompatible\",\"a\":60,\"b\":54},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":25},{\"tag\":\"incompatible\",\"a\":61,\"b\":34},{\"tag\":\"incompatible\",\"a\":61,\"b\":40},{\"tag\":\"incompatible\",\"a\":61,\"b\":44},{\"tag\":\"incompatible\",\"a\":61,\"b\":53},{\"tag\":\"incompatible\",\"a\":61,\"b\":56},{\"tag\":\"incompatible\",\"a\":61,\"b\":57},{\"tag\":\"incompatible\",\"a\":74,\"b\":61},{\"tag\":\"incompatible\",\"a\":83,\"b\":61},{\"tag\":\"incompatible\",\"a\":88,\"b\":87},{\"tag\":\"incompatible\",\"a\":89,\"b\":87},{\"tag\":\"incompatible\",\"a\":90,\"b\":87},{\"tag\":\"incompatible\",\"a\":91,\"b\":87},{\"tag\":\"incompatible\",\"a\":92,\"b\":87},{\"tag\":\"incompatible\",\"a\":93,\"b\":87},{\"tag\":\"incompatible\",\"a\":97,\"b\":61},{\"tag\":\"incompatible\",\"a\":98,\"b\":24},{\"tag\":\"incompatible\",\"a\":98,\"b\":26},{\"tag\":\"incompatible\",\"a\":98,\"b\":27},{\"tag\":\"incompatible\",\"a\":98,\"b\":32},{\"tag\":\"incompatible\",\"a\":98,\"b\":87},{\"tag\":\"incompatible\",\"a\":100,\"b\":87},{\"tag\":\"incompatible\",\"a\":101,\"b\":87},{\"tag\":\"incompatible\",\"a\":102,\"b\":87},{\"tag\":\"incompatible\",\"a\":106,\"b\":61},{\"tag\":\"incompatible\",\"a\":110,\"b\":61},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[29,48,61]},{\"tag\":\"mate\",\"ridge\":74,\"a\":87,\"owners\":[1,49,50,51]},{\"tag\":\"mate\",\"ridge\":131,\"a\":26,\"owners\":[5,54,58,59]},{\"tag\":\"mate\",\"ridge\":131,\"a\":31,\"owners\":[2,47,49,52]},{\"tag\":\"mate\",\"ridge\":138,\"a\":45,\"owners\":[88,90,93]},{\"tag\":\"mate\",\"ridge\":259,\"a\":27,\"owners\":[6,55,58,60]},{\"tag\":\"mate\",\"ridge\":266,\"a\":46,\"owners\":[89,91,93]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[28,59,61]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[28,60,61]},{\"tag\":\"mate\",\"ridge\":529,\"a\":17,\"owners\":[7,56,57,59,60,83]},{\"tag\":\"mate\",\"ridge\":529,\"a\":75,\"owners\":[7,56,59,60]},{\"tag\":\"mate\",\"ridge\":529,\"a\":77,\"owners\":[7,56,57,60,83]},{\"tag\":\"mate\",\"ridge\":529,\"a\":78,\"owners\":[7,56,57,59,83]},{\"tag\":\"mate\",\"ridge\":530,\"a\":33,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":530,\"a\":56,\"owners\":[98,100,101]},{\"tag\":\"mate\",\"ridge\":530,\"a\":98,\"owners\":[7,56,59,60]},{\"tag\":\"mate\",\"ridge\":530,\"a\":100,\"owners\":[7,56,57,60,106]},{\"tag\":\"mate\",\"ridge\":530,\"a\":101,\"owners\":[7,56,57,59,106]},{\"tag\":\"mate\",\"ridge\":578,\"a\":57,\"owners\":[92,102]},{\"tag\":\"mate\",\"ridge\":578,\"a\":61,\"owners\":[92,98]},{\"tag\":\"mate\",\"ridge\":526,\"a\":92,\"owners\":[28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[24,25,26,27,29,31,32,33,34,40,87],\"full_literals\":[-55,7,8,9,10,12,13,14,15,16,17,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[49,50,51,61],\"full_literals\":[-56,23,24,25,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[53,54,55,56,57,58,59,60],\"full_literals\":[-57,27,28,29,30,31,32,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[44,45,46,47,48,52],\"full_literals\":[-58,18,19,20,21,22,26]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-60,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-63,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-64,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-64,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[7,17,33,56,57,59,60,74,75,77,78,83,97,98,100,101,106,110]}]}"
  "124 60 0 122 120 0\n125 63 0 122 121 0\n126 55 0 124 114 0\n127 59 0 124 115 0\n128 61 0 125 118 0\n129 62 0 125 119 0\n130 56 0 127 113 0\n131 57 0 128 116 0\n132 58 0 129 117 0\n133 -18 25 0 130 9 14 65 110 0\n134 -23 18 22 -41 0 132 76 72 74 94 71 73 92 12 22 112 0\n135 -25 18 22 -41 0 132 76 72 74 94 71 73 92 19 24 112 0\n136 18 22 -41 0 130 132 82 75 107 76 72 74 94 71 73 92 134 135 110 17 23 112 0\n137 -18 -41 0 131 84 82 83 102 85 75 106 25 28 32 40 47 56 111 0\n138 18 -41 0 136 1 13 18 20 89 0\n139 -41 0 137 138 0\n140 -22 0 130 139 126 2 3 4 5 6 7 8 13 18 20 21 91 108 110 63 64 86 107 88 101 81 109 0\n141 5 33 34 -35 0 86 101 87 77 70 69 68 67 97 99 100 98 105 104 103 123 0\n142 33 34 -35 0 131 68 67 66 141 27 31 111 39 0\n143 34 -35 0 139 126 86 101 64 63 62 142 43 44 45 46 50 51 95 93 108 107 78 79 109 0\n144 -35 0 139 126 62 63 64 86 101 143 52 53 54 55 59 60 61 96 90 108 107 78 80 109 0\n145 -23 18 0 140 132 10 11 12 22 112 0\n146 -19 -25 0 131 38 26 29 33 36 41 48 57 111 0\n147 -25 18 0 140 132 131 19 24 26 38 146 112 30 34 37 42 49 58 111 0\n148 18 0 144 130 140 132 145 147 110 15 16 17 23 112 0\n149 -27 0 148 25 0\n150 -28 0 148 28 0\n151 -29 0 148 32 0\n152 -30 0 148 35 0\n153 -32 0 148 40 0\n154 -33 0 148 47 0\n155 -34 0 148 56 0\n156 25 0 148 133 0\n157 31 0 153 131 154 152 150 149 151 155 111 0\n158 0 157 156 38 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record009
