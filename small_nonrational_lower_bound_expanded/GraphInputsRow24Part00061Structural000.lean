module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00061Data
public import GraphInputsRow24Part00061Frames
public import GraphInputsRow24Part00061Leaves
public import GraphInputsRow24Part00061Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 165507286305865728, (certNat% 3), (certNat% 4), (certNat% 5), 20203526160384, 81627743246090240]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), 183521684815347712, (certNat% 8), (certNat% 5), 24601572671488, 81627743246090240]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 199284283511144448, (certNat% 3), (certNat% 4), (certNat% 5), 24326694764544, 81627743246090240]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), 200410183417987072, (certNat% 8), (certNat% 5), 24601572671488, 81627743246090240]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 12)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010
def vertexColumn : Fields := ⟨10, (certNat% 13)⟩
def kindColumn : Fields := ⟨3, (certNat% 14)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 434038812134342656, (certNat% 16), 2882303761517117440, (certNat% 17), 4556376185503744]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 20), 477381560501272576, 5946158883012608, 90071992547409920]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), (certNat% 23), (certNat% 24), 309237645312, 45035996273704960]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 19), (certNat% 26), 477381560501272576, 4820258976169984, 90071992547409920]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), (certNat% 29), (certNat% 30), 279223176896970752, 288235083435868160]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), 4035225274713899008, (certNat% 32), (certNat% 33), 432350271511724032, 5523963597815808, 135107988821114880]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record037
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037
def vertexColumn : Fields := ⟨10, (certNat% 34)⟩
def kindColumn : Fields := ⟨3, (certNat% 35)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), (certNat% 37), 36100269569736704, 15762598695796736, (certNat% 38), 14699749183737298944]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), 36100269569736704, (certNat% 41), 14699749183737298944]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), (certNat% 44), 57570428830351360, 14699749183737298944, 9078668047417344, 30333206528]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record037

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record036
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "572caaaa6a56ac6a9a6655936538ce2b86e4789e17ac9aa669566c5a966555535534cd2b46d4749d17743b0ea398d538cd33a2e4b52ccb8acab1ad1b26c5ba1d8791cc789d2729c6725c5743c3c0e946458362384e0b81e0e545454352344d0b41da0e4350e2344c3322c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6d24924936db6d2492492492492492492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 38), (facetIndex 54), (facetIndex 68), (facetIndex 84)]))
 (.leaf ([(facetIndex 33), (facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 80), (facetIndex 81), (facetIndex 82), (facetIndex 83)]))
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 55)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 42), (facetIndex 56), (facetIndex 69), (facetIndex 85)]))
 (.leaf ([(facetIndex 41), (facetIndex 52), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60)])))
 (.branch 7
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 49), (facetIndex 50), (facetIndex 53)]))
 (.branch 8
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 39), (facetIndex 40), (facetIndex 43)]))
 (.leaf ([(facetIndex 51)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "40222222200000004011111115555430658663336674577077001z21;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 73)]))
 (.branch 2
 (.leaf ([(facetIndex 89)]))
 (.leaf ([(facetIndex 93)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 76)])))
 (.branch 6
 (.leaf ([(facetIndex 86), (facetIndex 87), (facetIndex 88)]))
 (.leaf ([(facetIndex 90), (facetIndex 91), (facetIndex 92)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "16d8db400000049036cz34;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record036" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record036" 99

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record036" "{\"ridges\":[[8,74],[9,137],[9,138],[14,577],[18,73],[18,76],[19,137],[19,140],[22,321],[26,74],[26,76],[27,138],[27,140],[30,322],[39,546],[41,577],[41,578],[43,642],[45,137],[45,138],[48,137],[48,138],[49,546],[52,577],[52,578],[53,137],[53,138],[53,642],[57,545],[57,577],[58,546],[58,641],[59,577],[60,577],[61,73],[62,137],[62,140],[64,73],[65,137],[65,140],[66,73],[67,73],[67,321],[69,321],[70,577],[70,612],[71,676],[72,577],[72,708],[74,545],[74,616],[75,641],[75,680],[76,712],[77,74],[78,138],[78,140],[80,74],[81,138],[81,140],[82,74],[83,74],[83,322],[85,322],[86,578],[86,612],[88,578],[88,708],[90,578],[90,616],[92,712]],\"owners\":[[18,73,[8,44,47,50,51,52,73,74,76],[61,64,66,67]],[61,73,[8,47,50,51,52,74,76],[18,44,64,66,67,73]],[64,73,[8,44,50,51,52,73,76],[18,47,61,66,67,74]],[66,73,[8,44,47,51,52,73,74],[18,50,61,64,67,76]],[67,73,[8,44,47,50,52,74,76],[18,51,61,64,66,73]],[8,74,[26,77,80,82,83,89,90,92],[44,47,50,51,52]],[26,74,[8,44,47,50,51,52,89,90,92],[77,80,82,83]],[77,74,[8,47,50,51,52,90,92],[26,44,80,82,83,89]],[80,74,[8,44,50,51,52,89,92],[26,47,77,82,83,90]],[82,74,[8,44,47,51,52,89,90],[26,50,77,80,83,92]],[83,74,[8,44,47,50,52,90,92],[26,51,77,80,82,89]],[9,137,[19,62,65,66,75,76],[45,48,50,53]],[19,137,[9,45,48,50,53,75,76],[62,65,66]],[45,137,[19,65,66,75,76],[9,48,50,53,62]],[48,137,[19,62,66,76],[9,45,50,53,65,75]],[53,137,[19,62,65,66],[9,45,48,50,75,76]],[62,137,[9,48,50,53,75,76],[19,45,65,66]],[65,137,[9,45,50,53,76],[19,48,62,66,75]],[9,138,[27,78,81,82,91,92],[45,48,50,53]],[27,138,[9,45,48,50,53,91,92],[78,81,82]],[45,138,[27,81,82,91,92],[9,48,50,53,78]],[48,138,[27,78,82,92],[9,45,50,53,81,91]],[53,138,[27,78,81,82],[9,45,48,50,91,92]],[78,138,[9,48,50,53,91,92],[27,45,81,82]],[81,138,[9,45,50,53,92],[27,48,78,82,91]],[57,545,[71,75],[12,39,49,55,58,70,74]],[74,545,[12,39,55,58,71],[49,57,70,75]],[39,546,[90,91],[12,49,55,57,58,86,87]],[49,546,[86,87],[12,39,55,57,58,90,91]],[58,546,[86,90],[12,39,49,55,57,87,91]],[22,321,[13,51,56,60,73],[67,69]],[67,321,[13,56,60],[22,51,69,73]],[69,321,[13,51,60],[22,56,67,73]],[30,322,[13,51,56,60,89],[83,85]],[83,322,[13,56,60],[30,51,85,89]],[85,322,[13,51,60],[30,56,83,89]],[14,577,[70,72,74,76],[41,52,57,59,60]],[41,577,[74,76],[14,52,57,59,60,70,72]],[52,577,[70,72],[14,41,57,59,60,74,76]],[57,577,[72,76],[14,41,52,59,60,70,74]],[59,577,[70,74],[14,41,52,57,60,72,76]],[60,577,[70,72,74,76],[14,41,52,57,59]],[70,577,[14,52,59,60,76],[41,57,72,74]],[72,577,[14,52,57,60,74],[41,59,70,76]],[41,578,[90,92],[14,52,57,59,60,86,88]],[52,578,[86,88],[14,41,57,59,60,90,92]],[86,578,[14,52,59,60,92],[41,57,88,90]],[88,578,[14,52,57,60,90],[41,59,86,92]],[90,578,[14,41,59,60,88],[52,57,86,92]],[58,641,[72,76],[15,43,53,59,71,75]],[75,641,[15,43,59,72],[53,58,71,76]],[43,642,[91,92],[15,53,58,59,87,88]],[53,642,[87,88],[15,43,58,59,91,92]],[18,76,[26,77,80,82,83,93],[61,64,66,67]],[26,76,[18,61,64,66,67,93],[77,80,82,83]],[19,140,[27,78,81,82],[62,65,66]],[27,140,[19,62,65,66],[78,81,82]],[62,140,[27,81,82],[19,65,66,78]],[65,140,[27,78,82],[19,62,66,81]],[78,140,[19,65,66],[27,62,81,82]],[81,140,[19,62,66],[27,65,78,82]],[70,612,[86],[]],[86,612,[70],[]],[71,676,[87],[]],[72,708,[88],[]],[88,708,[72],[]],[74,616,[90],[]],[90,616,[74],[]],[75,680,[91],[]],[76,712,[92],[]],[92,712,[76],[]]],\"edges\":[[26,[8,18,26,44,47,50,51,52,61,64,66,67,73,74,76,77,80,82,83,89,90,92,93]],[27,[9,19,27,45,48,50,53,62,65,66,75,76,78,81,82,91,92]],[40,[13,22,30,51,56,60,67,69,73,83,85,89,93]],[41,[14,41,52,57,59,60,70,72,74,76,86,88,90,92]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record036" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record036\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-18,-14],[-18,-15],[-18,-16],[-18,-17],[-19,-18],[-20,-2],[-21,-19],[-21,-20],[-22,-21],[-23,-20],[-23,-21],[-24,-20],[-24,-21],[-25,-23],[-27,-5],[-27,-18],[-27,-20],[-27,-21],[-27,-22],[-27,-23],[-27,-24],[-27,-26],[-28,-4],[-28,-27],[-29,-20],[-29,-23],[-30,-15],[-30,-16],[-31,-28],[-32,-6],[-32,-19],[-32,-27],[-33,-5],[-33,-18],[-33,-30],[-34,-3],[-34,-16],[-34,-26],[-34,-27],[-34,-30],[-34,-33],[-35,-1],[-35,-14],[-35,-17],[-35,-20],[-35,-23],[-35,-26],[-35,-27],[-35,-28],[-36,-8],[-37,-7],[-37,-36],[-39,-8],[-39,-37],[-40,-7],[-40,-36],[-40,-39],[-41,-34],[-42,-14],[-42,-17],[-44,-42],[-45,-15],[-46,-26],[-46,-41],[-46,-42],[-51,-11],[-52,-10],[-52,-51],[-53,-13],[-53,-38],[-54,-11],[-54,-52],[-55,-10],[-55,-51],[-55,-54],[-56,-34],[-56,-46],[-57,-14],[-57,-17],[-59,-57],[-60,-15],[-61,-57],[-7,1,20,23,26,27,28,47,48,50],[-36,1,23,26,27,28,48,50],[-39,1,20,26,27,28,47,50],[-41,1,20,23,27,28,47,48],[-42,1,20,23,26,28,48,50],[-1,10,51,54,56,57,62,63,65],[-10,1,20,23,26,27,28,62,63,65],[-51,1,23,26,27,28,63,65],[-54,1,20,26,27,28,62,65],[-56,1,20,23,27,28,62,63],[-57,1,20,23,26,28,63,65],[-2,8,37,40,41,49,50],[-8,2,21,24,26,29,49,50],[-21,8,40,41,49,50],[-24,8,37,41,50],[-29,8,37,40,41],[-37,2,24,26,29,49,50],[-40,2,21,26,29,50],[-2,11,52,55,56,64,65],[-11,2,21,24,26,29,64,65],[-21,11,55,56,64,65],[-24,11,52,56,65],[-29,11,52,55,56],[-52,2,24,26,29,64,65],[-55,2,21,26,29,65],[-32,45,49],[-48,3,16,30,33,45],[-16,63,64],[-25,59,60],[-33,59,63],[-9,4,27,31,35,47],[-42,4,31,35],[-43,4,27,35],[-12,4,27,31,35,62],[-57,4,31,35],[-58,4,27,35],[-5,44,46,48,50],[-18,48,50],[-28,44,46],[-32,46,50],[-34,44,48],[-35,44,46,48,50],[-44,5,28,34,35,50],[-46,5,28,32,35,48],[-18,63,65],[-28,59,61],[-59,5,28,34,35,65],[-61,5,28,32,35,63],[-63,5,18,34,35,61],[-33,46,50],[-49,6,19,34,46],[-19,64,65],[-29,60,61],[-7,10,51,54,56,57,66],[-10,7,36,39,41,42,66],[-8,11,52,55,56],[-11,8,37,40,41],[-37,11,55,56],[-40,11,52,56],[-52,8,40,41],[-55,8,37,41],[-44,59],[-59,44],[-45,60],[-46,61],[-61,46],[-48,63],[-63,48],[-49,64],[-50,65],[-65,50],[-67,13,36,37,38,39,40,41,42],[-68,51,52,53,54,55,56,57],[-69,22,23,24,30],[-70,18,28,32,33,34,35],[-71,20,21,25,26,29],[-72,14,15,16,17,19],[-73,27],[-74,67],[-75,68],[-75,69],[-76,74],[-76,75],[-77,70],[-78,72,73],[-79,73],[-80,71,79],[-81,71],[-80,78],[-81,79],[-82,77,81],[-82,80],[-83,81],[-84,76,83],[-84,82],[84],[-47,85],[-62,86],[-66,87],[-88,44,45,46],[-44,88],[-45,88],[-46,88],[-89,48,49,50],[-48,89],[-49,89],[-50,89],[-90,59,60,61],[-59,90],[-60,90],[-61,90],[-63,91],[-64,91],[-65,91],[-87,92],[-86,92],[-92,93],[-85,93],[-94,88,89],[-89,94],[-88,94],[-90,95],[-90,-91,96],[-94,-95,97],[-94,-96,98],[-98,99],[-93,-97,99],[-99],[1,7,10,20,23,26,27,28,36,39,41,42,47,48,50,51,54,56,57,62,63,65,66],[2,8,11,21,24,26,29,37,40,41,49,50,52,55,56,64,65],[4,9,12,27,31,35,42,43,47,57,58,62,66],[5,18,28,32,34,35,44,46,48,50,59,61,63,65]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":41,\"b\":36},{\"tag\":\"incompatible\",\"a\":41,\"b\":37},{\"tag\":\"incompatible\",\"a\":41,\"b\":39},{\"tag\":\"incompatible\",\"a\":41,\"b\":40},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":9},{\"tag\":\"incompatible\",\"a\":45,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":47,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":45},{\"tag\":\"incompatible\",\"a\":48,\"b\":44},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":51,\"b\":14},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":51,\"b\":44},{\"tag\":\"incompatible\",\"a\":51,\"b\":45},{\"tag\":\"incompatible\",\"a\":51,\"b\":46},{\"tag\":\"incompatible\",\"a\":51,\"b\":47},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":13},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":44},{\"tag\":\"incompatible\",\"a\":53,\"b\":47},{\"tag\":\"incompatible\",\"a\":55,\"b\":37},{\"tag\":\"incompatible\",\"a\":55,\"b\":39},{\"tag\":\"incompatible\",\"a\":56,\"b\":52},{\"tag\":\"incompatible\",\"a\":57,\"b\":15},{\"tag\":\"incompatible\",\"a\":57,\"b\":43},{\"tag\":\"incompatible\",\"a\":57,\"b\":51},{\"tag\":\"incompatible\",\"a\":58,\"b\":14},{\"tag\":\"incompatible\",\"a\":58,\"b\":41},{\"tag\":\"incompatible\",\"a\":58,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":12},{\"tag\":\"incompatible\",\"a\":59,\"b\":39},{\"tag\":\"incompatible\",\"a\":59,\"b\":50},{\"tag\":\"incompatible\",\"a\":59,\"b\":51},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":8},{\"tag\":\"incompatible\",\"a\":60,\"b\":36},{\"tag\":\"incompatible\",\"a\":60,\"b\":40},{\"tag\":\"incompatible\",\"a\":60,\"b\":44},{\"tag\":\"incompatible\",\"a\":60,\"b\":47},{\"tag\":\"incompatible\",\"a\":60,\"b\":50},{\"tag\":\"incompatible\",\"a\":60,\"b\":51},{\"tag\":\"incompatible\",\"a\":60,\"b\":52},{\"tag\":\"incompatible\",\"a\":61,\"b\":19},{\"tag\":\"incompatible\",\"a\":62,\"b\":18},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":19},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":18},{\"tag\":\"incompatible\",\"a\":65,\"b\":61},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":59},{\"tag\":\"incompatible\",\"a\":67,\"b\":36},{\"tag\":\"incompatible\",\"a\":67,\"b\":40},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":71,\"b\":37},{\"tag\":\"incompatible\",\"a\":72,\"b\":50},{\"tag\":\"incompatible\",\"a\":72,\"b\":66},{\"tag\":\"incompatible\",\"a\":72,\"b\":67},{\"tag\":\"incompatible\",\"a\":77,\"b\":27},{\"tag\":\"incompatible\",\"a\":78,\"b\":26},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":33},{\"tag\":\"incompatible\",\"a\":79,\"b\":63},{\"tag\":\"incompatible\",\"a\":80,\"b\":27},{\"tag\":\"incompatible\",\"a\":80,\"b\":78},{\"tag\":\"incompatible\",\"a\":81,\"b\":26},{\"tag\":\"incompatible\",\"a\":81,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":59},{\"tag\":\"incompatible\",\"a\":82,\"b\":72},{\"tag\":\"incompatible\",\"a\":83,\"b\":36},{\"tag\":\"incompatible\",\"a\":83,\"b\":40},{\"tag\":\"incompatible\",\"a\":86,\"b\":83},{\"tag\":\"incompatible\",\"a\":87,\"b\":37},{\"tag\":\"incompatible\",\"a\":88,\"b\":83},{\"tag\":\"mate\",\"ridge\":73,\"a\":18,\"owners\":[8,44,47,50,51,52,73,74,76]},{\"tag\":\"mate\",\"ridge\":73,\"a\":61,\"owners\":[8,47,50,51,52,74,76]},{\"tag\":\"mate\",\"ridge\":73,\"a\":64,\"owners\":[8,44,50,51,52,73,76]},{\"tag\":\"mate\",\"ridge\":73,\"a\":66,\"owners\":[8,44,47,51,52,73,74]},{\"tag\":\"mate\",\"ridge\":73,\"a\":67,\"owners\":[8,44,47,50,52,74,76]},{\"tag\":\"mate\",\"ridge\":74,\"a\":8,\"owners\":[26,77,80,82,83,89,90,92]},{\"tag\":\"mate\",\"ridge\":74,\"a\":26,\"owners\":[8,44,47,50,51,52,89,90,92]},{\"tag\":\"mate\",\"ridge\":74,\"a\":77,\"owners\":[8,47,50,51,52,90,92]},{\"tag\":\"mate\",\"ridge\":74,\"a\":80,\"owners\":[8,44,50,51,52,89,92]},{\"tag\":\"mate\",\"ridge\":74,\"a\":82,\"owners\":[8,44,47,51,52,89,90]},{\"tag\":\"mate\",\"ridge\":74,\"a\":83,\"owners\":[8,44,47,50,52,90,92]},{\"tag\":\"mate\",\"ridge\":137,\"a\":9,\"owners\":[19,62,65,66,75,76]},{\"tag\":\"mate\",\"ridge\":137,\"a\":19,\"owners\":[9,45,48,50,53,75,76]},{\"tag\":\"mate\",\"ridge\":137,\"a\":45,\"owners\":[19,65,66,75,76]},{\"tag\":\"mate\",\"ridge\":137,\"a\":48,\"owners\":[19,62,66,76]},{\"tag\":\"mate\",\"ridge\":137,\"a\":53,\"owners\":[19,62,65,66]},{\"tag\":\"mate\",\"ridge\":137,\"a\":62,\"owners\":[9,48,50,53,75,76]},{\"tag\":\"mate\",\"ridge\":137,\"a\":65,\"owners\":[9,45,50,53,76]},{\"tag\":\"mate\",\"ridge\":138,\"a\":9,\"owners\":[27,78,81,82,91,92]},{\"tag\":\"mate\",\"ridge\":138,\"a\":27,\"owners\":[9,45,48,50,53,91,92]},{\"tag\":\"mate\",\"ridge\":138,\"a\":45,\"owners\":[27,81,82,91,92]},{\"tag\":\"mate\",\"ridge\":138,\"a\":48,\"owners\":[27,78,82,92]},{\"tag\":\"mate\",\"ridge\":138,\"a\":53,\"owners\":[27,78,81,82]},{\"tag\":\"mate\",\"ridge\":138,\"a\":78,\"owners\":[9,48,50,53,91,92]},{\"tag\":\"mate\",\"ridge\":138,\"a\":81,\"owners\":[9,45,50,53,92]},{\"tag\":\"mate\",\"ridge\":545,\"a\":57,\"owners\":[71,75]},{\"tag\":\"mate\",\"ridge\":545,\"a\":74,\"owners\":[12,39,55,58,71]},{\"tag\":\"mate\",\"ridge\":546,\"a\":39,\"owners\":[90,91]},{\"tag\":\"mate\",\"ridge\":546,\"a\":49,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":546,\"a\":58,\"owners\":[86,90]},{\"tag\":\"mate\",\"ridge\":321,\"a\":22,\"owners\":[13,51,56,60,73]},{\"tag\":\"mate\",\"ridge\":321,\"a\":67,\"owners\":[13,56,60]},{\"tag\":\"mate\",\"ridge\":321,\"a\":69,\"owners\":[13,51,60]},{\"tag\":\"mate\",\"ridge\":322,\"a\":30,\"owners\":[13,51,56,60,89]},{\"tag\":\"mate\",\"ridge\":322,\"a\":83,\"owners\":[13,56,60]},{\"tag\":\"mate\",\"ridge\":322,\"a\":85,\"owners\":[13,51,60]},{\"tag\":\"mate\",\"ridge\":577,\"a\":14,\"owners\":[70,72,74,76]},{\"tag\":\"mate\",\"ridge\":577,\"a\":41,\"owners\":[74,76]},{\"tag\":\"mate\",\"ridge\":577,\"a\":52,\"owners\":[70,72]},{\"tag\":\"mate\",\"ridge\":577,\"a\":57,\"owners\":[72,76]},{\"tag\":\"mate\",\"ridge\":577,\"a\":59,\"owners\":[70,74]},{\"tag\":\"mate\",\"ridge\":577,\"a\":60,\"owners\":[70,72,74,76]},{\"tag\":\"mate\",\"ridge\":577,\"a\":70,\"owners\":[14,52,59,60,76]},{\"tag\":\"mate\",\"ridge\":577,\"a\":72,\"owners\":[14,52,57,60,74]},{\"tag\":\"mate\",\"ridge\":578,\"a\":41,\"owners\":[90,92]},{\"tag\":\"mate\",\"ridge\":578,\"a\":52,\"owners\":[86,88]},{\"tag\":\"mate\",\"ridge\":578,\"a\":86,\"owners\":[14,52,59,60,92]},{\"tag\":\"mate\",\"ridge\":578,\"a\":88,\"owners\":[14,52,57,60,90]},{\"tag\":\"mate\",\"ridge\":578,\"a\":90,\"owners\":[14,41,59,60,88]},{\"tag\":\"mate\",\"ridge\":641,\"a\":58,\"owners\":[72,76]},{\"tag\":\"mate\",\"ridge\":641,\"a\":75,\"owners\":[15,43,59,72]},{\"tag\":\"mate\",\"ridge\":642,\"a\":43,\"owners\":[91,92]},{\"tag\":\"mate\",\"ridge\":642,\"a\":53,\"owners\":[87,88]},{\"tag\":\"mate\",\"ridge\":76,\"a\":18,\"owners\":[26,77,80,82,83,93]},{\"tag\":\"mate\",\"ridge\":76,\"a\":26,\"owners\":[18,61,64,66,67,93]},{\"tag\":\"mate\",\"ridge\":140,\"a\":19,\"owners\":[27,78,81,82]},{\"tag\":\"mate\",\"ridge\":140,\"a\":27,\"owners\":[19,62,65,66]},{\"tag\":\"mate\",\"ridge\":140,\"a\":62,\"owners\":[27,81,82]},{\"tag\":\"mate\",\"ridge\":140,\"a\":65,\"owners\":[27,78,82]},{\"tag\":\"mate\",\"ridge\":140,\"a\":78,\"owners\":[19,65,66]},{\"tag\":\"mate\",\"ridge\":140,\"a\":81,\"owners\":[19,62,66]},{\"tag\":\"mate\",\"ridge\":612,\"a\":70,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":612,\"a\":86,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":676,\"a\":71,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":708,\"a\":72,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":708,\"a\":88,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":616,\"a\":74,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":616,\"a\":90,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":680,\"a\":75,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":712,\"a\":76,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":712,\"a\":92,\"owners\":[76]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[33,61,62,63,64,65,66,67],\"full_literals\":[-67,13,36,37,38,39,40,41,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[77,78,79,80,81,82,83],\"full_literals\":[-68,51,52,53,54,55,56,57]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[46,47,48,55],\"full_literals\":[-69,22,23,24,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[41,52,57,58,59,60],\"full_literals\":[-70,18,28,32,33,34,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[44,45,49,50,53],\"full_literals\":[-71,20,21,25,26,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[36,37,39,40,43],\"full_literals\":[-72,14,15,16,17,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[51],\"full_literals\":[-73,27]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-75,68,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-75,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-76,74,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-76,false,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,72,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,false,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-80,71,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-81,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,false,78],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-81,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-82,77,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-82,false,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-83,false,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-84,76,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-84,false,82],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":73,\"full_literals\":[-47,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":89,\"full_literals\":[-62,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":93,\"full_literals\":[-66,87]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[70,71,72],\"full_literals\":[-88,44,45,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":70,\"full_literals\":[-44,88]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-45,88]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-46,88]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[74,75,76],\"full_literals\":[-89,48,49,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-48,89]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":75,\"full_literals\":[-49,89]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-50,89]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[86,87,88],\"full_literals\":[-90,59,60,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":86,\"full_literals\":[-59,90]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-60,90]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":88,\"full_literals\":[-61,90]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":90,\"full_literals\":[-63,91]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":91,\"full_literals\":[-64,91]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":92,\"full_literals\":[-65,91]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-86,false,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-92,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-94,88,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-89,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-88,false,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-90,false,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-90,-91,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-94,-95,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-94,-96,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-98,99],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-93,-97,99],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":26,\"owners\":[8,18,26,44,47,50,51,52,61,64,66,67,73,74,76,77,80,82,83,89,90,92,93]},{\"tag\":\"edge\",\"edge\":27,\"owners\":[9,19,27,45,48,50,53,62,65,66,75,76,78,81,82,91,92]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[13,22,30,51,56,60,67,69,73,83,85,89,93]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[14,41,52,57,59,60,70,72,74,76,86,88,90,92]}]}"
  "215 82 0 178 177 0\n216 80 0 215 174 0\n217 78 0 216 171 0\n218 -98 0 210 208 0\n219 94 0 202 203 187 188 189 183 184 185 120 150 153 119 121 123 124 145 108 148 214 0\n220 -96 0 219 218 207 0\n221 -81 90 0 193 192 135 191 111 170 172 168 160 17 18 22 158 0\n222 -27 90 0 215 178 221 175 176 165 163 173 166 193 191 128 16 19 20 21 32 39 48 156 157 35 0\n223 -33 34 35 90 0 193 191 33 34 112 131 0\n224 -32 34 90 0 193 147 192 146 30 31 108 133 0\n225 -18 -72 0 1 2 3 4 5 159 0\n226 34 35 90 0 215 217 222 160 167 225 221 173 166 193 191 128 223 224 157 0\n227 -34 90 0 192 146 191 144 36 37 40 41 123 109 0\n228 90 0 178 217 216 191 192 193 111 135 221 175 176 165 163 222 160 168 167 169 227 226 43 44 45 46 47 158 7 9 13 156 27 28 159 0\n229 -91 0 228 220 205 0\n230 -63 0 229 194 0\n231 -64 0 229 195 0\n232 -65 0 229 196 0\n233 -16 0 230 231 110 0\n234 -48 0 230 149 0\n235 -19 0 231 232 134 0\n236 -49 0 231 151 0\n237 -50 0 232 152 0\n238 -18 0 232 230 127 0\n239 -89 0 236 234 237 186 0\n240 88 0 239 219 201 0\n241 -35 93 0 232 230 237 234 199 198 180 197 181 200 179 42 45 46 47 48 49 89 92 93 91 83 86 87 85 90 84 211 0\n242 10 36 39 41 42 51 54 56 57 20 26 23 27 28 93 0 232 230 237 234 199 198 180 197 181 200 179 88 136 211 0\n243 36 39 41 42 51 54 56 57 20 26 23 27 28 93 0 178 160 168 172 175 176 165 162 164 161 199 197 181 242 67 73 137 155 51 55 69 70 154 0\n244 -36 41 56 26 0 232 231 237 236 50 52 56 94 139 143 98 97 96 142 212 0\n245 36 41 93 42 51 54 56 57 20 26 23 27 28 0 236 237 231 232 243 53 54 57 94 139 143 98 97 96 142 212 0\n246 41 42 51 54 56 57 20 26 23 27 28 93 0 244 245 0\n247 -41 -70 28 35 0 237 238 58 64 122 132 157 0\n248 -42 -72 0 233 235 240 59 60 61 65 159 182 62 0\n249 -51 56 26 41 0 232 231 237 236 66 68 74 101 138 103 141 104 105 140 212 0\n250 51 56 41 42 93 57 20 26 23 27 28 0 236 237 231 232 246 71 72 75 101 138 103 141 104 105 140 212 0\n251 56 57 20 26 23 27 28 93 0 215 217 160 167 248 241 168 172 173 166 247 249 250 0\n252 -56 -70 28 35 0 237 238 76 77 122 132 157 0\n253 -57 -72 0 233 235 228 78 79 80 82 159 190 81 0\n254 26 23 27 28 93 0 215 217 232 231 237 236 160 167 253 241 168 172 173 166 252 247 251 6 8 12 25 95 100 102 107 99 106 212 0\n255 -26 -70 28 35 0 237 238 38 63 122 132 157 0\n256 27 28 93 0 216 215 241 160 168 172 169 173 166 255 254 10 11 14 26 158 0\n257 28 93 0 232 230 237 234 238 241 256 15 32 39 130 129 126 125 214 0\n258 93 0 199 200 197 198 179 181 180 241 257 23 24 29 113 115 118 116 114 117 213 0\n259 95 0 228 204 0\n260 -97 0 258 210 209 0\n261 0 259 260 219 206 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record036_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record036
