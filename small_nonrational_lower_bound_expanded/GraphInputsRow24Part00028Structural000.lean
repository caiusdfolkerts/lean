module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00028Data
public import GraphInputsRow24Part00028Frames
public import GraphInputsRow24Part00028Leaves
public import GraphInputsRow24Part00028Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 1133596488237056, (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 126100789566373888, (certNat% 8), (certNat% 9)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), (certNat% 13), 54192729109823488, 7881299347898368]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), 13835058055282163712, (certNat% 16), 3870280929771520]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 19), 4081387162304512, (certNat% 20)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 19), 10952754293765046272, (certNat% 22), (certNat% 23), 3870280929771520]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 11), (certNat% 12), (certNat% 25), 54192729109823488, 8444249301319680]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), (certNat% 3), (certNat% 15), (certNat% 28)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 30), (certNat% 5), (certNat% 31), (certNat% 27)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), 293859875685924864, (certNat% 3), (certNat% 5), (certNat% 28), (certNat% 27)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 10376295740484878336, 8866461766385664, (certNat% 34), 126100927005327360, (certNat% 20)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 5), (certNat% 36), (certNat% 20), (certNat% 37)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 27), (certNat% 39), (certNat% 40)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 5), 4222124650659840, (certNat% 42), (certNat% 20)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), 9223653580550963200, (certNat% 16), 3448068464705536]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 19), (certNat% 22), (certNat% 46), 3448068464705536, (certNat% 47)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c22 c19
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c23 c16
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 49), (certNat% 50), (certNat% 51), (certNat% 52), 8655355533852672, 4611686018427387904]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c26 c15
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c27 c14
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c28 c9
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c29 c8
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c30 c3
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c31 c0
  c32
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012
def vertexColumn : Fields := ⟨10, (certNat% 53)⟩
def kindColumn : Fields := ⟨3, (certNat% 54)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), (certNat% 56), 576462478880276480, (certNat% 57), (certNat% 58), 4468419550248960, 571957187035791360]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019
def vertexColumn : Fields := ⟨10, (certNat% 59)⟩
def kindColumn : Fields := ⟨3, (certNat% 60)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 62), 865114440431828992, 1750422511419392, (certNat% 63), (certNat% 64), 247704782733574144]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "bc1f34a368ba1eb46c5a562d8765392e2b86e2785e0fb49364b91e745c56552d4755352d2b46d2745d0f743c4e9334e331cf0b62e4b52ccb4ac6b26c5b0ef0791d4749ca719e1745c9723c1f948b22a8560d90e1382e944b12a4550d50d1342dc0e4328e1324c530cd0b22c4b0ad0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36da6da49249a4da6da49249a492492492492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 36), (facetIndex 41), (facetIndex 42), (facetIndex 68), (facetIndex 84)]))
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 39), (facetIndex 47), (facetIndex 64), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 40), (facetIndex 49), (facetIndex 58), (facetIndex 65), (facetIndex 81)]))
 (.leaf ([(facetIndex 46), (facetIndex 48), (facetIndex 50), (facetIndex 51), (facetIndex 52)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57)]))
 (.leaf ([(facetIndex 38), (facetIndex 43), (facetIndex 63), (facetIndex 67), (facetIndex 79), (facetIndex 83)])))
 (.branch 7
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 59), (facetIndex 60), (facetIndex 72), (facetIndex 75), (facetIndex 76), (facetIndex 88)]))
 (.leaf ([(facetIndex 37), (facetIndex 62), (facetIndex 66), (facetIndex 78), (facetIndex 82)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6000bd1bc6c06000bd1bc6ca49236d32f6a02378909z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 69), (facetIndex 70)]))
 (.branch 2
 (.leaf ([(facetIndex 74), (facetIndex 86)]))
 (.leaf ([(facetIndex 85)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 90)]))
 (.leaf ([(facetIndex 61), (facetIndex 71), (facetIndex 73)])))
 (.branch 6
 (.leaf ([(facetIndex 77), (facetIndex 87), (facetIndex 89)]))
 (.leaf ([(facetIndex 91), (facetIndex 92)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6ce8a5000002806080000002z2e;"⟩
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
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped3_0009 : List Nat := [1]
def grouped3_0010 : List Nat := [1, 2]
def grouped3_0011 : List Nat := [2]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record007" 28

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record007" "{\"ridges\":[[15,770],[42,770],[52,770],[57,770],[58,770],[69,788],[70,836],[74,840]],\"owners\":[[15,770,[85,86,90],[42,52,57,58]],[42,770,[90],[15,52,57,58,85,86]],[52,770,[85,86],[15,42,57,58,90]],[57,770,[86,90],[15,42,52,58,85]],[58,770,[85],[15,42,52,57,86,90]],[69,788,[85],[]],[70,836,[86],[]],[74,840,[90],[]]],\"edges\":[[44,[15,42,52,57,58,69,70,74,85,86,90]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-17,-2],[-17,-4],[-17,-11],[-17,-16],[-18,-3],[-18,-6],[-18,-10],[-18,-15],[-19,-3],[-19,-6],[-19,-9],[-19,-10],[-19,-15],[-1,17,18,19],[-5,19],[-7,17,18],[-8,18,19],[-9,17],[-12,17],[-13,18],[-14,19],[-20,2,4,5,11,16],[-21,3,6,9,10,15],[-22,20],[-23,21],[-24,22],[-24,23],[-25,24],[25],[-26,14,18],[-18,26],[-27,17],[-17,27],[-28,26,27],[-27,28],[-26,28],[1,5,7,8,9,12,13,14,17,18,19]],\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":85,\"b\":36},{\"tag\":\"incompatible\",\"a\":85,\"b\":41},{\"tag\":\"incompatible\",\"a\":85,\"b\":68},{\"tag\":\"incompatible\",\"a\":85,\"b\":84},{\"tag\":\"incompatible\",\"a\":86,\"b\":40},{\"tag\":\"incompatible\",\"a\":86,\"b\":49},{\"tag\":\"incompatible\",\"a\":86,\"b\":65},{\"tag\":\"incompatible\",\"a\":86,\"b\":81},{\"tag\":\"incompatible\",\"a\":90,\"b\":40},{\"tag\":\"incompatible\",\"a\":90,\"b\":49},{\"tag\":\"incompatible\",\"a\":90,\"b\":58},{\"tag\":\"incompatible\",\"a\":90,\"b\":65},{\"tag\":\"incompatible\",\"a\":90,\"b\":81},{\"tag\":\"mate\",\"ridge\":770,\"a\":15,\"owners\":[85,86,90]},{\"tag\":\"mate\",\"ridge\":770,\"a\":42,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":770,\"a\":52,\"owners\":[85,86]},{\"tag\":\"mate\",\"ridge\":770,\"a\":57,\"owners\":[86,90]},{\"tag\":\"mate\",\"ridge\":770,\"a\":58,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":788,\"a\":69,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":836,\"a\":70,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":840,\"a\":74,\"owners\":[90]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[36,41,42,68,84],\"full_literals\":[-20,2,4,5,11,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[40,49,58,65,81],\"full_literals\":[-21,3,6,9,10,15]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-22,20,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-23,21,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-24,22,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-24,false,23],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-25,24,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[74,86],\"full_literals\":[-26,14,18]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":86,\"full_literals\":[-18,26]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[85],\"full_literals\":[-27,17]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":85,\"full_literals\":[-17,27]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-28,26,27],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,28],\"grouped\":true,\"kind\":3},{\"tag\":\"edge\",\"edge\":44,\"owners\":[15,42,52,57,58,69,70,74,85,86,90]}]}"
  "38 24 0 29 28 0\n39 22 0 38 26 0\n40 23 0 38 27 0\n41 20 0 39 24 0\n42 21 0 40 25 0\n43 28 19 0 21 15 35 36 33 31 14 18 19 17 20 16 37 0\n44 -19 0 42 9 10 11 12 13 23 0\n45 -5 0 44 15 0\n46 -14 0 44 21 0\n47 28 0 44 43 0\n48 -17 0 45 41 1 2 3 4 22 0\n49 -9 0 48 18 0\n50 -27 0 48 32 0\n51 26 0 50 47 34 0\n52 18 0 51 46 30 0\n53 -3 0 52 5 0\n54 -6 0 52 6 0\n55 -10 0 52 7 0\n56 -15 0 52 8 0\n57 0 55 56 42 53 54 49 23 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record013
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "31c2f34a4e8bac3a4e2b86e4789e17b49c65392e715c362d2b46d8751d2745dd0d934cf0b92d4b4acab1ac9b16f0791cc719d1715e0f43c8f2d24c0f0b24683a298960d84e0b81e2c709925190e645294950d60d1342d074a344c930cd0b12c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "d349a4924924d249249a4924924d2492489249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 47), (facetIndex 48), (facetIndex 55), (facetIndex 56)]))
 (.leaf ([(facetIndex 38), (facetIndex 40), (facetIndex 43), (facetIndex 44), (facetIndex 45)])))
 (.branch 3
 (.leaf ([(facetIndex 52), (facetIndex 54), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 71), (facetIndex 74), (facetIndex 76)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 78), (facetIndex 79)]))
 (.leaf ([(facetIndex 50), (facetIndex 59), (facetIndex 63), (facetIndex 67), (facetIndex 75), (facetIndex 81)])))
 (.branch 7
 (.leaf ([(facetIndex 39), (facetIndex 49), (facetIndex 51), (facetIndex 53)]))
 (.branch 8
 (.leaf ([(facetIndex 58), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 68)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "50440353443228507757775700026265600011100161z26;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 57)]))
 (.leaf ([(facetIndex 66), (facetIndex 77)])))
 (.branch 3
 (.leaf ([(facetIndex 80)]))
 (.leaf ([(facetIndex 82)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "320400001z21;"⟩
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
def grouped2_0008 : List Nat := [4, 5]
def grouped2_0009 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7, 8]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8]
def grouped2_0014 : List Nat := [8]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [2]
def grouped3_0020 : List Nat := [2, 3]
def grouped3_0021 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record013" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record013" 63

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record013" "{\"ridges\":[[8,266],[11,259],[11,273],[22,273],[33,266],[33,280],[39,259],[39,266],[41,67],[42,259],[43,67],[44,67],[45,67],[49,67],[49,74],[51,259],[51,266],[52,266],[54,776],[55,259],[56,259],[56,273],[57,67],[57,259],[57,834],[60,273],[66,273],[66,788],[68,273],[68,280],[71,74],[73,266],[79,266],[80,74],[80,266],[80,834],[82,280],[82,788]],\"owners\":[[41,67,[7,49,52,53,57],[3,43,44,45,47]],[43,67,[7,47,52,53,57],[3,41,44,45,49]],[44,67,[7,47,49,52,53,57],[3,41,43,45]],[45,67,[7,47,49,52],[3,41,43,44,53,57]],[11,259,[8,39,46,51,52,54,57],[42,55,56]],[55,259,[8,39,46,52,54,57],[11,42,51,56]],[56,259,[8,39,46,51,52,54,57],[11,42,55]],[8,266,[33,73,77,79,80],[39,51,52,54]],[33,266,[8,39,51,52,54,77,80],[73,79]],[52,266,[33,73,77,79],[8,39,51,54,80]],[79,266,[8,39,52,54,77,80],[33,51,73]],[22,273,[11,42,55,56,66],[60,68,69]],[60,273,[11,55,56],[22,42,66,68,69]],[54,776,[82],[24,65,69,70,77,80]],[57,834,[80],[]],[80,834,[57],[]],[66,788,[82],[]],[82,788,[66],[]]],\"edges\":[[15,[8,11,33,39,42,46,51,52,54,55,56,57,73,77,79,80]],[33,[11,22,33,42,55,56,60,66,68,69,73,79,82]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record013" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record013\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-7],[-10,-7],[-14,-6],[-14,-8],[-14,-11],[-14,-12],[-14,-13],[-15,-7],[-16,-7],[-17,-2],[-17,-6],[-17,-11],[-18,-1],[-18,-6],[-18,-15],[-18,-16],[-18,-17],[-19,-17],[-19,-18],[-20,-19],[-21,-17],[-21,-18],[-21,-20],[-22,-18],[-23,-15],[-27,-18],[-27,-21],[-27,-22],[-28,-7],[-28,-18],[-28,-27],[-29,-8],[-29,-20],[-32,-17],[-33,-14],[-34,-30],[-34,-32],[-35,-18],[-35,-27],[-36,-8],[-36,-13],[-36,-19],[-36,-20],[-36,-29],[-36,-33],[-37,-7],[-37,-10],[-37,-14],[-37,-28],[-37,-31],[-37,-34],[-9,1,17,19,20,24],[-11,1,15,19,20,24],[-12,1,15,17,19,20,24],[-13,1,15,17,19],[-12,-17,-24],[-17,-30,-36],[-3,2,7,14,18,19,21,24],[-22,2,7,14,19,21,24],[-23,2,7,14,18,19,21,24],[-3,-18,-24],[-7,-22,-24],[-7,-23,-24],[-10,-18,-24],[-18,-23,-24],[-2,5,31,34,35,36],[-5,2,7,18,19,21,34,36],[-19,5,31,34,35],[-35,2,7,19,21,34,36],[-5,-18,-36],[-7,-35,-36],[-18,-31,-36],[-4,3,10,22,23,26],[-25,3,22,23],[-3,-26,-27],[-23,-26,-27],[-5,-27,-37],[-21,37],[-24,36],[-36,24],[-26,37],[-37,26],[-38,9,10,15,16,22,23],[-39,6,8,11,12,13],[-40,19,21,28,29],[-41,30,32,33],[-42,7,17,18,20],[-43,27],[-44,38],[-44,39],[-45,40],[-45,41],[-46,44,45],[-47,44],[-47,45],[-48,43],[-49,42,48],[-50,42],[-50,48],[-51,49],[-52,50],[-53,46],[-53,47,52],[-53,51],[53],[-54,14,24],[-55,26,34],[-26,55],[-56,36],[-36,56],[-57,37],[-37,57],[-55,58],[-59,54],[-59,55],[-60,56,57],[-61,57],[-56,-57,61],[-62,59,60],[-58,-61,63],[62],[-63],[2,3,5,7,10,14,18,19,21,22,23,24,31,34,35,36],[3,4,5,10,22,23,25,26,27,28,31,35,37]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":41,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":39},{\"tag\":\"incompatible\",\"a\":46,\"b\":38},{\"tag\":\"incompatible\",\"a\":46,\"b\":40},{\"tag\":\"incompatible\",\"a\":46,\"b\":43},{\"tag\":\"incompatible\",\"a\":46,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":47,\"b\":39},{\"tag\":\"incompatible\",\"a\":48,\"b\":39},{\"tag\":\"incompatible\",\"a\":49,\"b\":8},{\"tag\":\"incompatible\",\"a\":49,\"b\":38},{\"tag\":\"incompatible\",\"a\":49,\"b\":43},{\"tag\":\"incompatible\",\"a\":51,\"b\":7},{\"tag\":\"incompatible\",\"a\":51,\"b\":38},{\"tag\":\"incompatible\",\"a\":51,\"b\":47},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":49},{\"tag\":\"incompatible\",\"a\":54,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":55,\"b\":51},{\"tag\":\"incompatible\",\"a\":56,\"b\":47},{\"tag\":\"incompatible\",\"a\":68,\"b\":51},{\"tag\":\"incompatible\",\"a\":68,\"b\":54},{\"tag\":\"incompatible\",\"a\":68,\"b\":55},{\"tag\":\"incompatible\",\"a\":69,\"b\":39},{\"tag\":\"incompatible\",\"a\":69,\"b\":51},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":40},{\"tag\":\"incompatible\",\"a\":70,\"b\":53},{\"tag\":\"incompatible\",\"a\":74,\"b\":49},{\"tag\":\"incompatible\",\"a\":76,\"b\":46},{\"tag\":\"incompatible\",\"a\":77,\"b\":71},{\"tag\":\"incompatible\",\"a\":77,\"b\":74},{\"tag\":\"incompatible\",\"a\":79,\"b\":51},{\"tag\":\"incompatible\",\"a\":79,\"b\":68},{\"tag\":\"incompatible\",\"a\":80,\"b\":40},{\"tag\":\"incompatible\",\"a\":80,\"b\":45},{\"tag\":\"incompatible\",\"a\":80,\"b\":52},{\"tag\":\"incompatible\",\"a\":80,\"b\":53},{\"tag\":\"incompatible\",\"a\":80,\"b\":70},{\"tag\":\"incompatible\",\"a\":80,\"b\":76},{\"tag\":\"incompatible\",\"a\":82,\"b\":39},{\"tag\":\"incompatible\",\"a\":82,\"b\":42},{\"tag\":\"incompatible\",\"a\":82,\"b\":46},{\"tag\":\"incompatible\",\"a\":82,\"b\":69},{\"tag\":\"incompatible\",\"a\":82,\"b\":73},{\"tag\":\"incompatible\",\"a\":82,\"b\":77},{\"tag\":\"mate\",\"ridge\":67,\"a\":41,\"owners\":[7,49,52,53,57]},{\"tag\":\"mate\",\"ridge\":67,\"a\":43,\"owners\":[7,47,52,53,57]},{\"tag\":\"mate\",\"ridge\":67,\"a\":44,\"owners\":[7,47,49,52,53,57]},{\"tag\":\"mate\",\"ridge\":67,\"a\":45,\"owners\":[7,47,49,52]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[44,49,57]},{\"tag\":\"three\",\"ridge\":74,\"vertices\":[49,71,80]},{\"tag\":\"mate\",\"ridge\":259,\"a\":11,\"owners\":[8,39,46,51,52,54,57]},{\"tag\":\"mate\",\"ridge\":259,\"a\":55,\"owners\":[8,39,46,52,54,57]},{\"tag\":\"mate\",\"ridge\":259,\"a\":56,\"owners\":[8,39,46,51,52,54,57]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[11,51,57]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[39,55,57]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[39,56,57]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[42,51,57]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[51,56,57]},{\"tag\":\"mate\",\"ridge\":266,\"a\":8,\"owners\":[33,73,77,79,80]},{\"tag\":\"mate\",\"ridge\":266,\"a\":33,\"owners\":[8,39,51,52,54,77,80]},{\"tag\":\"mate\",\"ridge\":266,\"a\":52,\"owners\":[33,73,77,79]},{\"tag\":\"mate\",\"ridge\":266,\"a\":79,\"owners\":[8,39,52,54,77,80]},{\"tag\":\"three\",\"ridge\":266,\"vertices\":[33,51,80]},{\"tag\":\"three\",\"ridge\":266,\"vertices\":[39,79,80]},{\"tag\":\"three\",\"ridge\":266,\"vertices\":[51,73,80]},{\"tag\":\"mate\",\"ridge\":273,\"a\":22,\"owners\":[11,42,55,56,66]},{\"tag\":\"mate\",\"ridge\":273,\"a\":60,\"owners\":[11,55,56]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[11,66,68]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[56,66,68]},{\"tag\":\"three\",\"ridge\":280,\"vertices\":[33,68,82]},{\"tag\":\"mate\",\"ridge\":776,\"a\":54,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":834,\"a\":57,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":834,\"a\":80,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":788,\"a\":66,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":788,\"a\":82,\"owners\":[66]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[41,42,47,48,55,56],\"full_literals\":[-38,9,10,15,16,22,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[38,40,43,44,45],\"full_literals\":[-39,6,8,11,12,13]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[52,54,69,70],\"full_literals\":[-40,19,21,28,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[71,74,76],\"full_literals\":[-41,30,32,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[39,49,51,53],\"full_literals\":[-42,7,17,18,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[68],\"full_literals\":[-43,27]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,44,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-47,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,42,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-50,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-52,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-53,46,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-53,47,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-53,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[46,57],\"full_literals\":[-54,14,24]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[66,77],\"full_literals\":[-55,26,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-26,55]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[80],\"full_literals\":[-56,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":80,\"full_literals\":[-36,56]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[82],\"full_literals\":[-57,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-37,57]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,54,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-57,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-58,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":15,\"owners\":[8,11,33,39,42,46,51,52,54,55,56,57,73,77,79,80]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[11,22,33,42,55,56,60,66,68,69,73,79,82]}]}"
  "125 46 0 105 102 0\n126 51 0 105 104 0\n127 49 0 126 100 0\n128 -61 0 122 117 120 111 113 82 108 0\n129 -27 -57 0 128 118 110 79 111 82 51 50 48 47 46 26 27 28 39 77 75 76 66 68 123 0\n130 18 19 21 22 23 35 -57 0 128 127 105 111 49 129 88 96 99 101 103 95 91 85 33 97 118 110 79 51 50 48 47 46 87 10 58 67 123 0\n131 19 21 22 23 35 -57 0 128 105 129 88 96 99 101 103 95 91 94 89 118 110 79 111 49 47 85 33 130 13 15 16 17 83 52 0\n132 -19 -57 0 127 129 88 96 97 111 46 18 19 20 87 0\n133 -21 -57 0 127 129 88 96 97 111 46 21 22 23 87 0\n134 -22 -57 0 128 127 105 132 111 49 129 88 96 99 101 103 95 91 133 85 33 97 118 110 79 48 46 24 59 87 10 0\n135 18 -23 -57 0 128 127 105 132 111 49 129 88 96 99 101 103 95 91 133 85 33 97 118 110 79 48 46 87 60 10 0\n136 -23 -57 0 128 105 132 111 49 129 88 96 99 101 103 95 91 133 85 33 32 94 90 118 110 79 25 135 13 14 17 53 54 55 84 0\n137 -57 0 128 127 105 111 118 46 49 51 110 129 88 96 99 97 101 103 95 91 132 133 85 33 134 136 131 38 69 87 10 0\n138 -37 0 137 112 0\n139 -21 0 138 78 0\n140 -26 0 138 81 0\n141 -35 -36 0 127 105 80 43 41 40 38 39 71 88 96 99 97 101 87 103 11 12 56 94 84 90 0\n142 -17 -36 0 125 80 45 41 40 11 12 34 56 57 86 84 92 90 93 0\n143 44 18 -36 0 125 105 139 142 44 43 42 93 94 91 103 85 101 29 98 87 0\n144 -28 18 -36 0 127 142 43 29 31 87 88 97 96 0\n145 18 -36 0 139 105 142 80 44 43 42 143 89 144 85 91 95 103 101 98 87 1 2 8 9 62 63 83 0\n146 -36 0 138 140 80 141 145 24 26 30 61 64 65 70 72 73 74 124 0\n147 -24 0 146 79 0\n148 -56 0 146 109 0\n149 -60 0 148 137 116 0\n150 59 0 149 121 119 0\n151 54 0 150 114 0\n152 55 0 150 115 0\n153 14 0 151 147 106 0\n154 34 0 152 140 107 0\n155 -6 0 153 3 0\n156 -8 0 153 4 0\n157 -11 0 153 5 0\n158 -12 0 153 6 0\n159 -13 0 153 7 0\n160 -33 0 153 35 0\n161 -30 0 154 36 0\n162 -32 0 154 37 0\n163 -39 0 158 156 157 159 155 84 0\n164 -41 0 162 160 161 86 0\n165 -44 0 163 90 0\n166 -45 0 164 92 0\n167 0 165 166 125 93 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00028.record013
