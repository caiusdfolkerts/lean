module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00029Data
public import GraphInputsRow24Part00029Frames
public import GraphInputsRow24Part00029Leaves
public import GraphInputsRow24Part00029Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 648520545364606976, (certNat% 3), (certNat% 4), (certNat% 5), 18691697672192, 51228445761339392]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 720611124751368192, (certNat% 3), (certNat% 4), (certNat% 5), 18691697672192, 51228445761339392]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 7)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record031
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031
def vertexColumn : Fields := ⟨10, (certNat% 8)⟩
def kindColumn : Fields := ⟨3, (certNat% 9)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), 13194139533312]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 577604252986245120, (certNat% 12), (certNat% 14), (certNat% 15), 4947802324992]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 576461851815051264, (certNat% 17), 10376293610181099520, (certNat% 18), (certNat% 19)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 324259173304893440, 1730508165407047680, 299342040662016, (certNat% 21)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 1730508156817113088, (certNat% 23), 6459630813184, (certNat% 24)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 1154047404513689600, (certNat% 23), 9223372105574252544, (certNat% 27)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 28)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c8 c9
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c8 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c8 c12
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c8 c13
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c14
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c8 c15
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c8 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c17 c11
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 36028797018963968, 577586652210266112, 9223372039002259456, (certNat% 30)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), 282711944069120, 1730508156817113088, 9223380835095281664, (certNat% 32), (certNat% 33)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 30), 10376293610181099520, (certNat% 17), 577604253053353984, 282711944069120, 13743895347200]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c24 c6
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c25 c5
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c26 c4
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c27 c3
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c28 c2
  c29
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record031

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record038
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038
def vertexColumn : Fields := ⟨10, (certNat% 35)⟩
def kindColumn : Fields := ⟨3, (certNat% 36)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), 153122662208503808, (certNat% 40)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1727130343279951872, 578712620836585472, (certNat% 41), (certNat% 39), (certNat% 42), (certNat% 43)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 45), 288072046477312, 36028797018963968]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 47), 288072046477312, 36028797018963968, 6917529027641081856]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c4 c2
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), 411217348788224, (certNat% 49), (certNat% 50), 686798943174000640]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 52), 704817739729993728, (certNat% 53), 1153944050420678656, (certNat% 54), 432416001691222016]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c9 c1
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c10 c0
  c11
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record038

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "dc2f0da2eb2639956358b6c38ce8b8ae2785e0faa9364b9d172539555354b5c34cd2b61d2745d0f5c3c8ce354cb3c2ccb8ac5b0ef0731e2749ca719d1725c3783d0f23c4f8b0d22a89a518560b81e346292a499c1545894558342d0754330ca324c5322c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da4da4db49249249a4d349249a49a492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 47), (facetIndex 55), (facetIndex 59), (facetIndex 68), (facetIndex 70)]))
 (.leaf ([(facetIndex 41), (facetIndex 44), (facetIndex 66), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 39), (facetIndex 43), (facetIndex 51), (facetIndex 52), (facetIndex 54)]))
 (.leaf ([(facetIndex 35), (facetIndex 42), (facetIndex 75)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 32), (facetIndex 38), (facetIndex 64), (facetIndex 80)]))
 (.leaf ([(facetIndex 37), (facetIndex 46), (facetIndex 48), (facetIndex 56), (facetIndex 69), (facetIndex 72), (facetIndex 84)])))
 (.branch 7
 (.leaf ([(facetIndex 33), (facetIndex 36), (facetIndex 50), (facetIndex 71), (facetIndex 83)]))
 (.branch 8
 (.leaf ([(facetIndex 34), (facetIndex 58), (facetIndex 61)]))
 (.leaf ([(facetIndex 40), (facetIndex 57), (facetIndex 63), (facetIndex 73), (facetIndex 74), (facetIndex 79)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "56004800038856050110480700785020226050501231824563764z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 49), (facetIndex 53)]))
 (.leaf ([(facetIndex 77), (facetIndex 82)])))
 (.branch 3
 (.leaf ([(facetIndex 60), (facetIndex 62), (facetIndex 65)]))
 (.branch 4
 (.leaf ([(facetIndex 76), (facetIndex 78), (facetIndex 81)]))
 (.leaf ([(facetIndex 85), (facetIndex 86)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1200580cb000000010082z2d;"⟩
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
def grouped3_0022 : List Nat := [2, 3, 4]
def grouped3_0023 : List Nat := [3]
def grouped3_0024 : List Nat := [3, 4]
def grouped3_0025 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009_matrix_checked

def leafCount : Nat := 2
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 12), (facetIndex 20), (facetIndex 29), (facetIndex 31), (facetIndex 52), (facetIndex 53), (facetIndex 58), (facetIndex 63), (facetIndex 67), (facetIndex 70), (facetIndex 71), (facetIndex 80), (facetIndex 82), (facetIndex 84)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 10), (facetIndex 20), (facetIndex 29), (facetIndex 31), (facetIndex 53), (facetIndex 54), (facetIndex 58), (facetIndex 63), (facetIndex 67), (facetIndex 70), (facetIndex 71), (facetIndex 80), (facetIndex 82), (facetIndex 84)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 1
 (.leaf (leaf0000))
 (.leaf (leaf0001)))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record009" 103

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record009" "{\"ridges\":[[2,37],[4,259],[9,131],[10,35],[10,131],[12,67],[17,545],[17,548],[19,772],[21,161],[22,521],[22,545],[29,162],[31,524],[31,548],[36,37],[37,7],[38,259],[39,37],[44,769],[45,35],[46,67],[49,521],[52,35],[52,67],[53,35],[53,259],[53,545],[53,802],[54,131],[54,259],[58,521],[58,524],[60,204],[61,769],[61,772],[62,180],[63,145],[65,228],[66,769],[66,772],[67,772],[68,161],[70,161],[70,521],[71,42],[74,162],[76,204],[77,524],[78,180],[80,322],[81,228],[82,548],[82,802],[83,162],[85,180],[86,204]],\"owners\":[[37,7,[0,2,3,4,35,42,44],[1,33,40,43]],[2,37,[14,17,55,59,62,65,66],[36,39,40,41]],[36,37,[14,17,59,65,66],[2,39,40,41,55,62]],[39,37,[14,17,55,59,62,66],[2,36,40,41,65]],[71,42,[6,29,47],[25,45,75,83]],[63,145,[9,20,50,68],[23,37,57,62]],[21,161,[10,40,50,52,62,65],[59,68,70]],[68,161,[10,40,52,65],[21,50,59,62,70]],[70,161,[10,40,50,52,62,65],[21,59,68]],[29,162,[10,40,50,52,78,81],[74,83]],[74,162,[10,50,52],[29,40,78,81,83]],[83,162,[10,40,52,81],[29,50,74,78]],[80,322,[12,54],[27,51]],[58,521,[22,47,49,70],[15,35,61]],[58,524,[31,75,77],[15,35,61]],[17,545,[22,47,53,70],[42,66]],[44,769,[],[19,49,53,61,66,67]],[61,769,[53],[19,44,49,66,67]],[66,769,[49],[19,44,53,61,67]],[19,772,[77,82],[44,61,66,67]],[61,772,[82],[19,44,66,67,77]],[66,772,[77],[19,44,61,67,82]],[67,772,[77,82],[19,44,61,66]],[53,802,[82],[]],[82,802,[53],[]],[60,204,[76,86],[]],[76,204,[60,86],[]],[86,204,[60,76],[]],[62,180,[78,85],[]],[78,180,[62,85],[]],[85,180,[62,78],[]],[65,228,[81],[]],[81,228,[65],[]]],\"edges\":[[36,[10,21,29,40,50,52,59,62,65,68,70,74,78,81,83,85]],[38,[17,22,31,42,47,53,66,70,75,82]],[44,[19,44,49,53,61,66,67,77,82]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-20,-19],[-26,-19],[-32,-14],[-34,-19],[-34,-20],[-34,-27],[-34,-32],[-37,-6],[-37,-33],[-37,-35],[-38,-20],[-38,-25],[-38,-26],[-38,-27],[-38,-32],[-38,-34],[-39,-3],[-39,-31],[-39,-33],[-39,-35],[-39,-37],[-43,-1],[-43,-9],[-43,-17],[-43,-18],[-43,-20],[-43,-40],[-43,-41],[-43,-42],[-44,-43],[-46,-20],[-51,-43],[-51,-46],[-52,-4],[-52,-19],[-52,-23],[-52,-46],[-52,-49],[-54,-48],[-55,-5],[-55,-14],[-55,-53],[-56,-53],[-58,-56],[-59,-56],[-60,-34],[-60,-38],[-62,-38],[-65,-3],[-65,-28],[-65,-36],[-65,-57],[-65,-64],[-68,-53],[-68,-58],[-68,-59],[-69,-68],[-22,1,2,3,4,20,27,29],[-7,-30,-38],[-30,-37,-38],[-2,9,10,40,44,47,50,51],[-21,9,10,44,50,51],[-24,9,10,40,44,47,51],[-8,-31,-37],[-4,-38,-39],[-23,-38,-39],[-56,5,15,32],[-6,-7,-39],[-48,6,12,35,53],[-13,7,25,35,37,47,50],[-53,7,25,37,50],[-55,7,25,35,37,47,50],[-15,7,25,35,37,63,66],[-59,7,35,37],[-68,7,25,37,66],[-65,8,39],[-43,14,32,34,55],[-14,-34,-43],[-34,-43,-55],[-43,16,60,62],[-16,-43,-62],[-10,14,32,38,55],[-10,-14,-38],[-10,-16,-67],[-29],[-46,38],[-51,34],[-11,62,67],[-46,67],[-51,62],[-52,62,67],[-38,67],[-67,38],[-45,61,71],[-61,45,71],[-71,45,61],[-47,63,70],[-63,47,70],[-70,47,63],[-50,66],[-66,50],[-72,30,32,40,44,53,55],[-73,26,29,51,52],[-74,24,28,36,37,39],[-75,20,27,60],[-76,17,23,49,65],[-77,22,31,33,41,54,57,69],[-78,18,21,35,56,68],[-79,19,43,46],[-80,25,42,48,58,59,64],[-81,72],[-81,73],[-82,74,75],[-83,75],[-84,81,83],[-84,82],[-85,83],[-86,76],[-86,77],[-87,79],[-87,80],[-88,78],[-88,87],[-89,86],[-89,88],[-90,84],[-90,85,89],[90],[-91,34,38],[-34,91],[-38,91],[-92,62,67],[-62,92],[-67,92],[-93,45,47,50],[-45,93],[-47,93],[-50,93],[-94,61,63,66],[-61,94],[-63,94],[-66,94],[-95,70,71],[-70,95],[-71,95],[-92,96],[-97,91],[-91,96],[-97,92],[-98,94,95],[-95,98],[-94,98],[-94,-95,99],[-100,93,98],[-99,101],[-93,-98,101],[-102,97,100],[-96,-101,103],[102],[-103],[-8,-12,-15,-16,-37,-38,-43,-48,-52,-55,-56,-65,-67,-69],[-7,-12,-15,-16,-38,-39,-43,-48,-52,-55,-56,-65,-67,-69],[7,13,15,25,35,37,44,47,50,53,55,59,63,66,68,70],[10,14,16,27,32,38,51,55,60,67],[11,29,34,38,46,51,52,62,67]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":35,\"b\":34},{\"tag\":\"incompatible\",\"a\":41,\"b\":34},{\"tag\":\"incompatible\",\"a\":47,\"b\":22},{\"tag\":\"incompatible\",\"a\":49,\"b\":34},{\"tag\":\"incompatible\",\"a\":49,\"b\":35},{\"tag\":\"incompatible\",\"a\":49,\"b\":42},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":52,\"b\":9},{\"tag\":\"incompatible\",\"a\":52,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":53,\"b\":35},{\"tag\":\"incompatible\",\"a\":53,\"b\":40},{\"tag\":\"incompatible\",\"a\":53,\"b\":41},{\"tag\":\"incompatible\",\"a\":53,\"b\":42},{\"tag\":\"incompatible\",\"a\":53,\"b\":47},{\"tag\":\"incompatible\",\"a\":53,\"b\":49},{\"tag\":\"incompatible\",\"a\":54,\"b\":3},{\"tag\":\"incompatible\",\"a\":54,\"b\":46},{\"tag\":\"incompatible\",\"a\":54,\"b\":48},{\"tag\":\"incompatible\",\"a\":54,\"b\":50},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":58,\"b\":0},{\"tag\":\"incompatible\",\"a\":58,\"b\":14},{\"tag\":\"incompatible\",\"a\":58,\"b\":32},{\"tag\":\"incompatible\",\"a\":58,\"b\":33},{\"tag\":\"incompatible\",\"a\":58,\"b\":35},{\"tag\":\"incompatible\",\"a\":58,\"b\":55},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":35},{\"tag\":\"incompatible\",\"a\":66,\"b\":58},{\"tag\":\"incompatible\",\"a\":66,\"b\":61},{\"tag\":\"incompatible\",\"a\":67,\"b\":4},{\"tag\":\"incompatible\",\"a\":67,\"b\":34},{\"tag\":\"incompatible\",\"a\":67,\"b\":38},{\"tag\":\"incompatible\",\"a\":67,\"b\":61},{\"tag\":\"incompatible\",\"a\":67,\"b\":64},{\"tag\":\"incompatible\",\"a\":69,\"b\":63},{\"tag\":\"incompatible\",\"a\":70,\"b\":6},{\"tag\":\"incompatible\",\"a\":70,\"b\":22},{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"incompatible\",\"a\":71,\"b\":68},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":74,\"b\":71},{\"tag\":\"incompatible\",\"a\":75,\"b\":49},{\"tag\":\"incompatible\",\"a\":75,\"b\":53},{\"tag\":\"incompatible\",\"a\":77,\"b\":53},{\"tag\":\"incompatible\",\"a\":80,\"b\":3},{\"tag\":\"incompatible\",\"a\":80,\"b\":43},{\"tag\":\"incompatible\",\"a\":80,\"b\":51},{\"tag\":\"incompatible\",\"a\":80,\"b\":72},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"incompatible\",\"a\":83,\"b\":68},{\"tag\":\"incompatible\",\"a\":83,\"b\":73},{\"tag\":\"incompatible\",\"a\":83,\"b\":74},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"mate\",\"ridge\":7,\"a\":37,\"owners\":[0,2,3,4,35,42,44]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[10,45,53]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[45,52,53]},{\"tag\":\"mate\",\"ridge\":37,\"a\":2,\"owners\":[14,17,55,59,62,65,66]},{\"tag\":\"mate\",\"ridge\":37,\"a\":36,\"owners\":[14,17,59,65,66]},{\"tag\":\"mate\",\"ridge\":37,\"a\":39,\"owners\":[14,17,55,59,62,66]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[12,46,52]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[4,53,54]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[38,53,54]},{\"tag\":\"mate\",\"ridge\":42,\"a\":71,\"owners\":[6,29,47]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[9,10,54]},{\"tag\":\"mate\",\"ridge\":145,\"a\":63,\"owners\":[9,20,50,68]},{\"tag\":\"mate\",\"ridge\":161,\"a\":21,\"owners\":[10,40,50,52,62,65]},{\"tag\":\"mate\",\"ridge\":161,\"a\":68,\"owners\":[10,40,52,65]},{\"tag\":\"mate\",\"ridge\":161,\"a\":70,\"owners\":[10,40,50,52,62,65]},{\"tag\":\"mate\",\"ridge\":162,\"a\":29,\"owners\":[10,40,50,52,78,81]},{\"tag\":\"mate\",\"ridge\":162,\"a\":74,\"owners\":[10,50,52]},{\"tag\":\"mate\",\"ridge\":162,\"a\":83,\"owners\":[10,40,52,81]},{\"tag\":\"mate\",\"ridge\":322,\"a\":80,\"owners\":[12,54]},{\"tag\":\"mate\",\"ridge\":521,\"a\":58,\"owners\":[22,47,49,70]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[22,49,58]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[49,58,70]},{\"tag\":\"mate\",\"ridge\":524,\"a\":58,\"owners\":[31,75,77]},{\"tag\":\"three\",\"ridge\":524,\"vertices\":[31,58,77]},{\"tag\":\"mate\",\"ridge\":545,\"a\":17,\"owners\":[22,47,53,70]},{\"tag\":\"three\",\"ridge\":545,\"vertices\":[17,22,53]},{\"tag\":\"three\",\"ridge\":548,\"vertices\":[17,31,82]},{\"tag\":\"mate\",\"ridge\":769,\"a\":44,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":769,\"a\":61,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":769,\"a\":66,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":772,\"a\":19,\"owners\":[77,82]},{\"tag\":\"mate\",\"ridge\":772,\"a\":61,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":772,\"a\":66,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":772,\"a\":67,\"owners\":[77,82]},{\"tag\":\"mate\",\"ridge\":802,\"a\":53,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":802,\"a\":82,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":204,\"a\":60,\"owners\":[76,86]},{\"tag\":\"mate\",\"ridge\":204,\"a\":76,\"owners\":[60,86]},{\"tag\":\"mate\",\"ridge\":204,\"a\":86,\"owners\":[60,76]},{\"tag\":\"mate\",\"ridge\":180,\"a\":62,\"owners\":[78,85]},{\"tag\":\"mate\",\"ridge\":180,\"a\":78,\"owners\":[62,85]},{\"tag\":\"mate\",\"ridge\":180,\"a\":85,\"owners\":[62,78]},{\"tag\":\"mate\",\"ridge\":228,\"a\":65,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":228,\"a\":81,\"owners\":[65]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[45,47,55,59,68,70],\"full_literals\":[-72,30,32,40,44,53,55]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[41,44,66,67],\"full_literals\":[-73,26,29,51,52]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[39,43,51,52,54],\"full_literals\":[-74,24,28,36,37,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[35,42,75],\"full_literals\":[-75,20,27,60]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[32,38,64,80],\"full_literals\":[-76,17,23,49,65]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[37,46,48,56,69,72,84],\"full_literals\":[-77,22,31,33,41,54,57,69]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[33,36,50,71,83],\"full_literals\":[-78,18,21,35,56,68]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[34,58,61],\"full_literals\":[-79,19,43,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[40,57,63,73,74,79],\"full_literals\":[-80,25,42,48,58,59,64]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-81,72,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-81,false,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-82,74,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-83,false,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-84,81,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-84,false,82],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-85,false,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,76,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-86,false,77],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-87,79,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-87,false,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-88,78,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-88,false,87],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-89,86,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-89,false,88],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-90,84,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-90,85,89],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[49,53],\"full_literals\":[-91,34,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-34,91]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":53,\"full_literals\":[-38,91]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[77,82],\"full_literals\":[-92,62,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-62,92]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-67,92]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[60,62,65],\"full_literals\":[-93,45,47,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":60,\"full_literals\":[-45,93]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":62,\"full_literals\":[-47,93]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-50,93]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[76,78,81],\"full_literals\":[-94,61,63,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-61,94]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":78,\"full_literals\":[-63,94]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":81,\"full_literals\":[-66,94]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[85,86],\"full_literals\":[-95,70,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":85,\"full_literals\":[-70,95]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":86,\"full_literals\":[-71,95]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-92,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-97,91,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-91,false,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-97,false,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-98,94,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-95,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-94,false,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-94,-95,99],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-100,93,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-99,101],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-93,-98,101],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-102,97,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-96,-101,103],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[12,20,29,31,52,53,58,63,67,70,71,80,82,84]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[10,20,29,31,53,54,58,63,67,70,71,80,82,84]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[10,21,29,40,50,52,59,62,65,68,70,74,78,81,83,85]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[17,22,31,42,47,53,66,70,75,82]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[19,44,49,53,61,66,67,77,82]}]}"
  "166 -73 26 51 52 0 85 103 0\n167 84 0 128 126 0\n168 82 0 167 116 0\n169 11 34 38 46 51 52 62 67 0 85 165 0\n170 96 0 146 148 133 134 130 131 90 89 88 91 169 0\n171 -101 0 170 160 158 0\n172 -99 0 171 155 0\n173 -95 93 0 172 137 136 153 140 141 96 99 143 0\n174 -98 0 171 156 136 137 138 101 173 144 145 150 98 95 139 0\n175 -95 0 174 151 0\n176 -94 0 174 152 0\n177 -70 0 175 144 0\n178 -71 0 175 145 0\n179 -61 0 176 140 0\n180 -63 0 176 141 0\n181 -66 0 176 142 0\n182 -45 0 178 179 94 0\n183 -47 0 180 177 97 0\n184 -50 0 181 100 0\n185 -93 0 183 182 184 135 0\n186 -100 0 185 174 154 0\n187 97 0 186 159 157 0\n188 91 0 187 147 0\n189 92 0 187 149 0\n190 -20 -79 0 1 26 31 109 0\n191 -27 0 188 6 14 129 0\n192 -60 0 188 46 47 129 0\n193 7 -39 25 55 44 0 177 181 180 184 183 21 20 74 70 73 71 75 163 0\n194 -39 -14 -43 -88 0 192 191 167 188 184 32 30 23 78 129 83 62 12 41 3 27 25 123 120 190 105 114 115 111 122 20 193 59 102 43 54 108 0\n195 -14 -43 -89 0 168 192 191 167 188 184 183 32 30 27 25 24 23 125 123 120 190 105 114 115 112 111 113 122 124 118 3 41 78 129 13 83 166 62 63 36 38 106 50 51 194 104 10 60 102 43 54 108 0\n196 -56 -37 -8 -38 -43 -89 0 183 184 192 167 191 85 10 9 8 64 125 123 120 190 105 114 115 112 32 13 166 34 30 27 23 48 80 92 84 61 22 24 124 118 36 38 106 49 58 53 52 195 15 16 77 42 40 12 29 28 121 119 44 45 67 110 39 69 107 161 0\n197 -38 39 -43 -89 0 168 167 192 184 183 85 191 32 30 29 28 27 25 24 23 22 125 123 120 190 105 114 115 112 113 121 122 124 119 118 12 13 48 92 166 80 84 34 36 38 62 61 63 106 49 50 51 52 53 76 58 104 64 9 10 196 108 55 56 57 110 107 39 0\n198 38 14 -43 0 188 189 192 191 32 93 129 132 7 79 81 82 164 0\n199 -68 -43 -89 0 183 184 85 192 191 167 24 124 118 195 198 197 66 125 123 120 190 105 114 115 112 32 13 166 38 106 53 52 65 30 27 23 48 80 92 84 61 22 17 58 19 18 12 29 28 121 119 55 56 57 110 107 39 0\n200 -43 -89 0 167 192 85 191 184 183 125 123 120 190 105 114 115 112 121 122 124 119 118 22 23 24 25 27 28 29 30 32 195 198 12 13 15 16 48 92 197 166 77 80 84 17 18 19 20 21 65 66 38 40 42 62 61 58 72 106 68 52 53 199 108 44 45 67 110 39 69 107 162 0\n201 -19 -73 0 2 4 35 87 166 0\n202 -89 0 191 192 167 125 123 120 190 105 114 115 112 200 201 109 33 37 86 166 13 0\n203 85 0 202 128 127 0\n204 83 0 203 117 0\n205 75 0 204 114 0\n206 20 0 205 192 191 105 0\n207 -34 0 206 5 0\n208 -38 0 206 11 0\n209 0 208 207 188 129 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009.l) :=
(.branch 1
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009.g)) :=
(.branch 1
 (.leaf ([]))
 (.leaf ([])))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record014
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "dc36a3a71b26558d61db0e33a2e2b89e178d98e5c5c955535475c34cd8b4ad2745dd0dc3c8d5334e331cf0ba2ccb2ae1b26c5bc1d8789d2729c6745c9783d0f13c3c8a83a518c6158362382e07a290e545314550d48d0b41dc0d4330e2314c3382c8b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da4d24d249349a49a492492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 72)]))
 (.leaf ([(facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 86)]))
 (.branch 4
 (.leaf ([(facetIndex 65), (facetIndex 69)]))
 (.leaf ([(facetIndex 78), (facetIndex 82)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "88100100000018018z30;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [2]
def grouped3_0005 : List Nat := [2, 3, 4]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record014" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record014" 47

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record014" "{\"ridges\":[[11,67],[11,82],[13,67],[13,193],[13,194],[14,67],[14,321],[14,322],[15,769],[15,770],[20,81],[20,84],[21,69],[21,193],[22,69],[22,321],[22,324],[29,70],[29,82],[29,84],[30,70],[30,194],[31,70],[31,322],[31,324],[45,769],[46,67],[46,82],[50,67],[50,193],[50,194],[52,769],[52,770],[53,67],[53,81],[53,82],[56,82],[56,321],[56,322],[57,769],[57,770],[59,67],[59,321],[59,322],[59,769],[59,770],[60,81],[60,84],[64,193],[64,196],[65,780],[66,69],[66,81],[66,84],[67,81],[68,81],[68,84],[68,321],[68,324],[69,804],[70,193],[70,321],[70,324],[73,70],[73,82],[77,70],[77,194],[78,780],[79,70],[79,82],[79,84],[80,82],[81,82],[81,322],[81,324],[82,804],[83,194],[83,322],[83,324],[86,216]],\"owners\":[[20,81,[11,46,53,55,56,72],[60,66,67,68]],[53,81,[20,60,67,68,72],[11,46,55,56,66]],[60,81,[11,53,55,56],[20,46,66,67,68,72]],[66,81,[11,46,55,56,72],[20,53,60,67,68]],[67,81,[11,46,53,56],[20,55,60,66,68,72]],[68,81,[11,46,53,55,72],[20,56,60,66,67]],[11,82,[29,73,79,80,81,85],[46,53,55,56]],[29,82,[11,46,53,55,56,85],[73,79,80,81]],[46,82,[29,79,80,81],[11,53,55,56,73,85]],[53,82,[29,73,80,81,85],[11,46,55,56,79]],[56,82,[29,73,79,80,85],[11,46,53,55,81]],[73,82,[11,53,55,56],[29,46,79,80,81,85]],[79,82,[11,46,55,56,85],[29,53,73,80,81]],[80,82,[11,46,53,56],[29,55,73,79,81,85]],[81,82,[11,46,53,55,85],[29,56,73,79,80]],[13,193,[21,64,67,70,72],[50,55,58]],[21,193,[13,50,55,58,72],[64,67,70]],[50,193,[21,67,70],[13,55,58,64,72]],[64,193,[13,55,58],[21,50,67,70,72]],[70,193,[13,50,55,72],[21,58,64,67]],[13,194,[30,77,80,83,85],[50,55,58]],[30,194,[13,50,55,58,85],[77,80,83]],[50,194,[30,80,83],[13,55,58,77,85]],[77,194,[13,55,58],[30,50,80,83,85]],[83,194,[13,50,55,85],[30,58,77,80]],[14,321,[22,68,70],[56,58,59]],[22,321,[14,56,58,59],[68,70]],[56,321,[22,70],[14,58,59,68]],[59,321,[22,68,70],[14,56,58]],[68,321,[14,58,59],[22,56,70]],[70,321,[14,56,59],[22,58,68]],[14,322,[31,81,83],[56,58,59]],[31,322,[14,56,58,59],[81,83]],[56,322,[31,83],[14,58,59,81]],[59,322,[31,81,83],[14,56,58]],[81,322,[14,58,59],[31,56,83]],[83,322,[14,56,59],[31,58,81]],[15,769,[65,69],[45,52,57,59]],[45,769,[],[15,52,57,59,65,69]],[52,769,[69],[15,45,57,59,65]],[57,769,[65],[15,45,52,59,69]],[59,769,[65,69],[15,45,52,57]],[15,770,[78,82],[45,52,57,59]],[52,770,[82],[15,45,57,59,78]],[57,770,[78],[15,45,52,59,82]],[59,770,[78,82],[15,45,52,57]],[20,84,[29,73,79,80,81,86],[60,66,67,68]],[29,84,[20,60,66,67,68,86],[73,79,80,81]],[60,84,[29,79,80,81],[20,66,67,68,73,86]],[66,84,[29,73,80,81,86],[20,60,67,68,79]],[68,84,[29,73,79,80,86],[20,60,66,67,81]],[79,84,[20,60,67,68,86],[29,66,73,80,81]],[64,196,[30,80,83],[21,67,70,77,86]],[22,324,[31,81,83],[68,70]],[31,324,[22,68,70],[81,83]],[68,324,[31,83],[22,70,81]],[70,324,[31,81],[22,68,83]],[81,324,[22,70],[31,68,83]],[83,324,[22,68],[31,70,81]],[65,780,[78],[]],[78,780,[65],[]],[69,804,[82],[]],[82,804,[69],[]],[86,216,[72,85],[]]],\"edges\":[[31,[11,20,29,46,53,55,56,60,66,67,68,72,73,79,80,81,85,86]],[39,[13,21,30,50,55,58,64,67,70,72,77,80,83,85,86]],[40,[14,22,31,56,58,59,68,70,81,83]],[44,[15,45,52,57,59,65,69,78,82]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record014" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record014\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-12],[-16,-3],[-16,-13],[-17,-2],[-17,-13],[-17,-15],[-17,-16],[-19,-1],[-19,-12],[-19,-15],[-19,-16],[-19,-17],[-20,-16],[-21,-13],[-25,-7],[-26,-6],[-26,-22],[-26,-25],[-28,-5],[-28,-24],[-28,-25],[-28,-26],[-30,-13],[-31,-21],[-31,-30],[-34,-10],[-34,-25],[-35,-9],[-35,-31],[-35,-34],[-37,-8],[-37,-10],[-37,-30],[-37,-33],[-37,-34],[-37,-35],[-1,-2,-3],[-1,-2,-20],[-1,-3,-13],[-1,-13,-20],[-2,-3,-12],[-2,-3,-15],[-2,-12,-20],[-2,-15,-20],[-3,-13,-15],[-13,-15,-20],[-6,-7,-24],[-8,-9,-10],[-8,-10,-31],[-9,-10,-30],[-9,-10,-33],[-10,-31,-33],[-5,1,12,15,16,17,29],[-15,5,21,25,26,29],[-21,1,15,16,17],[-24,1,12,16,17,29],[-25,1,12,15,17],[-26,1,12,15,16,29],[-1,8,30,33,34,35,38],[-8,1,12,15,16,17,38],[-12,8,33,34,35],[-15,8,30,34,35,38],[-17,8,30,33,34,38],[-30,1,15,16,17],[-33,1,12,16,17,38],[-34,1,12,15,17],[-35,1,12,15,16,38],[-2,6,22,25,28,29],[-6,2,13,16,19,29],[-13,6,25,28],[-22,2,16,19],[-28,2,13,16,29],[-2,9,31,34,37,38],[-9,2,13,16,19,38],[-13,9,34,37],[-31,2,16,19],[-37,2,13,16,38],[-3,7,26,28],[-7,3,17,19,20],[-17,7,28],[-20,7,26,28],[-26,3,19,20],[-28,3,17,20],[-3,10,35,37],[-10,3,17,19,20],[-17,10,37],[-20,10,35,37],[-35,3,19,20],[-37,3,17,20],[-4,23,27],[-11],[-14,27],[-18,23],[-20,23,27],[-4,32,36],[-14,36],[-18,32],[-20,32,36],[-5,8,30,33,34,35,39],[-8,5,21,24,25,26,39],[-21,8,33,34,35],[-24,8,30,34,35,39],[-26,8,30,33,34,39],[-33,5,21,25,26,39],[-22,9,34,37],[-7,10,35,37],[-10,7,26,28],[-26,10,37],[-28,10,35],[-35,7,28],[-37,7,26],[-23,32],[-32,23],[-27,36],[-36,27],[-39,29,38],[-29,40],[-38,41],[-23,42],[-27,42],[-32,43],[-36,43],[-41,44],[-40,44],[-42,-43,45],[-45,46],[-44,-46,47],[-47],[1,5,8,12,15,16,17,21,24,25,26,29,30,33,34,35,38,39],[2,6,9,13,16,19,22,25,28,29,31,34,37,38,39],[3,7,10,17,19,20,26,28,35,37],[4,11,14,18,20,23,27,32,36]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":55,\"b\":14},{\"tag\":\"incompatible\",\"a\":55,\"b\":50},{\"tag\":\"incompatible\",\"a\":56,\"b\":13},{\"tag\":\"incompatible\",\"a\":56,\"b\":50},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":58,\"b\":11},{\"tag\":\"incompatible\",\"a\":58,\"b\":46},{\"tag\":\"incompatible\",\"a\":58,\"b\":53},{\"tag\":\"incompatible\",\"a\":58,\"b\":55},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":60,\"b\":50},{\"tag\":\"incompatible\",\"a\":67,\"b\":22},{\"tag\":\"incompatible\",\"a\":68,\"b\":21},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":20},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"incompatible\",\"a\":73,\"b\":50},{\"tag\":\"incompatible\",\"a\":77,\"b\":60},{\"tag\":\"incompatible\",\"a\":77,\"b\":73},{\"tag\":\"incompatible\",\"a\":80,\"b\":31},{\"tag\":\"incompatible\",\"a\":80,\"b\":67},{\"tag\":\"incompatible\",\"a\":81,\"b\":30},{\"tag\":\"incompatible\",\"a\":81,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":83,\"b\":29},{\"tag\":\"incompatible\",\"a\":83,\"b\":31},{\"tag\":\"incompatible\",\"a\":83,\"b\":73},{\"tag\":\"incompatible\",\"a\":83,\"b\":79},{\"tag\":\"incompatible\",\"a\":83,\"b\":80},{\"tag\":\"incompatible\",\"a\":83,\"b\":81},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[11,13,14]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[11,13,59]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[11,14,50]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[11,50,59]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[13,14,46]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[13,14,53]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[13,46,59]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[13,53,59]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[14,50,53]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[50,53,59]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[21,22,66]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[29,30,31]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[29,31,77]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[30,31,73]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[30,31,79]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[31,77,79]},{\"tag\":\"mate\",\"ridge\":81,\"a\":20,\"owners\":[11,46,53,55,56,72]},{\"tag\":\"mate\",\"ridge\":81,\"a\":53,\"owners\":[20,60,67,68,72]},{\"tag\":\"mate\",\"ridge\":81,\"a\":60,\"owners\":[11,53,55,56]},{\"tag\":\"mate\",\"ridge\":81,\"a\":66,\"owners\":[11,46,55,56,72]},{\"tag\":\"mate\",\"ridge\":81,\"a\":67,\"owners\":[11,46,53,56]},{\"tag\":\"mate\",\"ridge\":81,\"a\":68,\"owners\":[11,46,53,55,72]},{\"tag\":\"mate\",\"ridge\":82,\"a\":11,\"owners\":[29,73,79,80,81,85]},{\"tag\":\"mate\",\"ridge\":82,\"a\":29,\"owners\":[11,46,53,55,56,85]},{\"tag\":\"mate\",\"ridge\":82,\"a\":46,\"owners\":[29,79,80,81]},{\"tag\":\"mate\",\"ridge\":82,\"a\":53,\"owners\":[29,73,80,81,85]},{\"tag\":\"mate\",\"ridge\":82,\"a\":56,\"owners\":[29,73,79,80,85]},{\"tag\":\"mate\",\"ridge\":82,\"a\":73,\"owners\":[11,53,55,56]},{\"tag\":\"mate\",\"ridge\":82,\"a\":79,\"owners\":[11,46,55,56,85]},{\"tag\":\"mate\",\"ridge\":82,\"a\":80,\"owners\":[11,46,53,56]},{\"tag\":\"mate\",\"ridge\":82,\"a\":81,\"owners\":[11,46,53,55,85]},{\"tag\":\"mate\",\"ridge\":193,\"a\":13,\"owners\":[21,64,67,70,72]},{\"tag\":\"mate\",\"ridge\":193,\"a\":21,\"owners\":[13,50,55,58,72]},{\"tag\":\"mate\",\"ridge\":193,\"a\":50,\"owners\":[21,67,70]},{\"tag\":\"mate\",\"ridge\":193,\"a\":64,\"owners\":[13,55,58]},{\"tag\":\"mate\",\"ridge\":193,\"a\":70,\"owners\":[13,50,55,72]},{\"tag\":\"mate\",\"ridge\":194,\"a\":13,\"owners\":[30,77,80,83,85]},{\"tag\":\"mate\",\"ridge\":194,\"a\":30,\"owners\":[13,50,55,58,85]},{\"tag\":\"mate\",\"ridge\":194,\"a\":50,\"owners\":[30,80,83]},{\"tag\":\"mate\",\"ridge\":194,\"a\":77,\"owners\":[13,55,58]},{\"tag\":\"mate\",\"ridge\":194,\"a\":83,\"owners\":[13,50,55,85]},{\"tag\":\"mate\",\"ridge\":321,\"a\":14,\"owners\":[22,68,70]},{\"tag\":\"mate\",\"ridge\":321,\"a\":22,\"owners\":[14,56,58,59]},{\"tag\":\"mate\",\"ridge\":321,\"a\":56,\"owners\":[22,70]},{\"tag\":\"mate\",\"ridge\":321,\"a\":59,\"owners\":[22,68,70]},{\"tag\":\"mate\",\"ridge\":321,\"a\":68,\"owners\":[14,58,59]},{\"tag\":\"mate\",\"ridge\":321,\"a\":70,\"owners\":[14,56,59]},{\"tag\":\"mate\",\"ridge\":322,\"a\":14,\"owners\":[31,81,83]},{\"tag\":\"mate\",\"ridge\":322,\"a\":31,\"owners\":[14,56,58,59]},{\"tag\":\"mate\",\"ridge\":322,\"a\":56,\"owners\":[31,83]},{\"tag\":\"mate\",\"ridge\":322,\"a\":59,\"owners\":[31,81,83]},{\"tag\":\"mate\",\"ridge\":322,\"a\":81,\"owners\":[14,58,59]},{\"tag\":\"mate\",\"ridge\":322,\"a\":83,\"owners\":[14,56,59]},{\"tag\":\"mate\",\"ridge\":769,\"a\":15,\"owners\":[65,69]},{\"tag\":\"mate\",\"ridge\":769,\"a\":45,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":769,\"a\":52,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":769,\"a\":57,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":769,\"a\":59,\"owners\":[65,69]},{\"tag\":\"mate\",\"ridge\":770,\"a\":15,\"owners\":[78,82]},{\"tag\":\"mate\",\"ridge\":770,\"a\":52,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":770,\"a\":57,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":770,\"a\":59,\"owners\":[78,82]},{\"tag\":\"mate\",\"ridge\":84,\"a\":20,\"owners\":[29,73,79,80,81,86]},{\"tag\":\"mate\",\"ridge\":84,\"a\":29,\"owners\":[20,60,66,67,68,86]},{\"tag\":\"mate\",\"ridge\":84,\"a\":60,\"owners\":[29,79,80,81]},{\"tag\":\"mate\",\"ridge\":84,\"a\":66,\"owners\":[29,73,80,81,86]},{\"tag\":\"mate\",\"ridge\":84,\"a\":68,\"owners\":[29,73,79,80,86]},{\"tag\":\"mate\",\"ridge\":84,\"a\":79,\"owners\":[20,60,67,68,86]},{\"tag\":\"mate\",\"ridge\":196,\"a\":64,\"owners\":[30,80,83]},{\"tag\":\"mate\",\"ridge\":324,\"a\":22,\"owners\":[31,81,83]},{\"tag\":\"mate\",\"ridge\":324,\"a\":31,\"owners\":[22,68,70]},{\"tag\":\"mate\",\"ridge\":324,\"a\":68,\"owners\":[31,83]},{\"tag\":\"mate\",\"ridge\":324,\"a\":70,\"owners\":[31,81]},{\"tag\":\"mate\",\"ridge\":324,\"a\":81,\"owners\":[22,70]},{\"tag\":\"mate\",\"ridge\":324,\"a\":83,\"owners\":[22,68]},{\"tag\":\"mate\",\"ridge\":780,\"a\":65,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":780,\"a\":78,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":804,\"a\":69,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":804,\"a\":82,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":216,\"a\":86,\"owners\":[72,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":72,\"full_literals\":[-29,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-38,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":65,\"full_literals\":[-23,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":69,\"full_literals\":[-27,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":78,\"full_literals\":[-32,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":82,\"full_literals\":[-36,43]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0003\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0003\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-44,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":31,\"owners\":[11,20,29,46,53,55,56,60,66,67,68,72,73,79,80,81,85,86]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[13,21,30,50,55,58,64,67,70,72,77,80,83,85,86]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[14,22,31,56,58,59,68,70,81,83]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[15,45,52,57,59,65,69,78,82]}]}"
  "133 4 14 18 20 23 27 32 36 0 91 132 0\n134 -19 12 44 0 123 118 124 117 116 8 10 11 12 60 67 53 58 56 57 65 66 55 64 129 0\n135 -20 -13 44 0 23 14 5 3 1 123 118 124 117 116 40 46 60 67 53 58 56 57 65 66 129 0\n136 8 15 24 26 33 35 25 34 -13 44 0 23 14 5 3 1 123 118 124 117 116 59 99 129 0\n137 15 24 26 33 35 25 34 -13 19 44 0 135 14 5 3 1 123 118 124 117 116 136 31 60 100 75 39 19 48 79 131 0\n138 -15 26 35 25 34 -13 19 44 0 135 23 14 5 124 117 123 118 54 62 45 19 31 79 85 131 0\n139 26 33 35 25 34 -13 19 44 0 135 23 5 3 1 123 118 124 117 116 138 137 20 56 102 70 39 31 47 85 131 0\n140 -26 25 -13 0 16 22 70 0\n141 35 25 34 -13 19 44 0 140 135 14 5 3 1 123 118 124 117 116 139 34 65 104 75 39 19 51 79 131 0\n142 -35 34 -13 0 28 36 75 0\n143 34 -13 19 44 0 135 5 142 141 15 18 21 78 107 111 131 0\n144 -13 19 44 0 5 135 143 26 27 30 35 84 106 109 140 131 0\n145 -34 19 0 26 30 35 84 106 109 87 86 108 131 0\n146 7 20 17 28 26 37 35 19 0 78 107 131 0\n147 2 9 16 25 28 37 19 44 0 145 105 144 123 118 124 117 116 76 69 130 0\n148 12 33 8 30 21 1 15 16 25 17 26 35 34 44 0 123 118 124 117 116 53 56 129 0\n149 9 20 17 28 26 37 35 19 44 0 146 79 2 106 15 145 123 118 147 73 42 37 24 25 49 41 52 148 0\n150 20 17 28 26 37 35 19 44 0 145 123 118 146 15 79 106 2 149 48 50 51 101 62 61 59 148 0\n151 15 21 12 33 17 26 35 1 16 25 44 34 0 123 118 60 64 148 0\n152 2 37 16 25 44 19 0 123 118 124 117 116 144 145 71 76 74 69 72 130 0\n153 -10 17 26 35 1 16 25 44 3 19 0 123 118 145 32 85 152 44 55 43 65 151 0\n154 -20 -2 37 10 15 16 38 0 87 43 38 67 0\n155 -35 -2 37 38 34 0 28 29 73 0\n156 37 10 15 16 25 44 19 0 123 118 145 152 86 108 154 155 109 150 0\n157 -37 15 16 25 44 34 0 123 118 124 117 116 31 33 34 36 103 101 61 63 59 151 0\n158 1 26 15 16 25 44 19 0 145 123 118 157 152 155 4 156 55 153 41 65 151 0\n159 -1 -10 -2 19 0 4 37 38 85 0\n160 15 16 25 44 19 0 124 117 145 157 152 156 159 158 16 17 22 68 0\n161 -2 -15 44 19 0 6 42 44 83 88 89 82 150 0\n162 16 25 44 19 0 123 118 124 117 116 144 145 160 161 71 76 74 77 69 72 130 0\n163 -16 44 19 0 2 7 13 83 88 89 82 150 0\n164 16 44 19 0 162 15 18 21 81 80 111 110 150 0\n165 44 19 0 163 164 0\n166 43 -20 0 121 122 98 0\n167 -20 45 0 166 125 119 120 94 0\n168 42 20 0 119 120 90 93 113 92 115 133 0\n169 45 0 167 168 125 121 122 95 97 112 96 114 133 0\n170 46 0 169 126 0\n171 -44 0 170 128 127 0\n172 19 0 171 165 0\n173 -12 0 172 9 0\n174 0 172 173 171 134 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record024
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "32c370bc78b2a6a8bad1b26598e6358b6c3a2e4b8ae8789e0f9e1727296a559364b9d1725594e5354b5c354d3362d4b4ad8749d1743dd0dc3c8da358ce354cb3c2e8b62e2b4acab86d1b26c3bc1e4751cc789d2729c6785c970de0f43c8f0bc1f34856347094a4a9264558342d0770350cc348ca324c5381c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6db4db6db6da4d26db4d36924924924924db49b4d249249249b489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 39), (facetIndex 48), (facetIndex 72), (facetIndex 73)]))
 (.leaf ([(facetIndex 28), (facetIndex 34), (facetIndex 49), (facetIndex 67), (facetIndex 87)])))
 (.branch 3
 (.leaf ([(facetIndex 47), (facetIndex 65), (facetIndex 76)]))
 (.leaf ([(facetIndex 22), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 62)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 35), (facetIndex 51), (facetIndex 53), (facetIndex 54), (facetIndex 55)]))
 (.leaf ([(facetIndex 26), (facetIndex 27), (facetIndex 29), (facetIndex 30), (facetIndex 33), (facetIndex 36), (facetIndex 37)])))
 (.branch 7
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 42), (facetIndex 50), (facetIndex 52)]))
 (.leaf ([(facetIndex 23), (facetIndex 43), (facetIndex 60), (facetIndex 61), (facetIndex 75)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "200000002e000002100ff6db926988400f8002d86ed69b40ecz10;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 63), (facetIndex 64), (facetIndex 74), (facetIndex 77)]))
 (.leaf ([(facetIndex 68), (facetIndex 69), (facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 88), (facetIndex 89), (facetIndex 95)]))
 (.branch 4
 (.leaf ([(facetIndex 25), (facetIndex 70), (facetIndex 71)]))
 (.leaf ([(facetIndex 83), (facetIndex 90), (facetIndex 91)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 24), (facetIndex 66), (facetIndex 97)]))
 (.branch 7
 (.leaf ([(facetIndex 38), (facetIndex 80), (facetIndex 86)]))
 (.leaf ([(facetIndex 79), (facetIndex 82), (facetIndex 96)]))))
 (.branch 9
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 85), (facetIndex 92)]))
 (.branch 10
 (.leaf ([(facetIndex 81), (facetIndex 84), (facetIndex 93)]))
 (.leaf ([(facetIndex 94), (facetIndex 98)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "a572a9844220689479671000000331105z13;88800880600000000000035z18;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
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
def grouped3_0015 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [2, 3, 4]
def grouped3_0020 : List Nat := [3]
def grouped3_0021 : List Nat := [3, 4]
def grouped3_0022 : List Nat := [4]
def grouped3_0023 : List Nat := [5]
def grouped3_0024 : List Nat := [5, 6, 7]
def grouped3_0025 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0026 : List Nat := [6]
def grouped3_0027 : List Nat := [6, 7]
def grouped3_0028 : List Nat := [7]
def grouped3_0029 : List Nat := [8]
def grouped3_0030 : List Nat := [8, 9, 10]
def grouped3_0031 : List Nat := [9]
def grouped3_0032 : List Nat := [9, 10]
def grouped3_0033 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record024" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0032\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record024" 64

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record024" "{\"ridges\":[[9,322],[35,322],[39,152],[42,168],[47,776],[49,322],[51,322],[54,322],[55,322],[64,332],[65,776],[72,152],[73,152],[74,344],[76,776],[77,456],[92,58]],\"owners\":[[9,322,[89,91,95],[35,49,51,54,55]],[35,322,[95],[9,49,51,54,55,89,91]],[49,322,[89,91,95],[9,35,51,54,55]],[51,322,[91],[9,35,49,54,55,89,95]],[54,322,[89,91],[9,35,49,51,55,95]],[55,322,[89,95],[9,35,49,51,54,91]],[39,152,[96,97],[15,58,72,73,80,92]],[72,152,[80,97],[15,39,58,73,92,96]],[73,152,[80,92,96],[15,39,58,72,97]],[42,168,[96],[16,60,72,75,82,92,93]],[47,776,[98],[18,65,76,85,94]],[65,776,[94],[18,47,76,85,98]],[76,776,[85],[18,47,65,94,98]],[92,58,[38,79],[]],[64,332,[],[]],[74,344,[],[]],[77,456,[],[]]],\"edges\":[[40,[9,35,49,51,54,55,64,69,71,74,77,78,89,91,95]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record024" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record024\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-2],[-9,-3],[-11,-9],[-13,-9],[-1,29,30,33],[-4,33],[-10,29,30,33],[-12,30],[-14,29,30],[-15,29,33],[-6,34,35],[-20,27,35],[-21,27,31,34],[-7,34],[-8,36],[-17,32],[-23,28],[-31,5,26],[-16],[-22],[-24],[-37,6,9,20,21],[-38,8,17,23],[-39,2,3,7,11,13],[-40,37],[-41,38],[-42,40],[-42,41],[-43,39],[-44,43],[-45,42],[-45,44],[45],[-18,46],[-25,46],[-29,47],[-33,47],[-19,48],[-30,49],[-35,50],[-5,51],[-27,51],[-26,52],[-34,52],[-28,53],[-32,54],[-36,54],[-46,55],[-49,56],[-48,56],[-56,57],[-47,57],[-57,58],[-55,58],[-52,59],[-51,59],[-59,60],[-50,60],[-54,61],[-61,62],[-53,62],[-60,-62,63],[-58,-63,64],[-64],[1,4,10,12,14,15,16,18,19,22,24,25,29,30,33]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":48,\"b\":31},{\"tag\":\"incompatible\",\"a\":48,\"b\":32},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":48},{\"tag\":\"mate\",\"ridge\":322,\"a\":9,\"owners\":[89,91,95]},{\"tag\":\"mate\",\"ridge\":322,\"a\":35,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":322,\"a\":49,\"owners\":[89,91,95]},{\"tag\":\"mate\",\"ridge\":322,\"a\":51,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":322,\"a\":54,\"owners\":[89,91]},{\"tag\":\"mate\",\"ridge\":322,\"a\":55,\"owners\":[89,95]},{\"tag\":\"mate\",\"ridge\":152,\"a\":39,\"owners\":[96,97]},{\"tag\":\"mate\",\"ridge\":152,\"a\":72,\"owners\":[80,97]},{\"tag\":\"mate\",\"ridge\":152,\"a\":73,\"owners\":[80,92,96]},{\"tag\":\"mate\",\"ridge\":168,\"a\":42,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":776,\"a\":47,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":776,\"a\":65,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":776,\"a\":76,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":58,\"a\":92,\"owners\":[38,79]},{\"tag\":\"mate\",\"ridge\":332,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":344,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":456,\"a\":77,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[39,48,72,73],\"full_literals\":[-37,6,9,20,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[47,65,76],\"full_literals\":[-38,8,17,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[31,32,42,50,52],\"full_literals\":[-39,2,3,7,11,13]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-42,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-42,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-45,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-45,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-18,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-25,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":89,\"full_literals\":[-29,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":95,\"full_literals\":[-33,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-19,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":91,\"full_literals\":[-30,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":97,\"full_literals\":[-35,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":38,\"full_literals\":[-5,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-27,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":79,\"full_literals\":[-26,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":96,\"full_literals\":[-34,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":85,\"full_literals\":[-28,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":94,\"full_literals\":[-32,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":98,\"full_literals\":[-36,54]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0027\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0033\",\"joined_name\":\"grouped3_0032\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-62,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-58,-63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[9,35,49,51,54,55,64,69,71,74,77,78,89,91,95]}]}"
  "66 42 0 33 31 0\n67 44 0 33 32 0\n68 40 0 66 27 0\n69 41 0 66 28 0\n70 43 0 67 30 0\n71 37 0 68 25 0\n72 38 0 69 26 0\n73 39 0 70 29 0\n74 1 4 10 12 14 15 18 19 25 29 30 33 0 19 20 21 65 0\n75 58 0 53 54 51 52 48 49 50 36 37 34 35 39 38 5 7 9 10 6 8 74 0\n76 -63 0 75 64 63 0\n77 60 0 71 73 57 58 55 56 40 43 44 41 42 11 14 18 12 13 22 1 2 3 4 24 0\n78 -62 0 77 76 62 0\n79 -61 0 78 60 0\n80 -53 0 78 61 0\n81 -54 0 79 59 0\n82 -28 0 80 45 0\n83 -32 0 81 46 0\n84 -36 0 81 47 0\n85 -23 0 82 17 0\n86 -17 0 83 16 0\n87 -8 0 84 15 0\n88 0 86 85 72 87 23 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00029.record024
