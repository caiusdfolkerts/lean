module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00082Data
public import GraphInputsRow24Part00082Frames
public import GraphInputsRow24Part00082Leaves
public import GraphInputsRow24Part00082Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6), (certNat% 7)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 10), (certNat% 11), (certNat% 12), 2765958938624]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 268280837177344, (certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 2491617902592, (certNat% 19), (certNat% 20), (certNat% 21), (certNat% 17)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), (certNat% 24), (certNat% 25), (certNat% 26), 2216203124736]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), 263882790666240, (certNat% 24), (certNat% 29), (certNat% 30), 3564822855680]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001
def vertexColumn : Fields := ⟨10, (certNat% 31)⟩
def kindColumn : Fields := ⟨3, (certNat% 32)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 1162210178838298624, 576465150618370048, (certNat% 34), (certNat% 35)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), 585472349873111040, (certNat% 37), (certNat% 38), (certNat% 39), 4222124650659840]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), 1675339061381824512, 8584986923892736, 36028797018963968, (certNat% 42)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), 8584986923892736, (certNat% 45), 342273571680157696]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 41), (certNat% 47), (certNat% 48), (certNat% 49), (certNat% 42)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 51), 1954562238278795264, (certNat% 48), 8584986789675008, (certNat% 38), (certNat% 52)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c9 c2
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006
def vertexColumn : Fields := ⟨10, (certNat% 53)⟩
def kindColumn : Fields := ⟨3, (certNat% 54)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [60187176142372864, (certNat% 55), (certNat% 56), 6629298651489370112, (certNat% 57), (certNat% 58)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), 6052837899185946624, (certNat% 60), 180657061888, 60095457283538944]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 62), 30366760960, (certNat% 63), 1100585369600, (certNat% 64)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), 5764607523168452608, 41658433992130560, (certNat% 66), 1650341183488, 72842645340160]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 68), 5188146770730811392, (certNat% 69), 58846412074385408]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), (certNat% 72), 180657061888, 37176687158362112, 18295873486192640]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), 92633854640128, 55450570411999232, 6629298651489370112, (certNat% 72), (certNat% 74)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), (certNat% 76), (certNat% 66), 18014570308173824, 4785624359895040, 18522046464]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 55), (certNat% 63), 18014578898108416, 90984654307328, 41939771529887744, 4611686036949434368]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "29a598e655936538ce4b8ae8791e785c96a719a64e555535534cd4b4ad876c3a8d63a4d534cd4b32d2b2ad1b26d4731d2729e1745c570de0f43c8f13c2f5911c38a8a8686607961386898651951525195154341da0cc328c6384e0b22c1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "926db6d24da4924d34924db4d2492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 52), (facetIndex 62), (facetIndex 67)]))
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 55), (facetIndex 63), (facetIndex 64)])))
 (.branch 3
 (.leaf ([(facetIndex 34), (facetIndex 69), (facetIndex 78)]))
 (.leaf ([(facetIndex 32), (facetIndex 39), (facetIndex 41), (facetIndex 76)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 45), (facetIndex 47), (facetIndex 51), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 33), (facetIndex 37), (facetIndex 40), (facetIndex 42), (facetIndex 57), (facetIndex 59), (facetIndex 60), (facetIndex 61)])))
 (.branch 7
 (.leaf ([(facetIndex 68), (facetIndex 77)]))
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 35), (facetIndex 36), (facetIndex 38)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "b300001600122da2832080082135d7efeabfcz16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 56), (facetIndex 58)]))
 (.leaf ([(facetIndex 65), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 70), (facetIndex 72)]))
 (.branch 4
 (.leaf ([(facetIndex 46), (facetIndex 48), (facetIndex 49), (facetIndex 50)]))
 (.leaf ([(facetIndex 71), (facetIndex 73), (facetIndex 74), (facetIndex 75)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9228800480000000000db0cz22;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7]
def grouped2_0010 : List Nat := [7]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0014 : List Nat := [1]
def grouped3_0015 : List Nat := [2]
def grouped3_0016 : List Nat := [2, 3, 4]
def grouped3_0017 : List Nat := [3]
def grouped3_0018 : List Nat := [3, 4]
def grouped3_0019 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record004" 33

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record004" "{\"ridges\":[[65,424],[66,456],[71,298],[73,330],[74,306],[75,338]],\"owners\":[[71,298,[46],[]],[73,330,[48],[]],[74,306,[49],[]],[75,338,[50],[]],[65,424,[],[]],[66,456,[],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-10,-4],[-10,-5],[-10,-6],[-10,-7],[-11,-1],[-11,-2],[-11,-3],[-13,-1],[-13,-2],[-13,-3],[-17,-11],[-17,-13],[-18,-4],[-18,-5],[-18,-6],[-18,-7],[-12,4],[-14,5],[-15,6],[-16,7],[-8],[-9],[-19,1,2,3,17],[-20,10,18],[-21,19],[-22,21],[-23,20],[-24,23],[-25,22],[-25,24],[25],[-26,8,9],[-27,11,13],[-28,4,5,6,7],[-4,28],[-5,28],[-6,28],[-7,28],[-29,12,14,15,16],[-30,26],[-31,28,29],[-32,27,31],[-33,30,32],[33]],\"atoms\":[{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":68,\"b\":46},{\"tag\":\"incompatible\",\"a\":68,\"b\":48},{\"tag\":\"incompatible\",\"a\":68,\"b\":49},{\"tag\":\"incompatible\",\"a\":68,\"b\":50},{\"tag\":\"incompatible\",\"a\":70,\"b\":32},{\"tag\":\"incompatible\",\"a\":70,\"b\":39},{\"tag\":\"incompatible\",\"a\":70,\"b\":41},{\"tag\":\"incompatible\",\"a\":72,\"b\":32},{\"tag\":\"incompatible\",\"a\":72,\"b\":39},{\"tag\":\"incompatible\",\"a\":72,\"b\":41},{\"tag\":\"incompatible\",\"a\":76,\"b\":70},{\"tag\":\"incompatible\",\"a\":76,\"b\":72},{\"tag\":\"incompatible\",\"a\":77,\"b\":46},{\"tag\":\"incompatible\",\"a\":77,\"b\":48},{\"tag\":\"incompatible\",\"a\":77,\"b\":49},{\"tag\":\"incompatible\",\"a\":77,\"b\":50},{\"tag\":\"mate\",\"ridge\":298,\"a\":71,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":330,\"a\":73,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":306,\"a\":74,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":338,\"a\":75,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":424,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":456,\"a\":66,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[32,39,41,76],\"full_literals\":[-19,1,2,3,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[68,77],\"full_literals\":[-20,10,18]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-21,false,19],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-22,false,21],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-23,20,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-24,false,23],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-25,22,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-25,false,24],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[65,66],\"full_literals\":[-26,8,9]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[70,72],\"full_literals\":[-27,11,13]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[46,48,49,50],\"full_literals\":[-28,4,5,6,7]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":46,\"full_literals\":[-4,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":48,\"full_literals\":[-5,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":49,\"full_literals\":[-6,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":50,\"full_literals\":[-7,28]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[71,73,74,75],\"full_literals\":[-29,12,14,15,16]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-30,false,26],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-31,28,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-32,27,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-33,30,32],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "45 22 0 31 29 0\n46 24 0 31 30 0\n47 21 0 45 26 0\n48 23 0 46 28 0\n49 19 0 47 25 0\n50 20 0 48 27 0\n51 -26 0 21 22 32 0\n52 -30 0 51 40 0\n53 -33 32 0 52 43 0\n54 32 0 44 53 0\n55 -18 -28 0 13 14 15 16 34 0\n56 -28 0 50 55 24 1 2 3 4 34 0\n57 -4 0 56 35 0\n58 -5 0 56 36 0\n59 -6 0 56 37 0\n60 -7 0 56 38 0\n61 -12 0 57 17 0\n62 -14 0 58 18 0\n63 -15 0 59 19 0\n64 -16 0 60 20 0\n65 -29 0 62 61 63 64 39 0\n66 -31 0 65 56 41 0\n67 27 0 66 54 42 0\n68 -11 0 49 5 6 7 11 23 0\n69 13 0 68 67 33 0\n70 -1 0 69 8 0\n71 -2 0 69 9 0\n72 -3 0 69 10 0\n73 -17 0 69 12 0\n74 0 72 73 49 70 71 23 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "7916cb296a5696639a964da8e538ce4b86e8791e786c95a719565c569565396954d68d534cd4b46d876c3a8d63a4d534ce8b92d4b32d2b1ad1b16e8751cc749c6785d1725c3783d0f23c4f0bd1c38a1a2981e584e15261946525295154341da0cc328c6384e0b12c1b21c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6d36db6d24d24d24d34d34924da493492692492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 60), (facetIndex 62)]))
 (.leaf ([(facetIndex 78), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 58), (facetIndex 70)]))
 (.leaf ([(facetIndex 76), (facetIndex 85)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 39), (facetIndex 44), (facetIndex 49), (facetIndex 50)]))
 (.leaf ([(facetIndex 56), (facetIndex 66), (facetIndex 77)])))
 (.branch 7
 (.leaf ([(facetIndex 75), (facetIndex 79), (facetIndex 82), (facetIndex 83)]))
 (.branch 8
 (.leaf ([(facetIndex 74), (facetIndex 87)]))
 (.leaf ([(facetIndex 84), (facetIndex 86)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "7838660161536700020005000000020500000440000400004z27;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8]
def grouped3_0016 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record005" 56

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record005" "{\"ridges\":[[11,641],[16,292],[21,352],[37,292],[40,642],[44,298],[48,642],[49,306],[51,642],[52,352],[53,641],[54,642],[57,292],[61,292],[64,292],[65,292],[69,352],[71,352],[74,108],[75,298],[79,306],[82,326],[83,338],[84,298],[86,108],[87,452]],\"owners\":[[11,641,[60,62,70],[40,48,51,53,54]],[53,641,[60,62,70],[11,40,48,51,54]],[40,642,[85],[11,48,51,53,54,78,80]],[48,642,[80],[11,40,51,53,54,78,85]],[51,642,[78,85],[11,40,48,53,54,80]],[54,642,[78,80],[11,40,48,51,53,85]],[16,292,[75,79,82,86,87],[37,57,61,64,65]],[37,292,[86,87],[16,57,61,64,65,75,79,82]],[57,292,[79,82,87],[16,37,61,64,65,75,86]],[61,292,[75,82,86,87],[16,37,57,64,65,79]],[64,292,[75,79],[16,37,57,61,65,82,86,87]],[65,292,[75,79,82,86],[16,37,57,61,64,87]],[21,352,[82,84,86,87],[52,64,69,71]],[52,352,[86,87],[21,64,69,71,82,84]],[69,352,[82,87],[21,52,64,71,84,86]],[71,352,[82,84,86],[21,52,64,69,87]],[82,326,[39,77],[]],[44,298,[75,84],[]],[75,298,[44,84],[]],[84,298,[44,75],[]],[49,306,[79],[]],[79,306,[49],[]],[83,338,[50],[]],[74,108,[56,86],[]],[86,108,[56,74],[]],[87,452,[66],[]]],\"edges\":[[37,[16,21,37,44,49,52,57,61,64,65,69,71,75,79,82,84,86,87]],[43,[11,40,48,51,53,54,60,62,70,78,80,85]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,17,19,24],[-13,17,19,24],[-6,35],[-8,31],[-11,29,35],[-14,29,31],[-2,27,30,32,36,37],[-4,36,37],[-16,30,32,37],[-18,27,32,36,37],[-20,27,30],[-21,27,30,32,36],[-3,32,34,36,37],[-12,36,37],[-23,32,37],[-25,32,34,36],[-32,5,28],[-7,27,34],[-27,7,34],[-34,7,27],[-9,30],[-30,9],[-33,10],[-26,15,36],[-36,15,26],[-37,22],[-17,38],[-19,38],[-29,39],[-31,39],[-24,40],[-35,41],[-5,42],[-7,42],[-9,42],[-10,42],[-15,43],[-22,43],[-28,43],[-44,27,30,32,33],[-27,44],[-30,44],[-32,44],[-45,26,37],[-26,45],[-37,45],[-46,34,36],[-34,46],[-36,46],[-39,47],[-38,47],[-41,48],[-40,48],[-48,49],[-47,49],[-43,50],[-42,50],[-51,45,46],[-46,51],[-45,51],[-45,-46,52],[-53,44,51],[-51,53],[-52,54],[-44,53],[-44,-51,54],[-54,55],[-50,-53,55],[-49,-55,56],[-56],[2,3,4,7,9,12,16,18,20,21,23,25,27,30,32,34,36,37],[1,6,8,11,13,14,17,19,24,29,31,35]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":641,\"a\":11,\"owners\":[60,62,70]},{\"tag\":\"mate\",\"ridge\":641,\"a\":53,\"owners\":[60,62,70]},{\"tag\":\"mate\",\"ridge\":642,\"a\":40,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":642,\"a\":48,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":642,\"a\":51,\"owners\":[78,85]},{\"tag\":\"mate\",\"ridge\":642,\"a\":54,\"owners\":[78,80]},{\"tag\":\"mate\",\"ridge\":292,\"a\":16,\"owners\":[75,79,82,86,87]},{\"tag\":\"mate\",\"ridge\":292,\"a\":37,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":292,\"a\":57,\"owners\":[79,82,87]},{\"tag\":\"mate\",\"ridge\":292,\"a\":61,\"owners\":[75,82,86,87]},{\"tag\":\"mate\",\"ridge\":292,\"a\":64,\"owners\":[75,79]},{\"tag\":\"mate\",\"ridge\":292,\"a\":65,\"owners\":[75,79,82,86]},{\"tag\":\"mate\",\"ridge\":352,\"a\":21,\"owners\":[82,84,86,87]},{\"tag\":\"mate\",\"ridge\":352,\"a\":52,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":352,\"a\":69,\"owners\":[82,87]},{\"tag\":\"mate\",\"ridge\":352,\"a\":71,\"owners\":[82,84,86]},{\"tag\":\"mate\",\"ridge\":326,\"a\":82,\"owners\":[39,77]},{\"tag\":\"mate\",\"ridge\":298,\"a\":44,\"owners\":[75,84]},{\"tag\":\"mate\",\"ridge\":298,\"a\":75,\"owners\":[44,84]},{\"tag\":\"mate\",\"ridge\":298,\"a\":84,\"owners\":[44,75]},{\"tag\":\"mate\",\"ridge\":306,\"a\":49,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":306,\"a\":79,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":338,\"a\":83,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":108,\"a\":74,\"owners\":[56,86]},{\"tag\":\"mate\",\"ridge\":108,\"a\":86,\"owners\":[56,74]},{\"tag\":\"mate\",\"ridge\":452,\"a\":87,\"owners\":[66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":60,\"full_literals\":[-17,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":62,\"full_literals\":[-19,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-29,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-31,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":70,\"full_literals\":[-24,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":85,\"full_literals\":[-35,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":39,\"full_literals\":[-5,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":44,\"full_literals\":[-7,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":49,\"full_literals\":[-9,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":50,\"full_literals\":[-10,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":56,\"full_literals\":[-15,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":66,\"full_literals\":[-22,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":77,\"full_literals\":[-28,43]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[75,79,82,83],\"full_literals\":[-44,27,30,32,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-27,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":79,\"full_literals\":[-30,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-32,44]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[74,87],\"full_literals\":[-45,26,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":74,\"full_literals\":[-26,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":87,\"full_literals\":[-37,45]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[84,86],\"full_literals\":[-46,34,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":84,\"full_literals\":[-34,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":86,\"full_literals\":[-36,46]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-46,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,44,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-51,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-53,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-49,-55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[16,21,37,44,49,52,57,61,64,65,69,71,75,79,82,84,86,87]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[11,40,48,51,53,54,60,62,70,78,80,85]}]}"
  "73 49 0 54 55 52 53 50 51 32 31 29 30 27 28 3 5 1 2 6 4 72 0\n74 -55 0 73 70 69 0\n75 -54 0 74 67 0\n76 -52 0 75 64 0\n77 -46 34 15 0 76 47 61 25 45 0\n78 -51 50 0 75 56 38 26 57 34 37 66 41 20 77 49 58 24 44 0\n79 -53 0 74 68 56 57 39 33 34 35 36 17 22 23 78 59 62 48 40 19 0\n80 -51 0 79 63 0\n81 -44 0 79 65 0\n82 -46 0 80 59 0\n83 -45 0 80 60 0\n84 -27 0 81 41 0\n85 -30 0 81 42 0\n86 -32 0 81 43 0\n87 -34 0 82 48 0\n88 -36 0 82 49 0\n89 -37 0 83 46 0\n90 -20 0 84 85 11 0\n91 -7 0 84 87 18 0\n92 -16 0 85 86 89 9 0\n93 -9 0 85 21 0\n94 -23 0 86 89 15 0\n95 -4 0 88 89 8 0\n96 -12 0 88 89 14 0\n97 -2 0 88 85 86 84 89 7 0\n98 -18 0 88 86 84 89 10 0\n99 -21 0 88 85 86 84 12 0\n100 -3 0 88 86 87 89 13 0\n101 -25 0 88 86 87 16 0\n102 0 95 97 88 100 93 96 92 98 90 99 94 101 84 85 86 87 91 89 71 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record010
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2ac78a9a3693a598e655936a38ce2ba1e1783e786d1aa69936539b16a5594e5955554d68d3362d2b45d0f5c368d6338e9334d33a2ccb4ae1b46c9b16c3ba1d4731d2729c6785d170de0f23c4f871522a8560b81e546892a619854558342d0754330d2328d1314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6d36d249b49b6db49a6924924d2492492692492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 61), (facetIndex 68)]))
 (.leaf ([(facetIndex 80), (facetIndex 84)])))
 (.branch 3
 (.leaf ([(facetIndex 64), (facetIndex 65), (facetIndex 73)]))
 (.leaf ([(facetIndex 82), (facetIndex 83), (facetIndex 87)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 50), (facetIndex 69), (facetIndex 72)]))
 (.leaf ([(facetIndex 85), (facetIndex 86)])))
 (.branch 7
 (.leaf ([(facetIndex 39), (facetIndex 59), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 88)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "77696c1fc0014020d92000c00000100000000cz1d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record010" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record010" 57

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record010" "{\"ridges\":[[10,290],[11,194],[20,641],[36,290],[37,194],[39,646],[45,290],[46,194],[47,641],[48,290],[49,194],[51,194],[52,290],[53,290],[54,194],[59,204],[60,641],[60,648],[64,228],[66,676],[67,708],[69,216],[70,641],[71,641],[72,720],[73,480],[78,204],[79,646],[82,228],[83,356],[87,480],[88,676]],\"owners\":[[10,290,[80,83,84,87],[36,45,48,52,53]],[36,290,[84,87],[10,45,48,52,53,80,83]],[45,290,[80,83,87],[10,36,48,52,53,84]],[48,290,[83,87],[10,36,45,52,53,80,84]],[52,290,[80,84],[10,36,45,48,53,83,87]],[53,290,[80,83,84],[10,36,45,48,52,87]],[11,194,[78,82,85,87],[37,46,49,51,54]],[37,194,[85,87],[11,46,49,51,54,78,82]],[46,194,[82,87],[11,37,49,51,54,78,85]],[49,194,[78,82,87],[11,37,46,51,54,85]],[51,194,[78,85],[11,37,46,49,54,82,87]],[54,194,[78,82,85],[11,37,46,49,51,87]],[20,641,[39,50,66,67,72],[47,60,70,71]],[47,641,[66,67,72],[20,39,50,60,70,71]],[60,641,[50,72],[20,39,47,66,67,70,71]],[70,641,[39,66,67],[20,47,50,60,71,72]],[71,641,[39,50,67,72],[20,47,60,66,70]],[60,648,[86],[20,47,70,71,79,88]],[39,646,[79],[]],[79,646,[39],[]],[59,204,[78],[]],[78,204,[59],[]],[64,228,[82],[]],[82,228,[64],[]],[83,356,[65],[]],[66,676,[88],[]],[88,676,[66],[]],[67,708,[],[]],[69,216,[85],[]],[72,720,[],[]],[73,480,[87],[]],[87,480,[73],[]]],\"edges\":[[37,[10,36,45,48,52,53,61,65,68,73,80,83,84,87]],[39,[11,37,46,49,51,54,59,64,67,69,72,73,78,82,85,87]],[43,[20,39,47,50,60,66,67,70,71,72,79,86,88]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record010" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record010\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-36,-12],[-37,-36],[-1,32,34,35,38],[-4,35,38],[-7,32,34,38],[-10,34,38],[-14,32,35],[-15,32,34,35],[-2,30,33,36,38],[-5,36,38],[-8,33,38],[-11,30,33,38],[-13,30,36],[-16,30,33,36],[-3,6,12,22,23,28],[-9,22,23,28],[-18,12,28],[-26,6,22,23],[-27,6,12,23,28],[-18,37],[-6,31],[-31,6],[-17,30],[-30,17],[-20,33],[-33,20],[-34,21],[-22,39],[-39,22],[-23],[-25,36],[-28],[-29,38],[-38,29],[-19,40],[-24,40],[-32,41],[-35,41],[-20,42],[-21,42],[-29,42],[-43,33,34,38],[-33,43],[-34,43],[-38,43],[-12,44],[-37,45],[-46,6,17,22,23],[-6,46],[-17,46],[-22,46],[-30,47],[-31,47],[-39,47],[-41,48],[-40,48],[-43,49],[-42,49],[-42,-43,50],[-49,51],[-50,52],[-48,51],[-45,53],[-44,53],[-46,-47,54],[-54,56],[-53,55],[-51,-56,57],[-52,-55,57],[-57],[1,4,7,10,14,15,19,21,24,29,32,34,35,38],[2,5,8,11,13,16,17,20,23,25,28,29,30,33,36,38],[3,6,9,12,18,22,23,26,27,28,31,37,39]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":85,\"b\":50},{\"tag\":\"incompatible\",\"a\":86,\"b\":85},{\"tag\":\"mate\",\"ridge\":290,\"a\":10,\"owners\":[80,83,84,87]},{\"tag\":\"mate\",\"ridge\":290,\"a\":36,\"owners\":[84,87]},{\"tag\":\"mate\",\"ridge\":290,\"a\":45,\"owners\":[80,83,87]},{\"tag\":\"mate\",\"ridge\":290,\"a\":48,\"owners\":[83,87]},{\"tag\":\"mate\",\"ridge\":290,\"a\":52,\"owners\":[80,84]},{\"tag\":\"mate\",\"ridge\":290,\"a\":53,\"owners\":[80,83,84]},{\"tag\":\"mate\",\"ridge\":194,\"a\":11,\"owners\":[78,82,85,87]},{\"tag\":\"mate\",\"ridge\":194,\"a\":37,\"owners\":[85,87]},{\"tag\":\"mate\",\"ridge\":194,\"a\":46,\"owners\":[82,87]},{\"tag\":\"mate\",\"ridge\":194,\"a\":49,\"owners\":[78,82,87]},{\"tag\":\"mate\",\"ridge\":194,\"a\":51,\"owners\":[78,85]},{\"tag\":\"mate\",\"ridge\":194,\"a\":54,\"owners\":[78,82,85]},{\"tag\":\"mate\",\"ridge\":641,\"a\":20,\"owners\":[39,50,66,67,72]},{\"tag\":\"mate\",\"ridge\":641,\"a\":47,\"owners\":[66,67,72]},{\"tag\":\"mate\",\"ridge\":641,\"a\":60,\"owners\":[50,72]},{\"tag\":\"mate\",\"ridge\":641,\"a\":70,\"owners\":[39,66,67]},{\"tag\":\"mate\",\"ridge\":641,\"a\":71,\"owners\":[39,50,67,72]},{\"tag\":\"mate\",\"ridge\":648,\"a\":60,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":646,\"a\":39,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":646,\"a\":79,\"owners\":[39]},{\"tag\":\"mate\",\"ridge\":204,\"a\":59,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":204,\"a\":78,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":228,\"a\":64,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":228,\"a\":82,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":356,\"a\":83,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":676,\"a\":66,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":676,\"a\":88,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":708,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":216,\"a\":69,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":720,\"a\":72,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":480,\"a\":73,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":480,\"a\":87,\"owners\":[73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":61,\"full_literals\":[-19,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":68,\"full_literals\":[-24,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-32,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":84,\"full_literals\":[-35,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":64,\"full_literals\":[-20,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-21,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":73,\"full_literals\":[-29,42]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[82,83,87],\"full_literals\":[-43,33,34,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-33,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-34,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":87,\"full_literals\":[-38,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":50,\"full_literals\":[-12,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":86,\"full_literals\":[-37,45]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[39,59,66,67],\"full_literals\":[-46,6,17,22,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":39,\"full_literals\":[-6,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":59,\"full_literals\":[-17,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":66,\"full_literals\":[-22,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":78,\"full_literals\":[-30,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":79,\"full_literals\":[-31,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":88,\"full_literals\":[-39,47]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-43,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-50,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-47,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-51,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[10,36,45,48,52,53,61,65,68,73,80,83,84,87]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[11,37,46,49,51,54,59,64,67,69,72,73,78,82,85,87]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[20,39,47,50,60,66,67,70,71,72,79,86,88]}]}"
  "74 -46 6 17 22 0 30 48 0\n75 2 5 8 11 13 16 17 20 25 29 30 33 36 38 0 30 32 72 0\n76 3 6 9 12 18 22 26 27 31 37 39 0 30 32 73 0\n77 51 0 60 62 57 58 55 56 44 45 40 41 37 38 35 36 6 5 8 3 4 7 71 0\n78 -56 0 77 70 68 0\n79 -54 0 78 66 0\n80 46 53 0 32 30 63 47 20 64 46 49 51 22 19 16 29 18 15 76 0\n81 -46 0 79 65 52 53 54 23 21 28 74 0\n82 -6 0 81 49 0\n83 -17 0 81 50 0\n84 -22 0 81 51 0\n85 53 0 81 80 0\n86 -31 0 82 22 0\n87 -30 0 83 24 0\n88 -9 0 84 30 32 16 0\n89 -39 0 84 29 0\n90 -26 0 84 82 30 18 0\n91 -43 50 0 59 39 40 41 26 27 34 42 0\n92 36 43 0 87 83 45 33 43 12 25 11 31 13 9 14 10 75 0\n93 -36 0 32 30 89 86 90 84 88 82 1 2 17 19 15 76 0\n94 55 0 85 67 0\n95 43 0 93 92 0\n96 -52 0 94 70 69 0\n97 50 0 95 91 0\n98 0 97 96 61 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record013
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2ac78a9a3696639956a38ce4b8ae8785e0f9e1b46a9a64d9b16a5594e595555a34cd8b52d2b45d0f5c368d6338e9354cd3a2ccb4ae1b26c5b0ee8731ca719e1745c3783d0f23c4f870aa519261582e07a892a61951525854558342d0754330d2328c5322c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db69a6d24936936d34934924924d2492493492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 64), (facetIndex 72)]))
 (.branch 2
 (.leaf ([(facetIndex 81), (facetIndex 85)]))
 (.leaf ([(facetIndex 50), (facetIndex 68), (facetIndex 71)]))))
 (.branch 4
 (.leaf ([(facetIndex 83), (facetIndex 84)]))
 (.branch 5
 (.leaf ([(facetIndex 40), (facetIndex 60), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 86)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "14b608b40000402900004000000080000004z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4, 5]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record013" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record013" 42

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record013" "{\"ridges\":[[11,193],[22,641],[39,193],[40,646],[46,193],[47,641],[48,193],[50,658],[51,193],[54,193],[61,641],[66,676],[67,708],[69,641],[70,641],[71,720],[79,646],[83,216],[84,658],[86,676]],\"owners\":[[11,193,[60,64,67,68,71,72],[39,46,48,51,54]],[39,193,[68,71,72],[11,46,48,51,54,60,64,67]],[46,193,[64,67,71,72],[11,39,48,51,54,60,68]],[48,193,[60,64,67,72],[11,39,46,51,54,68,71]],[51,193,[60,67,68,71],[11,39,46,48,54,64,72]],[54,193,[60,64,67,68,71],[11,39,46,48,51,72]],[22,641,[40,50,66,67,71],[47,61,69,70]],[47,641,[66,67,71],[22,40,50,61,69,70]],[61,641,[50,71],[22,40,47,66,67,69,70]],[69,641,[40,66,67],[22,47,50,61,70,71]],[70,641,[40,50,67,71],[22,47,61,66,69]],[40,646,[79],[]],[79,646,[40],[]],[50,658,[84],[]],[84,658,[50],[]],[66,676,[86],[]],[86,676,[66],[]],[67,708,[],[]],[83,216,[68],[]],[71,720,[],[]]],\"edges\":[[39,[11,39,46,48,51,54,60,64,67,68,71,72,78,81,83,85]],[43,[22,40,47,50,61,66,67,69,70,71,79,84,86]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record013" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record013\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-8,-5],[-8,-7],[-9,-4],[-9,-8],[-11,-4],[-14,-11],[-16,-8],[-21,-4],[-21,-14],[-24,-8],[-1,11,13,15,16,19,20],[-3,16,19,20],[-5,13,15,19,20],[-7,11,13,15,20],[-9,11,15,16,19],[-10,11,13,15,16,19],[-2,4,8,14,15,19],[-6,14,15,19],[-12,8,19],[-17,4,14,15],[-18,4,8,15,19],[-4,22],[-22,4],[-8,25],[-25,8],[-14,27],[-27,14],[-15],[-24,16],[-19],[-13,28],[-20,28],[-23,29],[-26,29],[-8,30],[-16,30],[-25,31],[-4,32],[-11,32],[-14,32],[-21,33],[-22,33],[-27,33],[-30,34],[-29,34],[-29,-30,35],[-34,36],[-35,37],[-28,36],[-28,-34,37],[-33,38],[-32,38],[-32,-33,39],[-39,41],[-31,40],[-31,-38,41],[-36,-41,42],[-37,-40,42],[-42],[1,3,5,7,9,10,11,13,15,16,19,20,21,23,24,26],[2,4,6,8,12,14,15,17,18,19,22,25,27]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":40},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":60,\"b\":40},{\"tag\":\"incompatible\",\"a\":66,\"b\":60},{\"tag\":\"incompatible\",\"a\":68,\"b\":50},{\"tag\":\"incompatible\",\"a\":78,\"b\":40},{\"tag\":\"incompatible\",\"a\":78,\"b\":66},{\"tag\":\"incompatible\",\"a\":83,\"b\":50},{\"tag\":\"mate\",\"ridge\":193,\"a\":11,\"owners\":[60,64,67,68,71,72]},{\"tag\":\"mate\",\"ridge\":193,\"a\":39,\"owners\":[68,71,72]},{\"tag\":\"mate\",\"ridge\":193,\"a\":46,\"owners\":[64,67,71,72]},{\"tag\":\"mate\",\"ridge\":193,\"a\":48,\"owners\":[60,64,67,72]},{\"tag\":\"mate\",\"ridge\":193,\"a\":51,\"owners\":[60,67,68,71]},{\"tag\":\"mate\",\"ridge\":193,\"a\":54,\"owners\":[60,64,67,68,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":22,\"owners\":[40,50,66,67,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":47,\"owners\":[66,67,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":61,\"owners\":[50,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":69,\"owners\":[40,66,67]},{\"tag\":\"mate\",\"ridge\":641,\"a\":70,\"owners\":[40,50,67,71]},{\"tag\":\"mate\",\"ridge\":646,\"a\":40,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":646,\"a\":79,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":658,\"a\":50,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":658,\"a\":84,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":676,\"a\":66,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":676,\"a\":86,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":708,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":216,\"a\":83,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":720,\"a\":71,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":64,\"full_literals\":[-13,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":72,\"full_literals\":[-20,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":81,\"full_literals\":[-23,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-26,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":50,\"full_literals\":[-8,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":68,\"full_literals\":[-16,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":84,\"full_literals\":[-25,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":40,\"full_literals\":[-4,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":60,\"full_literals\":[-11,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":66,\"full_literals\":[-14,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-21,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-22,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":86,\"full_literals\":[-27,33]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-29,-30,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-28,-34,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-33,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-39,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-38,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-36,-41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-37,-40,42],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[11,39,46,48,51,54,60,64,67,68,71,72,78,81,83,85]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[22,40,47,50,61,66,67,69,70,71,79,84,86]}]}"
  "62 1 3 5 7 9 10 11 13 16 20 21 23 24 26 0 28 30 60 0\n63 2 4 6 8 12 14 17 18 22 25 27 0 28 30 61 0\n64 14 4 8 0 30 28 21 23 25 19 18 27 20 17 63 0\n65 -14 9 36 0 30 28 47 44 36 29 49 32 12 31 13 45 34 33 6 9 14 11 16 62 0\n66 9 36 0 30 28 47 44 36 29 49 32 12 31 13 45 34 33 35 65 64 5 8 14 11 16 62 0\n67 36 0 30 28 47 44 35 36 66 3 15 64 6 0\n68 -41 0 67 59 57 0\n69 -39 0 68 54 0\n70 -14 0 69 26 40 43 53 0\n71 -8 0 68 59 28 30 1 2 4 7 10 24 35 37 44 55 56 58 51 52 48 50 41 39 46 31 32 11 16 33 34 12 62 0\n72 4 0 71 70 64 0\n73 22 0 72 22 0\n74 32 0 72 38 0\n75 33 0 73 42 0\n76 0 74 75 69 53 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record013
