module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00082Data
public import GraphInputsRow26Part00082Frames
public import GraphInputsRow26Part00082Leaves
public import GraphInputsRow26Part00082Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨76, by decide⟩, ⟨82, by decide⟩, ⟨92, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 32985348833280, (certNat% 3), 54043195528445952]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 28037546508288, (certNat% 5), (certNat% 6), (certNat% 7)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 10), 96757044215808, 2199023255552]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 9), (certNat% 10), 96757060993024, 2199023255552]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 14), (certNat% 15)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), (certNat% 13), 96757044215808, (certNat% 7)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 17), (certNat% 10), 6463422464, 98956046499840]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 10), (certNat% 20), (certNat% 21), 58003030016, 28587302322176]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c13 c2
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013
def vertexColumn : Fields := ⟨10, (certNat% 22)⟩
def kindColumn : Fields := ⟨3, (certNat% 23)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨86, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), (certNat% 26), 506906804224, (certNat% 27)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 25), (certNat% 26), 506973913088, (certNat% 27)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 30), 1037939211501568, (certNat% 31), 432345564227567616]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 33), (certNat% 34), (certNat% 35)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), 474989023199232, (certNat% 37), (certNat% 38)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), 263882790666240, (certNat% 41)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), 474989023199232, (certNat% 35), 4611686018427387904]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), (certNat% 45), (certNat% 37), 546457279004672]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 1037939211501568, (certNat% 47), 432345564227567616, 235149459456]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 49), 232163115008, (certNat% 47), 3221225472]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 26), (certNat% 51), (certNat% 52), 1037939077283840]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 31), (certNat% 54), (certNat% 55), (certNat% 56)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), (certNat% 26), 1037939110838272, (certNat% 52)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), 231928233984, (certNat% 38), (certNat% 60)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), 98784247808, (certNat% 55), (certNat% 34)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), (certNat% 63), (certNat% 64), 231928233984]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 64), (certNat% 55), 232196669440, (certNat% 66)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c22 c17
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 26), 52776759459840, (certNat% 68), 231928233984]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), (certNat% 55), (certNat% 49), 476088534827008, (certNat% 70), 232129560576]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c27 c16
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c28 c15
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c29 c14
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c30 c13
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c31 c12
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c32 c11
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c33 c2
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c34 c1
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c35 c0
  c36
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015
def vertexColumn : Fields := ⟨10, (certNat% 71)⟩
def kindColumn : Fields := ⟨3, (certNat% 72)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨84, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), (certNat% 74), 527765585526784, 17293822569102704640, (certNat% 75), (certNat% 76)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ae2743b2b29c8f2aa8eac6a9a66a3a2ea6639b16959568d876c38ce8b8ae1b8e9666394e4b9395558d5351d4cd8b52d2b46d38d9354e332cc7362ccb8acab1ae1b46c9b0ed4731e2729c6785d1715c3783c8f13c2f3c22c34a0e438e1344b11c4a91950d0b4c344c9314d0b22d0711c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6da6db6db6db6d34da6da4db4d24924d249a6d269369a4d2489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 22), (facetIndex 25), (facetIndex 67), (facetIndex 69)]))
 (.leaf ([(facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 40), (facetIndex 44), (facetIndex 45), (facetIndex 49), (facetIndex 84)]))
 (.leaf ([(facetIndex 27), (facetIndex 28), (facetIndex 55)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 59), (facetIndex 60), (facetIndex 64)]))
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 47)])))
 (.branch 7
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 43), (facetIndex 48)]))
 (.leaf ([(facetIndex 23), (facetIndex 24), (facetIndex 42)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2000000000000004004800609256a12dc2036168083607ez11;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record003" 45

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record003" "{\"ridges\":[[7,274],[28,273],[37,274],[46,530],[47,273],[48,274],[56,308],[57,533],[58,340],[61,312],[71,530],[74,788],[79,408],[81,792],[85,530],[86,530],[88,596]],\"owners\":[[28,273,[61,63],[7,37,47,48,56,58]],[47,273,[56,61,63],[7,28,37,48,58]],[7,274,[72,74,79,81],[28,37,47,48]],[37,274,[72,74],[7,28,47,48,79,81]],[48,274,[72,74,81],[7,28,37,47,79]],[46,530,[73,74,80,81],[29,38,71,78,85,86]],[71,530,[38,80,81],[29,46,73,74,78,85,86]],[85,530,[29,38,74,80,81],[46,71,73,78,86]],[86,530,[29,38,73,74,81],[46,71,78,80,85]],[57,533,[29],[]],[56,308,[],[]],[58,340,[72],[]],[61,312,[],[]],[79,408,[63],[]],[88,596,[73],[]],[74,788,[],[]],[81,792,[],[]]],\"edges\":[[33,[7,28,37,47,48,56,58,61,63,72,74,79,81]],[34,[29,38,46,57,62,71,73,74,78,80,81,85,86,88,89]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-6,-4],[-6,-5],[-7,-2],[-7,-3],[-12,-7],[-17,-6],[-23,-9],[-23,-10],[-23,-11],[-23,-13],[-23,-16],[-23,-22],[-25,-4],[-25,-8],[-25,-17],[-26,-4],[-26,-5],[-26,-17],[-28,-23],[-30,-23],[-35,-23],[-5,21,23],[-15,18,21,23],[-1,25,27,29,31],[-10,25,27],[-16,25,27,31],[-14,26,27,30,31],[-24,11,30,31],[-32,6,11,27,30,31],[-33,6,11,26,27,31],[-19,6],[-18],[-20,25],[-21],[-29,23],[-34,26],[-27],[-31],[-36,4,5,17],[-37,7,8,15],[-38,9,10,13,16],[-39,2,3,12],[-40,36],[-41,40],[-42,37],[-43,38],[-43,39],[-44,42],[-44,43],[-45,41,44],[45],[1,5,10,15,16,18,20,21,23,25,27,29,31],[6,11,14,19,22,24,26,27,28,30,31,32,33,34,35]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":29,\"b\":27},{\"tag\":\"incompatible\",\"a\":29,\"b\":28},{\"tag\":\"incompatible\",\"a\":33,\"b\":23},{\"tag\":\"incompatible\",\"a\":33,\"b\":24},{\"tag\":\"incompatible\",\"a\":42,\"b\":33},{\"tag\":\"incompatible\",\"a\":55,\"b\":29},{\"tag\":\"incompatible\",\"a\":63,\"b\":36},{\"tag\":\"incompatible\",\"a\":63,\"b\":37},{\"tag\":\"incompatible\",\"a\":63,\"b\":38},{\"tag\":\"incompatible\",\"a\":63,\"b\":43},{\"tag\":\"incompatible\",\"a\":63,\"b\":48},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":72,\"b\":27},{\"tag\":\"incompatible\",\"a\":72,\"b\":34},{\"tag\":\"incompatible\",\"a\":72,\"b\":55},{\"tag\":\"incompatible\",\"a\":73,\"b\":27},{\"tag\":\"incompatible\",\"a\":73,\"b\":28},{\"tag\":\"incompatible\",\"a\":73,\"b\":55},{\"tag\":\"incompatible\",\"a\":78,\"b\":63},{\"tag\":\"incompatible\",\"a\":80,\"b\":63},{\"tag\":\"incompatible\",\"a\":89,\"b\":63},{\"tag\":\"mate\",\"ridge\":273,\"a\":28,\"owners\":[61,63]},{\"tag\":\"mate\",\"ridge\":273,\"a\":47,\"owners\":[56,61,63]},{\"tag\":\"mate\",\"ridge\":274,\"a\":7,\"owners\":[72,74,79,81]},{\"tag\":\"mate\",\"ridge\":274,\"a\":37,\"owners\":[72,74]},{\"tag\":\"mate\",\"ridge\":274,\"a\":48,\"owners\":[72,74,81]},{\"tag\":\"mate\",\"ridge\":530,\"a\":46,\"owners\":[73,74,80,81]},{\"tag\":\"mate\",\"ridge\":530,\"a\":71,\"owners\":[38,80,81]},{\"tag\":\"mate\",\"ridge\":530,\"a\":85,\"owners\":[29,38,74,80,81]},{\"tag\":\"mate\",\"ridge\":530,\"a\":86,\"owners\":[29,38,73,74,81]},{\"tag\":\"mate\",\"ridge\":533,\"a\":57,\"owners\":[29]},{\"tag\":\"mate\",\"ridge\":308,\"a\":56,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":340,\"a\":58,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":312,\"a\":61,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":408,\"a\":79,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":596,\"a\":88,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":788,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":792,\"a\":81,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[27,28,55],\"full_literals\":[-36,4,5,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[33,34,47],\"full_literals\":[-37,7,8,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[36,37,43,48],\"full_literals\":[-38,9,10,13,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[23,24,42],\"full_literals\":[-39,2,3,12]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-40,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-42,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-44,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-45,41,44],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[7,28,37,47,48,56,58,61,63,72,74,79,81]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[29,38,46,57,62,71,73,74,78,80,81,85,86,88,89]}]}"
  "54 1 5 10 15 16 20 23 25 29 0 32 34 37 38 52 0\n55 6 11 14 19 22 24 26 28 30 32 33 34 35 0 37 38 53 0\n56 25 23 0 32 34 38 37 35 23 22 24 25 26 33 54 0\n57 23 -36 0 34 22 56 13 15 39 0\n58 6 26 -23 0 38 37 36 20 27 9 28 21 19 12 31 29 30 55 0\n59 -6 -36 0 1 2 6 39 0\n60 -23 0 51 7 8 10 11 41 46 49 50 44 43 59 58 16 17 18 39 0\n61 -15 0 60 32 34 23 0\n62 25 0 60 56 0\n63 -36 0 60 57 0\n64 -8 0 62 14 0\n65 -40 0 63 43 0\n66 -41 0 65 44 0\n67 44 0 66 51 50 0\n68 42 0 67 48 0\n69 43 0 67 49 0\n70 37 0 68 45 0\n71 39 0 69 47 0\n72 7 0 70 61 64 40 0\n73 -2 0 72 3 0\n74 -3 0 72 4 0\n75 -12 0 72 5 0\n76 0 75 74 73 71 42 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ae0f43b2b29c8f2aa8eac6a9a66a3a2e8e665956358b61d98e33a2e2b86e9c4f13a7198e5392e4e5554d54d4b51d4cd8b52d2b46d98ce3c4e5354cd38ccb31cf0b32e2b2ac6b86d1b26c3b51cc789ca719d1725c570de0f23c4f0bcf0390ac348c64388e8c4718a4654342d84d1314e0b42d0711c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a4da6db6da6d36934d26d369b6d34926d249349a6d26d26d269a491249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 65), (facetIndex 69)]))
 (.leaf ([(facetIndex 23), (facetIndex 71), (facetIndex 73), (facetIndex 74)])))
 (.branch 3
 (.leaf ([(facetIndex 21), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55)]))
 (.leaf ([(facetIndex 62), (facetIndex 80), (facetIndex 91), (facetIndex 92)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 24), (facetIndex 37), (facetIndex 40), (facetIndex 42)]))
 (.leaf ([(facetIndex 26), (facetIndex 28), (facetIndex 57), (facetIndex 77)])))
 (.branch 7
 (.leaf ([(facetIndex 22), (facetIndex 29), (facetIndex 32), (facetIndex 33)]))
 (.branch 8
 (.leaf ([(facetIndex 36), (facetIndex 47), (facetIndex 48), (facetIndex 49)]))
 (.leaf ([(facetIndex 43), (facetIndex 46), (facetIndex 68), (facetIndex 88)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "330080000000300500110100800000300005022220077780084040047006600650504162z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 25), (facetIndex 27), (facetIndex 59), (facetIndex 61), (facetIndex 79)]))
 (.leaf ([(facetIndex 58), (facetIndex 75), (facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 64), (facetIndex 66), (facetIndex 83), (facetIndex 84)]))
 (.leaf ([(facetIndex 63), (facetIndex 81), (facetIndex 85), (facetIndex 93)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 30), (facetIndex 41), (facetIndex 60)]))
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 56)])))
 (.branch 7
 (.leaf ([(facetIndex 44), (facetIndex 67), (facetIndex 70)]))
 (.branch 8
 (.leaf ([(facetIndex 31), (facetIndex 50), (facetIndex 51), (facetIndex 76), (facetIndex 82), (facetIndex 86), (facetIndex 87)]))
 (.leaf ([(facetIndex 72), (facetIndex 89), (facetIndex 90)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3008807732273001071008060062023004010500007700000600405500220074z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
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
def grouped3_0019 : List Nat := [0, 1, 2, 3]
def grouped3_0021 : List Nat := [1]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [2, 3]
def grouped3_0024 : List Nat := [3]
def grouped3_0025 : List Nat := [4, 5]
def grouped3_0026 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0027 : List Nat := [6]
def grouped3_0028 : List Nat := [6, 7, 8]
def grouped3_0029 : List Nat := [7]
def grouped3_0030 : List Nat := [7, 8]
def grouped3_0031 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record004" 116

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record004" "{\"ridges\":[[5,81],[5,82],[6,274],[8,13],[9,13],[9,265],[10,69],[11,521],[11,552],[13,560],[14,14],[15,14],[15,266],[17,82],[18,44],[19,100],[22,67],[22,69],[22,70],[23,138],[24,13],[24,14],[24,521],[24,522],[28,274],[36,274],[37,522],[40,552],[41,67],[45,560],[47,67],[47,274],[48,81],[48,82],[49,274],[51,67],[51,610],[52,41],[53,41],[55,552],[56,13],[59,308],[61,69],[61,81],[61,340],[62,69],[64,312],[65,552],[65,560],[66,265],[66,273],[66,521],[66,792],[67,41],[68,81],[68,224],[69,560],[70,14],[71,14],[73,138],[74,138],[78,70],[78,82],[78,340],[79,404],[80,70],[83,408],[85,266],[85,522],[85,530],[85,792],[86,106],[87,522],[87,674],[88,82],[89,610],[90,146],[90,674],[91,168]],\"owners\":[[22,67,[5,43,46,47,48,50,51],[1,29,32,33,38,41]],[9,265,[3,36,42,64,66],[54]],[66,265,[3,9,54],[36,42,64]],[15,266,[3,36,42,83,85],[74]],[85,266,[3,15,74],[36,42,83]],[37,522,[72,87],[4,24,40,42,82,84,85]],[66,273,[6,28,47,59,61],[36,49,64]],[6,274,[78,79,83,85],[28,36,47,49]],[28,274,[83,85],[6,36,47,49,78,79]],[36,274,[78,79],[6,28,47,49,83,85]],[47,274,[79,83,85],[6,28,36,49,78]],[49,274,[78,79,83],[6,28,36,47,85]],[85,530,[7,45,48,89,90],[37,49,82,84]],[52,41,[11,34,39,40,63,64,65],[8,21,38,53,54,67]],[53,41,[11,34,38,40,64,65],[8,21,39,52,54,63,67]],[67,41,[8,11,21,34,40,54,64,65],[38,39,52,53,63]],[18,44,[8,21,52,54,55,70,72],[71,91]],[19,100,[10,29,52,57,70,75],[80,91,92]],[11,552,[72,82,87,93],[40,55,65]],[40,552,[93],[11,55,65,72,82,87]],[55,552,[82,87,93],[11,40,65,72]],[65,552,[72,87],[11,40,55,82,93]],[13,560,[82,89,90,93],[45,65,69]],[45,560,[93],[13,65,69,82,89,90]],[65,560,[89,90],[13,45,69,82,93]],[69,560,[82,90,93],[13,45,65,89]],[23,138,[81,83,84,86,87],[14,35,39,41,71,73,74]],[73,138,[35,39,81,83,84,87],[14,23,41,71,74,86]],[74,138,[35,39,41,81,84,86,87],[14,23,71,73,83]],[90,146,[17,27,35,46,77,79,83],[44,76,81,84,88]],[91,168,[39,63,81,87,93],[18,53,67,71,86]],[68,224,[19,80,86,91],[20,50,62,67,88]],[86,106,[38,70],[]],[51,610,[89],[]],[89,610,[51],[]],[59,308,[],[]],[61,340,[78],[]],[78,340,[61],[]],[64,312,[],[]],[66,792,[85],[]],[85,792,[66],[]],[79,404,[],[]],[83,408,[],[]],[87,674,[90],[]],[90,674,[87],[]]],\"edges\":[[27,[14,18,23,35,39,41,53,56,63,67,71,73,74,81,83,84,86,87,91,93]],[28,[3,9,15,36,42,54,64,66,74,83,85]],[33,[6,28,36,47,49,59,61,64,66,78,79,83,85]],[38,[11,13,31,40,45,51,55,65,69,72,82,87,89,90,93]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-17,-16],[-18,-1],[-18,-15],[-18,-17],[-21,-16],[-25,-21],[-30,-18],[-31,-18],[-33,-18],[-37,-19],[-37,-24],[-38,-4],[-38,-19],[-38,-21],[-38,-25],[-38,-35],[-38,-37],[-39,-3],[-39,-21],[-39,-38],[-40,-34],[-40,-36],[-43,-16],[-45,-18],[-46,-18],[-50,-22],[-50,-35],[-54,-28],[-54,-29],[-57,-17],[-57,-24],[-57,-41],[-57,-51],[-58,-35],[-58,-48],[-58,-57],[-59,-16],[-61,-18],[-63,-16],[-63,-18],[-65,-24],[-65,-37],[-65,-62],[-66,-19],[-66,-20],[-66,-21],[-66,-24],[-66,-25],[-66,-37],[-66,-38],[-66,-48],[-66,-64],[-66,-65],[-73,-26],[-73,-27],[-73,-29],[-73,-34],[-73,-52],[-73,-54],[-73,-69],[-73,-70],[-73,-72],[-74,-16],[-76,-23],[-76,-32],[-76,-36],[-76,-41],[-76,-42],[-76,-61],[-76,-70],[-76,-75],[-77,-31],[-77,-57],[-77,-60],[-77,-74],[-77,-76],[-78,-22],[-78,-32],[-78,-36],[-78,-60],[-78,-68],[-78,-76],[-79,-16],[-79,-62],[-80,-57],[-80,-66],[-81,-28],[-81,-73],[-5,-6,-18],[-6,-18,-47],[-10,-11,-18],[-11,-18,-59],[-11,-18,-60],[-16,2,35,37,38,39,41,42],[-33,-38,-42],[-7,-16,-50],[-16,-50,-51],[-16,-66,-68],[-6,1,28,34,53,55],[-55,1,6,45],[-11,1,28,34,71,73],[-73,1,11,63],[-8,-18,-55],[-29,61,75],[-18,-73,-75],[-2,-50,-57],[-39,-50,-57],[-2,-66,-76],[-12,-39,-66],[-39,-66,-76],[-55,3,21,38,49,50],[-3,66,67,71,73],[-21,71,73],[-28,66,67],[-38,67,71,73],[-40,66,67,71],[-73,4,36,39,77,78],[-43,8,26,31,32,52,53,54],[-44,8,26,30,32,53,54],[-56,5,8,15,26,32,45,53,54],[-13,5,15,43,45,46,59,61],[-14,7,22,43,48,59,64],[-8,61,70,75,81],[-32,81],[-46,70,75,81],[-54,61,75],[-9,70,77,78,81],[-36,81],[-54,77,78],[-58,70,78,81],[-17,69,71,72,74,75],[-62,27,31,69,71,72,75],[-63,27,31,33,69,72,74,75],[-78,12,20,27,37,65,67,71],[-79,31,52,69,75,81],[-57,14,68,74,79],[-74,30,59],[-42,77],[-77,42],[-49],[-50,66],[-66,50],[-53],[-55,73],[-73,55],[-67],[-71],[-75,78],[-78,75],[-82,36,54,58],[-83,17,60,62,63],[-84,51,68,79,80],[-85,18,29,32,34],[-86,19,21,48,65],[-87,16,22,24,25],[-88,28,38,39,40],[-89,35,37,57,76],[-90,82,83],[-91,82],[-91,83],[-92,84],[-93,90],[-93,91,92],[-94,91],[-94,92],[-95,85,86],[-96,85],[-96,86],[-97,88,89],[-98,88],[-98,89],[-99,87,98],[-100,87],[-99,97],[-100,98],[-101,95,100],[-101,96,99],[-102,96,100],[-103,96],[-104,93,103],[-104,94,102],[-104,101],[104],[-50,105],[-66,106],[-27,107],[-75,108],[-78,109],[-105,-106,110],[-107,111],[-110,-111,112],[-108,-109,113],[-113,114],[-114,115],[-112,-115,116],[-116],[10,13,17,27,31,33,44,47,52,56,60,62,63,69,71,72,74,75,79,81],[1,6,11,28,34,45,53,55,63,71,73],[3,21,28,38,40,49,50,53,55,66,67,71,73],[8,9,23,32,36,42,46,54,58,61,70,75,77,78,81]],\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":23,\"b\":22},{\"tag\":\"incompatible\",\"a\":24,\"b\":3},{\"tag\":\"incompatible\",\"a\":24,\"b\":21},{\"tag\":\"incompatible\",\"a\":24,\"b\":23},{\"tag\":\"incompatible\",\"a\":28,\"b\":22},{\"tag\":\"incompatible\",\"a\":33,\"b\":28},{\"tag\":\"incompatible\",\"a\":38,\"b\":24},{\"tag\":\"incompatible\",\"a\":39,\"b\":24},{\"tag\":\"incompatible\",\"a\":41,\"b\":24},{\"tag\":\"incompatible\",\"a\":46,\"b\":26},{\"tag\":\"incompatible\",\"a\":46,\"b\":32},{\"tag\":\"incompatible\",\"a\":47,\"b\":7},{\"tag\":\"incompatible\",\"a\":47,\"b\":26},{\"tag\":\"incompatible\",\"a\":47,\"b\":28},{\"tag\":\"incompatible\",\"a\":47,\"b\":33},{\"tag\":\"incompatible\",\"a\":47,\"b\":43},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":48,\"b\":6},{\"tag\":\"incompatible\",\"a\":48,\"b\":28},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":42},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":52,\"b\":22},{\"tag\":\"incompatible\",\"a\":54,\"b\":24},{\"tag\":\"incompatible\",\"a\":55,\"b\":24},{\"tag\":\"incompatible\",\"a\":61,\"b\":29},{\"tag\":\"incompatible\",\"a\":61,\"b\":43},{\"tag\":\"incompatible\",\"a\":65,\"b\":36},{\"tag\":\"incompatible\",\"a\":65,\"b\":37},{\"tag\":\"incompatible\",\"a\":68,\"b\":23},{\"tag\":\"incompatible\",\"a\":68,\"b\":32},{\"tag\":\"incompatible\",\"a\":68,\"b\":50},{\"tag\":\"incompatible\",\"a\":68,\"b\":62},{\"tag\":\"incompatible\",\"a\":69,\"b\":43},{\"tag\":\"incompatible\",\"a\":69,\"b\":57},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":22},{\"tag\":\"incompatible\",\"a\":72,\"b\":24},{\"tag\":\"incompatible\",\"a\":74,\"b\":22},{\"tag\":\"incompatible\",\"a\":74,\"b\":24},{\"tag\":\"incompatible\",\"a\":77,\"b\":32},{\"tag\":\"incompatible\",\"a\":77,\"b\":46},{\"tag\":\"incompatible\",\"a\":77,\"b\":73},{\"tag\":\"incompatible\",\"a\":78,\"b\":26},{\"tag\":\"incompatible\",\"a\":78,\"b\":27},{\"tag\":\"incompatible\",\"a\":78,\"b\":28},{\"tag\":\"incompatible\",\"a\":78,\"b\":32},{\"tag\":\"incompatible\",\"a\":78,\"b\":33},{\"tag\":\"incompatible\",\"a\":78,\"b\":46},{\"tag\":\"incompatible\",\"a\":78,\"b\":47},{\"tag\":\"incompatible\",\"a\":78,\"b\":57},{\"tag\":\"incompatible\",\"a\":78,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":85,\"b\":34},{\"tag\":\"incompatible\",\"a\":85,\"b\":35},{\"tag\":\"incompatible\",\"a\":85,\"b\":37},{\"tag\":\"incompatible\",\"a\":85,\"b\":42},{\"tag\":\"incompatible\",\"a\":85,\"b\":63},{\"tag\":\"incompatible\",\"a\":85,\"b\":65},{\"tag\":\"incompatible\",\"a\":85,\"b\":81},{\"tag\":\"incompatible\",\"a\":85,\"b\":82},{\"tag\":\"incompatible\",\"a\":85,\"b\":84},{\"tag\":\"incompatible\",\"a\":86,\"b\":22},{\"tag\":\"incompatible\",\"a\":88,\"b\":31},{\"tag\":\"incompatible\",\"a\":88,\"b\":40},{\"tag\":\"incompatible\",\"a\":88,\"b\":45},{\"tag\":\"incompatible\",\"a\":88,\"b\":50},{\"tag\":\"incompatible\",\"a\":88,\"b\":51},{\"tag\":\"incompatible\",\"a\":88,\"b\":72},{\"tag\":\"incompatible\",\"a\":88,\"b\":82},{\"tag\":\"incompatible\",\"a\":88,\"b\":87},{\"tag\":\"incompatible\",\"a\":89,\"b\":39},{\"tag\":\"incompatible\",\"a\":89,\"b\":68},{\"tag\":\"incompatible\",\"a\":89,\"b\":71},{\"tag\":\"incompatible\",\"a\":89,\"b\":86},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":90,\"b\":29},{\"tag\":\"incompatible\",\"a\":90,\"b\":40},{\"tag\":\"incompatible\",\"a\":90,\"b\":45},{\"tag\":\"incompatible\",\"a\":90,\"b\":71},{\"tag\":\"incompatible\",\"a\":90,\"b\":80},{\"tag\":\"incompatible\",\"a\":90,\"b\":88},{\"tag\":\"incompatible\",\"a\":91,\"b\":22},{\"tag\":\"incompatible\",\"a\":91,\"b\":73},{\"tag\":\"incompatible\",\"a\":92,\"b\":68},{\"tag\":\"incompatible\",\"a\":92,\"b\":78},{\"tag\":\"incompatible\",\"a\":93,\"b\":36},{\"tag\":\"incompatible\",\"a\":93,\"b\":85},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[8,9,24]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[9,24,56]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[14,15,24]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[15,24,70]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[15,24,71]},{\"tag\":\"mate\",\"ridge\":67,\"a\":22,\"owners\":[5,43,46,47,48,50,51]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[41,47,51]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[10,22,61]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[22,61,62]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[22,78,80]},{\"tag\":\"mate\",\"ridge\":265,\"a\":9,\"owners\":[3,36,42,64,66]},{\"tag\":\"mate\",\"ridge\":265,\"a\":66,\"owners\":[3,9,54]},{\"tag\":\"mate\",\"ridge\":266,\"a\":15,\"owners\":[3,36,42,83,85]},{\"tag\":\"mate\",\"ridge\":266,\"a\":85,\"owners\":[3,15,74]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[11,24,66]},{\"tag\":\"mate\",\"ridge\":522,\"a\":37,\"owners\":[72,87]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[24,85,87]},{\"tag\":\"three\",\"ridge\":81,\"vertices\":[5,61,68]},{\"tag\":\"three\",\"ridge\":81,\"vertices\":[48,61,68]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[5,78,88]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[17,48,78]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[48,78,88]},{\"tag\":\"mate\",\"ridge\":273,\"a\":66,\"owners\":[6,28,47,59,61]},{\"tag\":\"mate\",\"ridge\":274,\"a\":6,\"owners\":[78,79,83,85]},{\"tag\":\"mate\",\"ridge\":274,\"a\":28,\"owners\":[83,85]},{\"tag\":\"mate\",\"ridge\":274,\"a\":36,\"owners\":[78,79]},{\"tag\":\"mate\",\"ridge\":274,\"a\":47,\"owners\":[79,83,85]},{\"tag\":\"mate\",\"ridge\":274,\"a\":49,\"owners\":[78,79,83]},{\"tag\":\"mate\",\"ridge\":530,\"a\":85,\"owners\":[7,45,48,89,90]},{\"tag\":\"mate\",\"ridge\":41,\"a\":52,\"owners\":[11,34,39,40,63,64,65]},{\"tag\":\"mate\",\"ridge\":41,\"a\":53,\"owners\":[11,34,38,40,64,65]},{\"tag\":\"mate\",\"ridge\":41,\"a\":67,\"owners\":[8,11,21,34,40,54,64,65]},{\"tag\":\"mate\",\"ridge\":44,\"a\":18,\"owners\":[8,21,52,54,55,70,72]},{\"tag\":\"mate\",\"ridge\":100,\"a\":19,\"owners\":[10,29,52,57,70,75]},{\"tag\":\"mate\",\"ridge\":552,\"a\":11,\"owners\":[72,82,87,93]},{\"tag\":\"mate\",\"ridge\":552,\"a\":40,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":552,\"a\":55,\"owners\":[82,87,93]},{\"tag\":\"mate\",\"ridge\":552,\"a\":65,\"owners\":[72,87]},{\"tag\":\"mate\",\"ridge\":560,\"a\":13,\"owners\":[82,89,90,93]},{\"tag\":\"mate\",\"ridge\":560,\"a\":45,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":560,\"a\":65,\"owners\":[89,90]},{\"tag\":\"mate\",\"ridge\":560,\"a\":69,\"owners\":[82,90,93]},{\"tag\":\"mate\",\"ridge\":138,\"a\":23,\"owners\":[81,83,84,86,87]},{\"tag\":\"mate\",\"ridge\":138,\"a\":73,\"owners\":[35,39,81,83,84,87]},{\"tag\":\"mate\",\"ridge\":138,\"a\":74,\"owners\":[35,39,41,81,84,86,87]},{\"tag\":\"mate\",\"ridge\":146,\"a\":90,\"owners\":[17,27,35,46,77,79,83]},{\"tag\":\"mate\",\"ridge\":168,\"a\":91,\"owners\":[39,63,81,87,93]},{\"tag\":\"mate\",\"ridge\":224,\"a\":68,\"owners\":[19,80,86,91]},{\"tag\":\"mate\",\"ridge\":106,\"a\":86,\"owners\":[38,70]},{\"tag\":\"mate\",\"ridge\":610,\"a\":51,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":610,\"a\":89,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":308,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":340,\"a\":61,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":340,\"a\":78,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":312,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":792,\"a\":66,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":792,\"a\":85,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":404,\"a\":79,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":408,\"a\":83,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":674,\"a\":87,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":674,\"a\":90,\"owners\":[87]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[45,65,69],\"full_literals\":[-82,36,54,58]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[23,71,73,74],\"full_literals\":[-83,17,60,62,63]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[62,80,91,92],\"full_literals\":[-84,51,68,79,80]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[24,37,40,42],\"full_literals\":[-85,18,29,32,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[26,28,57,77],\"full_literals\":[-86,19,21,48,65]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[22,29,32,33],\"full_literals\":[-87,16,22,24,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[36,47,48,49],\"full_literals\":[-88,28,38,39,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[43,46,68,88],\"full_literals\":[-89,35,37,57,76]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-90,82,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-91,82,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-91,false,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-92,false,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-93,90,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-93,91,92],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-94,91,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-94,false,92],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-95,85,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-96,85,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-96,false,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-97,88,89],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-98,88,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-98,false,89],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-99,87,98],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-100,87,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-99,false,97],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-100,false,98],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-101,95,100],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-101,96,99],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-102,96,100],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-103,96,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-104,93,103],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-104,94,102],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-104,false,101],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":61,\"full_literals\":[-50,105]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-66,106]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":35,\"full_literals\":[-27,107]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":87,\"full_literals\":[-75,108]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":90,\"full_literals\":[-78,109]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-105,-106,110],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-107,false,111],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0019\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-110,-111,112],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-108,-109,113],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-113,114],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-114,115],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-112,-115,116],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":27,\"owners\":[14,18,23,35,39,41,53,56,63,67,71,73,74,81,83,84,86,87,91,93]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[3,9,15,36,42,54,64,66,74,83,85]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[6,28,36,47,49,59,61,64,66,78,79,83,85]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[11,13,31,40,45,51,55,65,69,72,82,87,89,90,93]}]}"
  "201 101 0 183 182 0\n202 10 13 17 27 31 33 44 47 52 56 60 62 63 69 72 74 75 79 81 0 147 197 0\n203 1 6 11 28 34 45 55 63 73 0 143 147 198 0\n204 3 21 28 38 40 50 55 66 73 0 140 143 146 147 199 0\n205 -66 110 0 142 185 184 189 0\n206 73 66 0 147 146 141 116 114 144 113 115 112 204 0\n207 85 76 88 21 -73 0 201 183 170 175 176 88 128 59 166 167 177 178 174 181 169 164 159 150 34 35 36 157 10 42 154 0\n208 -18 -73 0 147 143 88 124 145 62 60 59 58 55 54 2 3 4 24 25 38 40 103 105 100 102 92 7 8 9 119 118 132 135 89 90 91 93 137 121 120 202 0\n209 77 23 81 32 36 42 8 9 54 61 70 75 46 78 0 200 130 0\n210 -76 -73 0 88 128 124 61 59 64 68 69 71 76 82 125 123 127 209 0\n211 -39 38 66 0 140 206 145 141 18 19 111 0\n212 88 -73 0 201 183 210 57 88 124 56 208 153 167 177 174 128 61 59 170 207 169 175 172 5 6 178 181 164 159 150 34 36 130 157 77 11 155 0\n213 -21 66 0 146 147 206 212 116 114 14 19 156 0\n214 38 66 0 146 147 206 212 116 114 211 156 0\n215 -58 -78 66 0 201 183 80 77 214 17 16 15 13 213 206 210 57 88 124 56 208 153 167 177 35 36 157 171 175 172 176 178 166 181 154 164 41 43 160 155 1 39 151 0\n216 -78 66 0 183 214 17 16 15 206 57 88 124 56 208 153 167 179 180 210 128 59 77 81 215 150 159 163 164 161 181 178 173 175 171 157 31 33 85 155 152 83 0\n217 66 0 183 147 206 55 56 57 59 60 61 62 88 124 128 208 153 167 179 180 162 214 12 20 216 148 130 117 150 72 74 75 139 158 132 131 95 151 133 0\n218 -19 0 217 44 0\n219 -20 0 217 45 0\n220 -21 0 217 46 0\n221 -24 0 217 47 0\n222 -25 0 217 48 0\n223 -37 0 217 49 0\n224 -38 0 217 50 0\n225 -48 0 217 51 0\n226 -64 0 217 52 0\n227 -65 0 217 53 0\n228 -80 0 217 86 0\n229 50 0 217 142 0\n230 110 0 217 205 0\n231 -86 0 225 220 218 227 154 0\n232 -22 0 229 26 0\n233 -35 0 229 27 0\n234 -96 0 231 168 0\n235 99 0 234 201 177 0\n236 -100 76 0 222 221 229 217 233 223 226 225 232 173 175 155 171 23 37 63 83 96 98 157 136 122 0\n237 -57 58 -82 78 0 229 223 233 222 221 232 235 224 32 73 106 107 138 129 94 150 155 22 128 172 87 170 156 0\n238 -16 -84 0 229 217 228 83 97 98 152 0\n239 76 78 0 234 183 222 221 232 235 233 223 236 178 181 164 165 159 161 238 155 172 171 157 36 237 0\n240 78 0 217 223 233 222 221 232 235 201 234 231 183 224 143 147 148 239 65 66 67 68 69 70 108 110 210 104 126 94 144 155 173 172 176 178 170 166 181 164 159 150 130 87 156 21 153 2 24 40 99 101 203 0\n241 -32 0 240 78 0\n242 -36 0 240 79 0\n243 -60 0 240 80 0\n244 -68 0 240 81 0\n245 -76 0 240 82 0\n246 75 0 240 149 0\n247 109 0 240 188 0\n248 -100 0 245 236 0\n249 108 0 246 187 0\n250 95 0 248 201 176 0\n251 -102 0 248 234 178 0\n252 113 0 249 247 192 0\n253 85 0 250 231 166 0\n254 94 0 251 183 181 0\n255 114 0 252 193 0\n256 91 0 254 164 0\n257 92 0 254 165 0\n258 115 0 255 194 0\n259 82 0 256 159 0\n260 83 0 256 160 0\n261 84 0 257 161 0\n262 -112 0 258 196 195 0\n263 -16 0 261 238 0\n264 -111 0 262 230 191 0\n265 -87 0 263 232 221 222 155 0\n266 -107 0 264 190 0\n267 98 0 265 235 172 0\n268 -27 0 266 186 0\n269 88 0 267 170 0\n270 89 0 267 171 0\n271 12 0 268 219 240 223 227 146 147 134 0\n272 57 0 270 223 233 245 157 0\n273 -39 0 271 217 109 0\n274 -17 0 272 30 0\n275 -51 0 272 33 0\n276 -58 0 272 36 0\n277 79 0 275 261 244 228 152 0\n278 54 0 276 242 259 150 0\n279 -62 0 277 84 0\n280 -28 0 278 28 0\n281 -29 0 278 29 0\n282 63 0 279 274 243 260 151 0\n283 40 0 280 273 269 224 156 0\n284 -18 0 282 40 0\n285 -34 0 283 21 0\n286 0 285 284 241 281 253 153 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record004
