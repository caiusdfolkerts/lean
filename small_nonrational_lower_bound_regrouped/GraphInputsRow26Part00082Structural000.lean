module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00082Data
public import GraphInputsRow26Part00082Frames
public import GraphInputsRow26Part00082Leaves
public import GraphInputsRow26Part00082Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

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
#print axioms local_excluded
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
#print axioms local_excluded
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
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record015
