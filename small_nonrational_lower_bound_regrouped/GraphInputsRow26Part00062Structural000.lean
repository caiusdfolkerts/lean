module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00062Data
public import GraphInputsRow26Part00062Frames
public import GraphInputsRow26Part00062Leaves
public import GraphInputsRow26Part00062Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 2251799813685248, 2341871806232657920, (certNat% 3)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 74309393985830912, (certNat% 5), (certNat% 6), 45035996273704960]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 4613937886960549888, (certNat% 8), (certNat% 9), 2882303761517117440]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 5188146770730811392, 117093590311632896, 2251799824171008, 141150610522112]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 81064793292668928, 7493989779944505344, 2251799824171008, 141150610522112]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 141150612619264, 117093590328410112, 7493989797124374528, 2251868675768320, 1100585369600]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c9 c2
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record017
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017
def vertexColumn : Fields := ⟨10, (certNat% 13)⟩
def kindColumn : Fields := ⟨3, (certNat% 14)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 1224979099718516736, (certNat% 16), (certNat% 17)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 1224979099718516736, (certNat% 19), 2989303529472, (certNat% 20)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4580169634145107968, 2989316112384, (certNat% 21), (certNat% 22), 1374389534720]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 19), (certNat% 24), 72066391238246400, 900719925474099200]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), (certNat% 27), 2989318209536, (certNat% 28)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 30), 549776785408, 4294967296]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), 3350678122763649024, (certNat% 32), 2886238994432, (certNat% 33)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), 4503599627370496000, 15573450752, (certNat% 36), 2989316112384]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c13 c2
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record017

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019
def vertexColumn : Fields := ⟨10, (certNat% 37)⟩
def kindColumn : Fields := ⟨3, (certNat% 38)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨61, by decide⟩, ⟨76, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), 25895697857511424, (certNat% 40), (certNat% 41), 9007199338627072, 183762944]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020
def vertexColumn : Fields := ⟨10, (certNat% 42)⟩
def kindColumn : Fields := ⟨3, (certNat% 43)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 45), 3314649325744685056, (certNat% 46), (certNat% 47)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 49), (certNat% 45), (certNat% 50)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 52), 1873497444986126336, (certNat% 53)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 1008806316530991104, (certNat% 55), (certNat% 56), (certNat% 57)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), (certNat% 52), 3602879701896396800, (certNat% 53)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), 2738188573441261568, (certNat% 55), (certNat% 56), (certNat% 57)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 60), (certNat% 61), (certNat% 62)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 64), (certNat% 65)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), (certNat% 67), (certNat% 68), (certNat% 69)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 55), (certNat% 46), (certNat% 45)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 71), (certNat% 72)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), (certNat% 68), (certNat% 55), (certNat% 74)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), (certNat% 46), (certNat% 49), (certNat% 76), (certNat% 77)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), (certNat% 79), (certNat% 55), (certNat% 57), (certNat% 56)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 80), (certNat% 81), 4179340454199820288, (certNat% 77), (certNat% 82)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), (certNat% 84), (certNat% 77), (certNat% 49), (certNat% 82)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), 3026418949592973312, (certNat% 52), (certNat% 86), (certNat% 87)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 88), (certNat% 86), 4179340454199951360, (certNat% 89), (certNat% 90), (certNat% 91)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨16, by decide⟩ c28 c25
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c29 c24
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c30 c23
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨20, by decide⟩ c31 c22
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c32 c9
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c33 c5
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c34 c0
  c35
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record020
