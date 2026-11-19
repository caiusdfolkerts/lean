module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00084Data
public import GraphInputsRow26Part00084Frames
public import GraphInputsRow26Part00084Leaves
public import GraphInputsRow26Part00084Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00084.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 37260250042073088, (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 5), 144125633436319744, (certNat% 10)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), (certNat% 13), 37154696925806592, 144123984168878080, (certNat% 14)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), (certNat% 17), 144123984168878080, 37154696925806592, (certNat% 9)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 18), (certNat% 19)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), 37154696925806592, 144123984168878080, (certNat% 3)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 23), (certNat% 24)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), (certNat% 27), 144123984168878080, 37154696925806592, (certNat% 5)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c4 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 28), (certNat% 29), (certNat% 30)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c13 c9
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c14 c6
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c15 c1
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c16 c0
  c17
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00084.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00084.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006
def vertexColumn : Fields := ⟨10, (certNat% 31)⟩
def kindColumn : Fields := ⟨3, (certNat% 32)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 1441154079781814272, (certNat% 34), (certNat% 35), 61572651155456]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), (certNat% 37), (certNat% 38), 53326313947136, 180143985094819840, (certNat% 39)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c3 c4
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c3 c5
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 864693327478390784, (certNat% 41), (certNat% 42), 61572651155456]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), (certNat% 45), 44049184587776, 5629499534213120, (certNat% 46)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c3 c9
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c3 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c3 c11
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 48), (certNat% 49), (certNat% 50)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 52), (certNat% 49), 6917529027641081856]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 54), (certNat% 55)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), 108086940812705792, (certNat% 55), (certNat% 50), (certNat% 57)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), (certNat% 59), (certNat% 60), (certNat% 61), (certNat% 62), 16140901064495857664]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c3 c21
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c3 c22
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 63), (certNat% 64)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 65), (certNat% 66), (certNat% 67)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c27 c12
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c28 c6
  c29
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00084.record006
