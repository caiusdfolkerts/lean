module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00292Data
public import GraphInputsRow29Part00292Frames
public import GraphInputsRow29Part00292Leaves
public import GraphInputsRow29Part00292Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00292.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨92, by decide⟩, ⟨95, by decide⟩, ⟨102, by decide⟩, ⟨105, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨116, by decide⟩, ⟨123, by decide⟩, ⟨125, by decide⟩, ⟨128, by decide⟩, ⟨136, by decide⟩, ⟨137, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 31336081391616]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), 63050394783186944]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 64176294690029568, (certNat% 11), (certNat% 12), 30786325577728]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 15), (certNat% 16), 14293651161088]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 14671883161042944, (certNat% 18), (certNat% 8), (certNat% 19)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 23089744183296, 27021597764222976, (certNat% 11), (certNat% 12)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 4505798650626048, 23347442221056, 28675263252398080, (certNat% 11), (certNat% 12)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨105, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨116, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c11 c0
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), 66428102019907584, (certNat% 24), (certNat% 25)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), (certNat% 3), (certNat% 5), 31336081391616]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), 32651097298436096, (certNat% 29), 17042430230528, (certNat% 30)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), (certNat% 33)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), (certNat% 36), (certNat% 37)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), (certNat% 27), 21990232555520, (certNat% 7)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 18), 49574780273164288, (certNat% 41), (certNat% 42)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), 21440476741632, (certNat% 29), (certNat% 45)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 47), (certNat% 29), 25838523252736, (certNat% 18)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 49), (certNat% 42), (certNat% 11), 21990232555520]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), 22553182508941312, (certNat% 30), (certNat% 51), (certNat% 42)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 53), 7146825580544, (certNat% 47)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), (certNat% 47), (certNat% 55), 7146825580544, (certNat% 56)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 47), 58581979527905280, (certNat% 51), (certNat% 58)]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), (certNat% 60), 6047313952768, (certNat% 61)]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), (certNat% 63), (certNat% 64), 54043195528445952]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), 1649267441664, 54043195528445952, (certNat% 61), (certNat% 66)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c33 c30
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 68), 58581979527905280, 72550175247171584, (certNat% 69)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), 72550175247171584, 18014398509481984, (certNat% 61)]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), (certNat% 61), (certNat% 47), (certNat% 66), 3848290697216]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), 4505798650626048, 54570961109778432, (certNat% 74), (certNat% 61), 1649267441664]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c38 c37
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c39 c36
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c40 c35
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c41 c34
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c42 c29
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c43 c28
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c44 c25
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨113, by decide⟩ c45 c24
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c46 c23
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c47 c22
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c48 c21
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c49 c20
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c50 c15
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c51 c14
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), (certNat% 76), 66428094503714816]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 78), (certNat% 79), (certNat% 80), 66428100946165760, (certNat% 64)]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c54 c53
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 81), 34634616274944, 70931694131085312, (certNat% 82)]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), (certNat% 84), (certNat% 85), (certNat% 86), (certNat% 12), 66428094503714816]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), (certNat% 88), 32435593019392]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 89), (certNat% 76), 32504312496128, 66885491340869632, (certNat% 90)]
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c59 c58
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 91), (certNat% 92), (certNat% 84), (certNat% 85), (certNat% 12), 66428094503714816]
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 93), (certNat% 94), (certNat% 95), (certNat% 96), (certNat% 11), 32435593019392]
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), (certNat% 98), (certNat% 99), 34635153145856, (certNat% 100), (certNat% 101), 70931694131085312]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c63 c62
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c64 c61
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c65 c60
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c66 c57
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c67 c56
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c68 c55
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨128, by decide⟩ c69 c52
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c70 c13
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨125, by decide⟩ c71 c12
  c72
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00292.record003
