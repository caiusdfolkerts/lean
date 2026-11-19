module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00046Data
public import GraphInputsRow29Part00046Frames
public import GraphInputsRow29Part00046Leaves
public import GraphInputsRow29Part00046Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 598136472993792, (certNat% 4), (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 3), 598136472993792, (certNat% 7), (certNat% 5)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 10), (certNat% 11), 5066549580791808, 3377699720527872]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 879611449704448, (certNat% 13), (certNat% 14), (certNat% 15)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 4824657022681088, (certNat% 17), (certNat% 18), (certNat% 19)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), 5383208929591296, (certNat% 22), (certNat% 15)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), 5383208929591296, (certNat% 22), (certNat% 15)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 5383208929591296, (certNat% 27), (certNat% 19)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), 5383208929591296, (certNat% 22), (certNat% 15)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), 598136472993792, (certNat% 31), 7025615418832191488, (certNat% 32), (certNat% 33)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 7025615419100626944, 5383208929591296, (certNat% 27), (certNat% 35), (certNat% 22), (certNat% 36)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c16 c7
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c19 c4
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002
def vertexColumn : Fields := ⟨10, (certNat% 37)⟩
def kindColumn : Fields := ⟨3, (certNat% 38)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), (certNat% 41), 4611694814520410112, (certNat% 42)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), (certNat% 45), (certNat% 46), (certNat% 47), 10376330924856967168]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), 1275068416, (certNat% 49), (certNat% 50), (certNat% 51)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), 1207959552, (certNat% 47), (certNat% 53)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), (certNat% 55), (certNat% 47), (certNat% 51), (certNat% 53)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), (certNat% 58), (certNat% 59), (certNat% 60), (certNat% 61)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 62)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), 4611686018427387904, (certNat% 64)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c11 c15
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c11 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 66), 1152921508901814272]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), 1152921508901814272, (certNat% 64), 4611686018427387904]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 69), (certNat% 70), (certNat% 71), (certNat% 66)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), (certNat% 58), (certNat% 71), (certNat% 73), (certNat% 74), (certNat% 75)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c11 c10
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), (certNat% 77), 1207959552]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), 1207959552, 144115222435594240, 9223372036854775808]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), (certNat% 80), 1140850688, (certNat% 81), (certNat% 82)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), 1275068416, (certNat% 84), (certNat% 82), (certNat% 51)]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), (certNat% 86), (certNat% 80), (certNat% 87), (certNat% 88), (certNat% 89)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c36 c33
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 90), (certNat% 91), (certNat% 40), 144115222435594240, (certNat% 42)]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 92), (certNat% 93), 1140850688, (certNat% 94), (certNat% 95)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 96), (certNat% 97), (certNat% 98), (certNat% 99), (certNat% 100), (certNat% 66)]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c41 c38
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 101), (certNat% 102), (certNat% 47), (certNat% 103), 1811939328, 9223372036854775808]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 104), (certNat% 105), 1275068416, (certNat% 106), (certNat% 69), (certNat% 94)]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c11 c10
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 107), (certNat% 95), 216172782113783808]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 108), (certNat% 109), 216172782113783808, (certNat% 110)]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c48 c47
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 111), 216172782113783808, (certNat% 112), (certNat% 105), (certNat% 40)]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c50 c49
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 113), (certNat% 46), (certNat% 94), (certNat% 102), (certNat% 61), (certNat% 114)]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c52 c51
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 115), (certNat% 57), 14987979559889010688, (certNat% 116), 2080374784, 648518346341351424]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 117), (certNat% 80), 2080374784, 13835066851375185920, (certNat% 118), (certNat% 109)]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 119), (certNat% 114), (certNat% 64), (certNat% 120), (certNat% 121), 1275068416]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 122), 1369094286720630784, (certNat% 123), (certNat% 120), 1275068416, 576460752303423488]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 124), (certNat% 114), (certNat% 80), (certNat% 120), 9223372036988993536, 1140850688]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 125), 10376295740484878336, (certNat% 126), (certNat% 120), (certNat% 106), 1275068416, (certNat% 127)]
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c59 c58
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c60 c57
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c61 c56
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c62 c55
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c63 c54
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c64 c53
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c65 c44
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c66 c43
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c67 c42
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c68 c37
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c69 c26
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c70 c9
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c71 c2
  c72
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007
def vertexColumn : Fields := ⟨10, (certNat% 128)⟩
def kindColumn : Fields := ⟨3, (certNat% 129)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [1, 2, 3, 4]
def candidates : List (Fin raw.n) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c1 c2
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 130), 144115188075855872, (certNat% 131), (certNat% 132)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c4 c2
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c5 c3
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 133), (certNat% 134), (certNat% 135), (certNat% 136), (certNat% 137)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 138), (certNat% 139), 72066390130950144, (certNat% 140)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 141), (certNat% 134), (certNat% 136), (certNat% 142), 108086391056891904]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 143), 72070788177461248, (certNat% 140), (certNat% 144), (certNat% 145)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 146), (certNat% 147), (certNat% 148), (certNat% 140), 72057594037927936]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 149), (certNat% 148), (certNat% 136), (certNat% 150), (certNat% 151), (certNat% 152)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c17 c8
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 153)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c1 c19
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c1 c20
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .size 1
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c1 c22
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c1 c23
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c1 c24
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c1 c25
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c26 c21
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 154), 3298534883328, (certNat% 155), (certNat% 136)]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 156), (certNat% 136), (certNat% 157), 12094627905536, 72057594037927936]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 158), (certNat% 142), (certNat% 159), 12232066859008, (certNat% 160), 108086391056891904]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 161), (certNat% 162), (certNat% 163), (certNat% 151), 17042463784960, 34359738368]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 164), (certNat% 165), 1008806316581322752, (certNat% 166), (certNat% 167), 10445360463872]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 168), 90076424953659392, (certNat% 136), (certNat% 169), (certNat% 140), (certNat% 150)]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c1 c22
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c1 c37
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c1 c38
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c1 c39
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 170), (certNat% 171), (certNat% 172), (certNat% 173)]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c1 c0
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c1 c43
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c1 c44
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 174), (certNat% 172), (certNat% 175), (certNat% 173)]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 176), (certNat% 177), (certNat% 162), (certNat% 178), 1152921505680588800]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c48 c47
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c49 c42
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 179), (certNat% 180), (certNat% 181), 7696581394432]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 182), (certNat% 183), 1170935904190070784, (certNat% 181), (certNat% 180)]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 184), (certNat% 140), (certNat% 185), (certNat% 144), (certNat% 186)]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 187), 571746046443520, (certNat% 172), (certNat% 188)]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 189), (certNat% 190), (certNat% 167), (certNat% 191), 10995116277760]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c55 c54
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 192), (certNat% 172), 571746046443520, (certNat% 171), (certNat% 180)]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 193), 10995116277760, (certNat% 194), (certNat% 185), (certNat% 144), (certNat% 195)]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c58 c57
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c59 c56
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c60 c53
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c61 c52
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c62 c51
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c63 c50
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 196), (certNat% 197), (certNat% 144), (certNat% 198), 3848324251648, (certNat% 145)]
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c1 c19
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c1 c66
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c1 c67
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 199), 72057594037927936, (certNat% 200), (certNat% 157)]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c69 c68
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 201), 1152921504606846976, (certNat% 200), (certNat% 157)]
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c71 c44
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 202), 1152921505680588800, (certNat% 177), (certNat% 157), (certNat% 203)]
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c73 c72
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c74 c70
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 204), (certNat% 205), 1152921505680588800, (certNat% 206), (certNat% 207)]
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 208), 1152921504606846976, 3298534883328, (certNat% 191)]
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c77 c44
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 209), 1152921505680588800, 3298534883328, 72057594037927936]
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c1 c24
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 210), (certNat% 211), 3298534883328]
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c81 c80
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c1 c20
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c83 c83
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 212), (certNat% 139), (certNat% 213), 3298534883328]
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c85 c84
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c86 c82
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 214), 3298534883328, (certNat% 136), 72057628397666304, (certNat% 215)]
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c88 c87
  let c90 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c89 c79
  let c91 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c90 c78
  let c92 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 216), (certNat% 136), (certNat% 181), (certNat% 137), 16492674416640, 72057594037927936]
  let c93 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c92 c91
  let c94 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c93 c76
  let c95 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c94 c75
  let c96 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 217), 72064225467432960, (certNat% 135), (certNat% 218), (certNat% 160), 9895638204416]
  let c97 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 219), (certNat% 181), (certNat% 160), (certNat% 220), (certNat% 221), (certNat% 222)]
  let c98 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 223), (certNat% 224), (certNat% 162), (certNat% 157), (certNat% 222), (certNat% 225)]
  let c99 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 226), (certNat% 157), (certNat% 140), (certNat% 144), 7181185318912, (certNat% 227)]
  let c100 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 228), (certNat% 157), (certNat% 229), (certNat% 203), (certNat% 132), (certNat% 230)]
  let c101 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 231), (certNat% 181), (certNat% 135), (certNat% 232), (certNat% 233)]
  let c102 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 234), (certNat% 147), 13743895347200, (certNat% 218), 34359738368, (certNat% 203)]
  let c103 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 235), (certNat% 218), (certNat% 236), 4982162063360, (certNat% 134), (certNat% 237), (certNat% 230)]
  let c104 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c103 c102
  let c105 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c104 c101
  let c106 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c105 c100
  let c107 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c106 c99
  let c108 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c107 c98
  let c109 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c108 c97
  let c110 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c109 c96
  let c111 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c110 c95
  let c112 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c111 c65
  let c113 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c112 c64
  let c114 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c113 c36
  let c115 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c114 c35
  let c116 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c115 c34
  let c117 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c116 c33
  let c118 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c117 c18
  c118
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record007
