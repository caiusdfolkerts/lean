module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00046Data
public import GraphInputsRow29Part00046Frames
public import GraphInputsRow29Part00046Leaves
public import GraphInputsRow29Part00046Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

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
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ea178ad274ab0ec1f3a2ccab29c972e2b2aaa9aa5a8ea5693a1eb16a5a56c3a8e3391e17ba1cc6b15c5a95a4e9565391e6a539715a56352d475334ad1b51d1743de0f23a8da358ce3c4e9354e334ccb31cd8b52ccb4acab1ad1b16c3bc1e8731e1745c9743c1fcc312a1a161588e139311c5292a4691548d1351314d0b22c4b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6d36db6db6da49a4d34d249a4db6da4934db6db4d34d2492493692492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 26), (facetIndex 30), (facetIndex 80), (facetIndex 83)]))
 (.leaf ([(facetIndex 43), (facetIndex 47), (facetIndex 75), (facetIndex 97)])))
 (.branch 3
 (.leaf ([(facetIndex 27), (facetIndex 28), (facetIndex 82), (facetIndex 84)]))
 (.leaf ([(facetIndex 41), (facetIndex 45), (facetIndex 60), (facetIndex 73)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 57), (facetIndex 58), (facetIndex 70), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 24), (facetIndex 25), (facetIndex 29), (facetIndex 38), (facetIndex 59), (facetIndex 79)])))
 (.branch 7
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 39), (facetIndex 40)]))
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 55), (facetIndex 67), (facetIndex 68), (facetIndex 77)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "8000000002080a3821c907e00003b20e0000021821ed76df802a42dz12;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 81), (facetIndex 91), (facetIndex 93), (facetIndex 101)]))
 (.branch 2
 (.leaf ([(facetIndex 54), (facetIndex 61), (facetIndex 62), (facetIndex 65), (facetIndex 102)]))
 (.leaf ([(facetIndex 32), (facetIndex 56), (facetIndex 69), (facetIndex 99)]))))
 (.branch 4
 (.leaf ([(facetIndex 78), (facetIndex 85), (facetIndex 87)]))
 (.branch 5
 (.leaf ([(facetIndex 66), (facetIndex 100), (facetIndex 103)]))
 (.leaf ([(facetIndex 49), (facetIndex 86), (facetIndex 104)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 31), (facetIndex 44), (facetIndex 46), (facetIndex 53)]))
 (.branch 8
 (.leaf ([(facetIndex 51), (facetIndex 63), (facetIndex 64), (facetIndex 76)]))
 (.leaf ([(facetIndex 42), (facetIndex 52), (facetIndex 74)]))))
 (.branch 10
 (.leaf ([(facetIndex 48), (facetIndex 50), (facetIndex 89), (facetIndex 92), (facetIndex 95), (facetIndex 96)]))
 (.branch 11
 (.leaf ([(facetIndex 90), (facetIndex 105)]))
 (.leaf ([(facetIndex 88), (facetIndex 94), (facetIndex 98)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "a541042b099b090a9b353000000307080000200417711000020168795906060800000000026z1f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
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
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1, 2]
def grouped3_0017 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0019 : List Nat := [1]
def grouped3_0020 : List Nat := [1, 2]
def grouped3_0021 : List Nat := [2]
def grouped3_0022 : List Nat := [3]
def grouped3_0023 : List Nat := [3, 4, 5]
def grouped3_0024 : List Nat := [4]
def grouped3_0025 : List Nat := [4, 5]
def grouped3_0026 : List Nat := [5]
def grouped3_0027 : List Nat := [6]
def grouped3_0028 : List Nat := [6, 7, 8]
def grouped3_0029 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0030 : List Nat := [7]
def grouped3_0031 : List Nat := [7, 8]
def grouped3_0032 : List Nat := [8]
def grouped3_0033 : List Nat := [9]
def grouped3_0034 : List Nat := [9, 10, 11]
def grouped3_0035 : List Nat := [10]
def grouped3_0036 : List Nat := [10, 11]
def grouped3_0037 : List Nat := [11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0031\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0031\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0036\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0034\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0029\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0029\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record004" 90

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record004" "{\"ridges\":[[23,560],[23,800],[42,178],[44,547],[47,770],[47,784],[51,672],[52,547],[62,549],[66,549],[70,104],[71,104],[72,296],[74,657],[74,672],[75,560],[75,800],[76,672],[81,780],[91,554],[92,554],[95,610],[96,178],[97,560],[97,770],[97,800],[98,672],[101,556],[102,612],[103,180],[105,672],[105,904]],\"owners\":[[70,104,[85,89,99,104],[12,35,57,67,71,88,100]],[71,104,[85,88,99,100],[12,35,57,67,70,89,104]],[72,296,[86,89,92,104],[14,37,68,71,90,105]],[47,770,[81,92,93,98],[22,31,52,53,84,97]],[97,770,[31,53,81,93],[22,47,52,84,92,98]],[47,784,[23],[22,64,75,84]],[23,560,[44,62,74,95,96,102,103],[75,97]],[75,560,[95,96,102,103],[23,44,62,74,97]],[97,560,[62,74,102,103],[23,44,75,95,96]],[23,800,[52,76,92,98,105],[75,97]],[75,800,[92,98,105],[23,52,76,97]],[97,800,[76,105],[23,52,75,92,98]],[42,178,[96],[]],[96,178,[42],[]],[44,547,[51,52],[]],[52,547,[44,51],[]],[74,657,[46,63],[]],[51,672,[101,103,105],[66,74,76,91,96,98]],[74,672,[91,98,101,105],[51,66,76,96,103]],[76,672,[91,96,101,103],[51,66,74,98,105]],[98,672,[66,74,101,103],[51,76,91,96,105]],[105,672,[51,66,74,96,103],[76,91,98,101]],[103,180,[61],[]],[62,549,[66],[]],[66,549,[62],[]],[81,780,[],[]],[91,554,[92],[]],[92,554,[91],[]],[105,904,[93],[]],[95,610,[],[]],[101,556,[],[]],[102,612,[],[]]],\"edges\":[[38,[23,44,51,52,62,66,74,75,76,91,92,95,96,97,98,101,102,103,105]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-8],[-10,-9],[-12,-6],[-12,-10],[-15,-10],[-15,-14],[-16,-10],[-22,-20],[-24,-14],[-24,-20],[-28,-22],[-29,-2],[-29,-14],[-29,-17],[-30,-29],[-38,-10],[-42,-3],[-42,-4],[-42,-5],[-42,-8],[-42,-37],[-43,-10],[-48,-18],[-48,-19],[-48,-44],[-48,-45],[-50,-7],[-25,33,36,44,49],[-26,33,35,44,45],[-27,34,36,38,49],[-14,32,38,39,43],[-42,2,17,32,39],[-14,1],[-1,11,22,29,40,41,47,48],[-30,40,41,47,48],[-42,22,29,47,48],[-1,16,31,38,43,50],[-30,38,43,50],[-42,31,50],[-9,41],[-41,9],[-11,15,16],[-16,11,15],[-29,13,23],[-15,46,48,50],[-29,37,43,46,50],[-31,37,41,46,48],[-43,24,29,46,48],[-50,15,24,29,41,48],[-48,21],[-22,24],[-24,22],[-32],[-37,38],[-38,37],[-50,39],[-40],[-46],[-47],[-51,10,14,30,42],[-52,8,12,20,28],[-53,18,19,25,26,27],[-54,3,4,5,6,7],[-55,51],[-56,52],[-57,55],[-57,56],[-58,53],[-59,54],[-60,58],[-60,59],[-61,57],[-61,60],[61],[-37,62],[-39,62],[-21,63],[-22,63],[-33,64],[-24,65],[-48,65],[-34,66],[-49,66],[-11,67],[-13,67],[-15,68],[-23,68],[-69,9,16,29],[-9,69],[-16,69],[-29,69],[-36,70],[-41,70],[-35,71],[-63,72],[-72,73],[-62,73],[-62,-72,74],[-65,75],[-65,-66,76],[-75,77],[-76,78],[-64,-75,78],[-77,79],[-73,79],[-73,-77,80],[-73,-78,81],[-74,-77,81],[-69,82],[-68,-69,83],[-82,84],[-83,85],[-67,-82,85],[-71,86],[-86,87],[-70,87],[-87,88],[-84,-87,89],[-85,89],[-79,-89,90],[-80,-88,90],[-81,90],[-90],[1,11,15,16,22,24,29,30,31,37,38,40,41,42,43,46,47,48,50]],\"atoms\":[{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":42},{\"tag\":\"incompatible\",\"a\":45,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":43},{\"tag\":\"incompatible\",\"a\":51,\"b\":43},{\"tag\":\"incompatible\",\"a\":51,\"b\":47},{\"tag\":\"incompatible\",\"a\":52,\"b\":43},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":66,\"b\":47},{\"tag\":\"incompatible\",\"a\":66,\"b\":60},{\"tag\":\"incompatible\",\"a\":73,\"b\":62},{\"tag\":\"incompatible\",\"a\":74,\"b\":31},{\"tag\":\"incompatible\",\"a\":74,\"b\":47},{\"tag\":\"incompatible\",\"a\":74,\"b\":53},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":92,\"b\":43},{\"tag\":\"incompatible\",\"a\":97,\"b\":35},{\"tag\":\"incompatible\",\"a\":97,\"b\":36},{\"tag\":\"incompatible\",\"a\":97,\"b\":37},{\"tag\":\"incompatible\",\"a\":97,\"b\":41},{\"tag\":\"incompatible\",\"a\":97,\"b\":91},{\"tag\":\"incompatible\",\"a\":98,\"b\":43},{\"tag\":\"incompatible\",\"a\":103,\"b\":57},{\"tag\":\"incompatible\",\"a\":103,\"b\":58},{\"tag\":\"incompatible\",\"a\":103,\"b\":99},{\"tag\":\"incompatible\",\"a\":103,\"b\":100},{\"tag\":\"incompatible\",\"a\":105,\"b\":40},{\"tag\":\"mate\",\"ridge\":104,\"a\":70,\"owners\":[85,89,99,104]},{\"tag\":\"mate\",\"ridge\":104,\"a\":71,\"owners\":[85,88,99,100]},{\"tag\":\"mate\",\"ridge\":296,\"a\":72,\"owners\":[86,89,92,104]},{\"tag\":\"mate\",\"ridge\":770,\"a\":47,\"owners\":[81,92,93,98]},{\"tag\":\"mate\",\"ridge\":770,\"a\":97,\"owners\":[31,53,81,93]},{\"tag\":\"mate\",\"ridge\":784,\"a\":47,\"owners\":[23]},{\"tag\":\"mate\",\"ridge\":560,\"a\":23,\"owners\":[44,62,74,95,96,102,103]},{\"tag\":\"mate\",\"ridge\":560,\"a\":75,\"owners\":[95,96,102,103]},{\"tag\":\"mate\",\"ridge\":560,\"a\":97,\"owners\":[62,74,102,103]},{\"tag\":\"mate\",\"ridge\":800,\"a\":23,\"owners\":[52,76,92,98,105]},{\"tag\":\"mate\",\"ridge\":800,\"a\":75,\"owners\":[92,98,105]},{\"tag\":\"mate\",\"ridge\":800,\"a\":97,\"owners\":[76,105]},{\"tag\":\"mate\",\"ridge\":178,\"a\":42,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":178,\"a\":96,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":547,\"a\":44,\"owners\":[51,52]},{\"tag\":\"mate\",\"ridge\":547,\"a\":52,\"owners\":[44,51]},{\"tag\":\"mate\",\"ridge\":657,\"a\":74,\"owners\":[46,63]},{\"tag\":\"mate\",\"ridge\":672,\"a\":51,\"owners\":[101,103,105]},{\"tag\":\"mate\",\"ridge\":672,\"a\":74,\"owners\":[91,98,101,105]},{\"tag\":\"mate\",\"ridge\":672,\"a\":76,\"owners\":[91,96,101,103]},{\"tag\":\"mate\",\"ridge\":672,\"a\":98,\"owners\":[66,74,101,103]},{\"tag\":\"mate\",\"ridge\":672,\"a\":105,\"owners\":[51,66,74,96,103]},{\"tag\":\"mate\",\"ridge\":180,\"a\":103,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":549,\"a\":62,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":549,\"a\":66,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":780,\"a\":81,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":554,\"a\":91,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":554,\"a\":92,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":904,\"a\":105,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":610,\"a\":95,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":556,\"a\":101,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":612,\"a\":102,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[43,47,75,97],\"full_literals\":[-51,10,14,30,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[41,45,60,73],\"full_literals\":[-52,8,12,20,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[57,58,70,71,72],\"full_literals\":[-53,18,19,25,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[35,36,37,39,40],\"full_literals\":[-54,3,4,5,6,7]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-57,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-60,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-61,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-61,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":91,\"full_literals\":[-37,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":93,\"full_literals\":[-39,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":61,\"full_literals\":[-21,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":62,\"full_literals\":[-22,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":85,\"full_literals\":[-33,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":66,\"full_literals\":[-24,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":103,\"full_literals\":[-48,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":86,\"full_literals\":[-34,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":104,\"full_literals\":[-49,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":44,\"full_literals\":[-11,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":46,\"full_literals\":[-13,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":51,\"full_literals\":[-15,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":63,\"full_literals\":[-23,68]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[42,52,74],\"full_literals\":[-69,9,16,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":42,\"full_literals\":[-9,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":52,\"full_literals\":[-16,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":74,\"full_literals\":[-29,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":89,\"full_literals\":[-36,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":96,\"full_literals\":[-41,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":88,\"full_literals\":[-35,71]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-62,-72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-66,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-76,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-75,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-73,-77,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-73,-78,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0017\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-74,-77,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0030\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0031\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0030\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0031\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-69,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-82,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-83,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-67,-82,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0035\",\"right_name\":\"grouped3_0037\",\"joined_name\":\"grouped3_0036\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0033\",\"right_name\":\"grouped3_0036\",\"joined_name\":\"grouped3_0034\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-86,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0033\",\"right_name\":\"grouped3_0036\",\"joined_name\":\"grouped3_0034\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0028\",\"right_name\":\"grouped3_0034\",\"joined_name\":\"grouped3_0029\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0028\",\"right_name\":\"grouped3_0034\",\"joined_name\":\"grouped3_0029\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-84,-87,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0028\",\"right_name\":\"grouped3_0034\",\"joined_name\":\"grouped3_0029\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-79,-89,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-80,-88,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,90],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[23,44,51,52,62,66,74,75,76,91,92,95,96,97,98,101,102,103,105]}]}"
  "125 57 0 74 72 0\n126 60 0 74 73 0\n127 55 0 125 66 0\n128 56 0 125 67 0\n129 58 0 126 70 0\n130 59 0 126 71 0\n131 51 0 127 64 0\n132 52 0 128 65 0\n133 53 0 129 68 0\n134 54 0 130 69 0\n135 -81 0 123 122 0\n136 1 11 15 16 22 24 29 30 31 37 38 41 42 43 48 50 0 57 58 59 124 0\n137 69 79 0 58 59 57 105 97 76 56 104 101 99 81 45 75 55 96 95 78 80 89 90 91 41 42 48 36 47 35 34 136 0\n138 29 79 0 58 59 53 131 137 105 97 76 56 75 55 96 95 78 104 101 99 81 80 48 36 38 31 60 2 7 88 0\n139 79 0 58 53 131 105 97 75 76 56 138 12 13 14 15 46 32 22 60 0\n140 -89 0 139 123 120 0\n141 -85 0 140 119 0\n142 -83 0 141 112 0\n143 -69 0 142 141 140 109 110 111 113 86 87 118 84 85 116 43 44 93 88 40 0\n144 -9 0 143 89 0\n145 -16 0 143 90 0\n146 -29 0 143 91 0\n147 -41 0 144 41 0\n148 50 24 38 42 43 48 0 57 59 58 147 146 145 51 54 47 35 45 37 42 136 0\n149 -15 42 30 0 131 5 6 60 0\n150 24 38 42 43 48 0 57 59 147 146 35 149 148 49 0\n151 -24 42 30 0 131 132 9 10 52 60 11 1 4 61 0\n152 42 43 48 0 145 59 147 57 146 131 35 149 42 151 51 150 34 16 33 60 0\n153 -42 48 0 59 146 58 147 132 134 17 18 19 20 21 36 47 8 11 39 61 27 3 63 0\n154 48 0 147 59 57 58 146 35 153 151 152 48 0\n155 -18 0 154 23 0\n156 -19 0 154 24 0\n157 -44 0 154 25 0\n158 -45 0 154 26 0\n159 21 0 154 50 0\n160 65 0 154 81 0\n161 63 0 159 77 0\n162 75 0 160 99 0\n163 72 0 161 95 0\n164 77 0 162 101 0\n165 73 0 163 96 0\n166 -74 0 164 135 108 0\n167 80 0 165 164 106 0\n168 -78 0 165 135 107 0\n169 -62 0 166 163 98 0\n170 -88 0 167 123 121 0\n171 -76 0 168 102 0\n172 -64 0 168 162 103 0\n173 -37 0 169 75 0\n174 -87 0 170 117 0\n175 -66 0 171 160 100 0\n176 -33 0 172 79 0\n177 -38 0 173 55 0\n178 -86 0 174 115 0\n179 -70 0 174 116 0\n180 -34 0 175 82 0\n181 -49 0 175 83 0\n182 -71 0 178 114 0\n183 -36 0 179 92 0\n184 -27 0 181 183 177 180 30 0\n185 -25 0 181 183 176 157 28 0\n186 -35 0 182 94 0\n187 26 0 185 133 156 155 184 62 0\n188 0 187 186 176 157 158 29 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ea178ad274ab0ec1f1726a96a3a95a4e87ac5a963391e17ba1ac6715c789ca6a96a5693a5594e479a966539715a56558d4b51d70da34cd8b4ad1b51d1743de0da358ce3c4e9354d332cc7362d4b32d2b2ac6b46c5b0ef07a1cc785d1725d0f07f301588e13b21a87118c5311c5292a469a16151548d1351314d0b22c4b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6db6db4d24934924d24da4934d26934db6d349a4924926d2492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 48), (facetIndex 53)]))
 (.leaf ([(facetIndex 59), (facetIndex 62), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 88), (facetIndex 89)]))
 (.branch 4
 (.leaf ([(facetIndex 52), (facetIndex 103)]))
 (.leaf ([(facetIndex 54), (facetIndex 64), (facetIndex 69), (facetIndex 70), (facetIndex 99)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 97), (facetIndex 98), (facetIndex 100), (facetIndex 101)]))
 (.branch 7
 (.leaf ([(facetIndex 35), (facetIndex 56), (facetIndex 74)]))
 (.leaf ([(facetIndex 86), (facetIndex 90), (facetIndex 92)]))))
 (.branch 9
 (.leaf ([(facetIndex 51), (facetIndex 91), (facetIndex 102)]))
 (.branch 10
 (.leaf ([(facetIndex 45), (facetIndex 50), (facetIndex 94), (facetIndex 95)]))
 (.leaf ([(facetIndex 93), (facetIndex 96)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3855455a99a7872207000001000006000440000401001006040389000090000000006z23;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3, 4]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6, 7]
def grouped3_0012 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0013 : List Nat := [6]
def grouped3_0014 : List Nat := [6, 7]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [8, 9, 10]
def grouped3_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [9, 10]
def grouped3_0020 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record005" 89

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record005" "{\"ridges\":[[6,266],[12,532],[13,644],[14,104],[16,265],[17,112],[21,672],[28,266],[31,532],[33,644],[34,774],[37,266],[38,104],[40,266],[42,266],[43,266],[44,112],[53,898],[57,104],[59,556],[61,644],[62,780],[63,112],[65,532],[66,532],[67,532],[67,644],[68,532],[69,228],[70,612],[71,644],[71,672],[72,104],[73,265],[75,104],[76,104],[76,265],[77,296],[78,672],[79,296],[80,904],[81,112],[82,112],[83,672],[84,672],[88,658],[99,556],[101,180],[103,904]],\"owners\":[[16,265,[6,28,37,42,43,56,62,74,80],[73,76,77,79]],[73,265,[6,28,42,43,62,80],[16,37,56,74,76,77,79]],[76,265,[6,28,37,43,56,62,80],[16,42,73,74,77,79]],[6,266,[86,91,92,94,95],[28,37,40,42,43]],[28,266,[91,92,94,95],[6,37,40,42,43,86]],[37,266,[94,95],[6,28,40,42,43,86,91,92]],[40,266,[86,92],[6,28,37,42,43,91,94,95]],[42,266,[86,91,95],[6,28,37,40,43,92,94]],[43,266,[86,91,92,94],[6,28,37,40,42,95]],[12,532,[88,89,100,101],[31,65,66,67,68]],[31,532,[100,101],[12,65,66,67,68,88,89]],[65,532,[88,89],[12,31,66,67,68,100,101]],[66,532,[88,89,101],[12,31,65,67,68,100]],[67,532,[89,100],[12,31,65,66,68,88,101]],[68,532,[88,100,101],[12,31,65,66,67,89]],[13,644,[88,99,101],[33,61,67,71]],[33,644,[99,101],[13,61,67,71,88]],[61,644,[88,101],[13,33,67,71,99]],[67,644,[99],[13,33,61,71,88,101]],[71,644,[88],[13,33,61,67,99,101]],[14,104,[90,93,94,97,98,102],[38,57,72,75,76]],[38,104,[97,98,102],[14,57,72,75,76,90,93,94]],[57,104,[90,93,94,102],[14,38,72,75,76,97,98]],[72,104,[93,94,98],[14,38,57,75,76,90,97,102]],[75,104,[90,94,97,102],[14,38,57,72,76,93,98]],[76,104,[90,93,97,98],[14,38,57,72,75,94,102]],[77,296,[91,94,102],[16,40,73,76,79,95,103]],[79,296,[91,94,95,102],[16,40,73,76,77,103]],[17,112,[90,96,97,100,102],[44,63,72,81,82]],[44,112,[97,100,102],[17,63,72,81,82,90,96]],[63,112,[90,96,102],[17,44,72,81,82,97,100]],[81,112,[90,97,100],[17,44,63,72,82,96,102]],[82,112,[90,96,97,102],[17,44,63,72,81,100]],[21,672,[99,101,103],[71,78,83,84]],[71,672,[103],[21,78,83,84,99,101]],[78,672,[101],[21,71,83,84,99,103]],[83,672,[99,103],[21,71,78,84,101]],[84,672,[99,101],[21,71,78,83,103]],[34,774,[89],[]],[88,658,[48],[]],[53,898,[],[]],[59,556,[99],[]],[99,556,[59],[]],[62,780,[],[]],[101,180,[64],[]],[69,228,[98],[]],[70,612,[100],[]],[80,904,[103],[]],[103,904,[80],[]]],\"edges\":[[23,[12,13,31,33,34,59,61,62,65,66,67,68,70,71,88,89,99,100,101]],[28,[6,16,28,37,40,42,43,56,62,73,74,76,77,79,80,86,91,92,94,95,102,103]],[35,[14,17,38,44,50,51,57,63,69,70,72,75,76,81,82,90,93,94,96,97,98,100,102]],[43,[13,21,33,48,53,61,67,71,78,80,83,84,88,99,101,103]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-5,1,8,12,15,16,22,26,38,44],[-37,1,8,15,16,26,44],[-40,1,8,12,16,22,26,44],[-1,49,53,54,56,57],[-8,53,54,56,57],[-12,56,57],[-14,49,54],[-15,49,53,57],[-16,49,53,54,56],[-2,50,51,62,63],[-9,62,63],[-29,50,51],[-30,50,51,63],[-31,51,62],[-32,50,62,63],[-3,50,61,63],[-10,61,63],[-25,50,63],[-31,61],[-35,50],[-4,52,55,56,59,60,64],[-13,59,60,64],[-23,52,55,56,64],[-36,55,56,60],[-39,52,56,59,64],[-40,52,55,59,60],[-41,53,56,64],[-43,53,56,57,64],[-6,52,58,59,62,64],[-17,59,62,64],[-27,52,58,64],[-45,52,59,62],[-46,52,58,59,64],[-7,61,63,65],[-35,65],[-42,63],[-47,61,65],[-48,61,63],[-11,51],[-50,18],[-21],[-24,61],[-61,24],[-26],[-63,28],[-33,60],[-34,62],[-44,65],[-65,44],[-18,66],[-24,67],[-44,67],[-50,68],[-51,68],[-65,69],[-28,70],[-61,70],[-59,71],[-60,71],[-62,71],[-63,71],[-22,72],[-38,72],[-49,73],[-52,73],[-54,73],[-20,74],[-53,74],[-64,74],[-19,75],[-56,75],[-57,75],[-55,76],[-58,76],[-67,77],[-66,77],[-70,78],[-69,78],[-78,79],[-68,79],[-79,80],[-77,80],[-77,-79,81],[-73,82],[-72,82],[-82,83],[-71,83],[-71,-82,84],[-76,85],[-75,85],[-85,86],[-74,86],[-86,87],[-83,87],[-83,-86,88],[-84,88],[-80,-88,89],[-81,-87,89],[-89],[2,3,9,10,11,24,25,26,29,30,31,32,34,35,50,51,61,62,63],[1,5,8,12,14,15,16,22,26,37,38,40,41,43,44,49,53,54,56,57,64,65],[4,6,13,17,19,20,23,27,33,34,36,39,40,45,46,52,55,56,58,59,60,62,64],[3,7,10,18,21,25,31,35,42,44,47,48,50,61,63,65]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":265,\"a\":16,\"owners\":[6,28,37,42,43,56,62,74,80]},{\"tag\":\"mate\",\"ridge\":265,\"a\":73,\"owners\":[6,28,42,43,62,80]},{\"tag\":\"mate\",\"ridge\":265,\"a\":76,\"owners\":[6,28,37,43,56,62,80]},{\"tag\":\"mate\",\"ridge\":266,\"a\":6,\"owners\":[86,91,92,94,95]},{\"tag\":\"mate\",\"ridge\":266,\"a\":28,\"owners\":[91,92,94,95]},{\"tag\":\"mate\",\"ridge\":266,\"a\":37,\"owners\":[94,95]},{\"tag\":\"mate\",\"ridge\":266,\"a\":40,\"owners\":[86,92]},{\"tag\":\"mate\",\"ridge\":266,\"a\":42,\"owners\":[86,91,95]},{\"tag\":\"mate\",\"ridge\":266,\"a\":43,\"owners\":[86,91,92,94]},{\"tag\":\"mate\",\"ridge\":532,\"a\":12,\"owners\":[88,89,100,101]},{\"tag\":\"mate\",\"ridge\":532,\"a\":31,\"owners\":[100,101]},{\"tag\":\"mate\",\"ridge\":532,\"a\":65,\"owners\":[88,89]},{\"tag\":\"mate\",\"ridge\":532,\"a\":66,\"owners\":[88,89,101]},{\"tag\":\"mate\",\"ridge\":532,\"a\":67,\"owners\":[89,100]},{\"tag\":\"mate\",\"ridge\":532,\"a\":68,\"owners\":[88,100,101]},{\"tag\":\"mate\",\"ridge\":644,\"a\":13,\"owners\":[88,99,101]},{\"tag\":\"mate\",\"ridge\":644,\"a\":33,\"owners\":[99,101]},{\"tag\":\"mate\",\"ridge\":644,\"a\":61,\"owners\":[88,101]},{\"tag\":\"mate\",\"ridge\":644,\"a\":67,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":644,\"a\":71,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":104,\"a\":14,\"owners\":[90,93,94,97,98,102]},{\"tag\":\"mate\",\"ridge\":104,\"a\":38,\"owners\":[97,98,102]},{\"tag\":\"mate\",\"ridge\":104,\"a\":57,\"owners\":[90,93,94,102]},{\"tag\":\"mate\",\"ridge\":104,\"a\":72,\"owners\":[93,94,98]},{\"tag\":\"mate\",\"ridge\":104,\"a\":75,\"owners\":[90,94,97,102]},{\"tag\":\"mate\",\"ridge\":104,\"a\":76,\"owners\":[90,93,97,98]},{\"tag\":\"mate\",\"ridge\":296,\"a\":77,\"owners\":[91,94,102]},{\"tag\":\"mate\",\"ridge\":296,\"a\":79,\"owners\":[91,94,95,102]},{\"tag\":\"mate\",\"ridge\":112,\"a\":17,\"owners\":[90,96,97,100,102]},{\"tag\":\"mate\",\"ridge\":112,\"a\":44,\"owners\":[97,100,102]},{\"tag\":\"mate\",\"ridge\":112,\"a\":63,\"owners\":[90,96,102]},{\"tag\":\"mate\",\"ridge\":112,\"a\":81,\"owners\":[90,97,100]},{\"tag\":\"mate\",\"ridge\":112,\"a\":82,\"owners\":[90,96,97,102]},{\"tag\":\"mate\",\"ridge\":672,\"a\":21,\"owners\":[99,101,103]},{\"tag\":\"mate\",\"ridge\":672,\"a\":71,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":672,\"a\":78,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":672,\"a\":83,\"owners\":[99,103]},{\"tag\":\"mate\",\"ridge\":672,\"a\":84,\"owners\":[99,101]},{\"tag\":\"mate\",\"ridge\":774,\"a\":34,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":658,\"a\":88,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":898,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":556,\"a\":59,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":556,\"a\":99,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":780,\"a\":62,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":180,\"a\":101,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":228,\"a\":69,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":612,\"a\":70,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":904,\"a\":80,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":904,\"a\":103,\"owners\":[80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":48,\"full_literals\":[-18,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":59,\"full_literals\":[-24,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-44,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":88,\"full_literals\":[-50,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":89,\"full_literals\":[-51,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":103,\"full_literals\":[-65,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":64,\"full_literals\":[-28,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":99,\"full_literals\":[-61,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":97,\"full_literals\":[-59,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":98,\"full_literals\":[-60,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":100,\"full_literals\":[-62,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":101,\"full_literals\":[-63,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":56,\"full_literals\":[-22,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":74,\"full_literals\":[-38,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-49,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":90,\"full_literals\":[-52,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":92,\"full_literals\":[-54,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":51,\"full_literals\":[-20,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":91,\"full_literals\":[-53,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":102,\"full_literals\":[-64,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":50,\"full_literals\":[-19,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":94,\"full_literals\":[-56,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":95,\"full_literals\":[-57,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":93,\"full_literals\":[-55,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":96,\"full_literals\":[-58,76]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-79,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-77,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-77,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-73,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-82,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-82,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-76,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-85,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-86,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-83,false,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-83,-86,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-84,false,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-80,-88,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-81,-87,89],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[12,13,31,33,34,59,61,62,65,66,67,68,70,71,88,89,99,100,101]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[6,16,28,37,40,42,43,56,62,73,74,76,77,79,80,86,91,92,94,95,102,103]},{\"tag\":\"edge\",\"edge\":35,\"owners\":[14,17,38,44,50,51,57,63,69,70,72,75,76,81,82,90,93,94,96,97,98,100,102]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[13,21,33,48,53,61,67,71,78,80,83,84,88,99,101,103]}]}"
  "104 2 3 9 10 11 24 25 29 30 31 32 34 35 50 51 61 62 63 0 44 100 0\n105 1 5 8 12 14 15 16 22 37 38 40 41 43 44 49 53 54 56 57 64 65 0 44 101 0\n106 3 7 10 18 25 31 35 42 44 47 48 50 61 63 65 0 41 103 0\n107 80 0 81 82 79 80 75 76 77 78 53 52 50 56 57 55 20 45 19 34 37 38 16 36 18 17 106 0\n108 -88 0 107 99 97 0\n109 -84 0 108 96 0\n110 79 71 0 60 47 61 11 79 80 77 53 54 57 12 20 10 15 18 13 39 14 42 16 17 104 0\n111 71 81 0 61 36 110 83 75 76 51 52 50 43 49 40 19 34 37 38 16 17 35 18 106 0\n112 44 -71 0 109 108 44 87 95 92 68 88 84 64 91 90 72 8 66 71 4 9 5 69 28 27 6 7 85 63 62 49 2 1 3 105 0\n113 81 0 111 112 48 52 55 75 78 83 79 0\n114 -87 0 113 99 98 0\n115 -86 0 114 93 0\n116 -83 0 114 94 0\n117 -85 0 115 91 0\n118 -74 0 115 92 0\n119 -82 0 116 86 0\n120 -71 0 116 87 0\n121 -76 0 117 89 0\n122 -75 0 117 90 0\n123 -20 0 118 67 0\n124 -64 0 118 69 0\n125 -73 0 119 84 0\n126 -59 0 120 58 0\n127 -60 0 120 59 0\n128 -62 0 120 60 0\n129 -55 0 121 73 0\n130 -58 0 121 74 0\n131 -19 0 122 70 0\n132 -56 0 122 71 0\n133 -52 0 125 65 0\n134 -45 0 126 133 128 32 0\n135 -13 0 126 127 124 22 0\n136 -17 0 126 128 124 30 0\n137 -40 0 126 127 133 129 26 0\n138 -6 0 126 133 130 128 124 29 0\n139 -46 0 126 133 130 124 33 0\n140 -39 0 126 133 132 124 25 0\n141 -4 0 126 133 129 132 127 124 21 0\n142 -33 0 127 46 0\n143 -36 0 127 129 132 24 0\n144 -34 0 128 47 0\n145 -23 0 129 133 132 124 23 0\n146 -27 0 130 133 124 31 0\n147 0 138 142 141 135 136 131 123 146 145 144 143 140 137 134 139 133 129 132 130 126 127 128 124 102 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record005
