module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00041Data
public import GraphInputsRow29Part00041Frames
public import GraphInputsRow29Part00041Leaves
public import GraphInputsRow29Part00041Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 37383395344384, (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), (certNat% 13), (certNat% 14)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 12), (certNat% 16), (certNat% 14)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 19), (certNat% 3), (certNat% 20)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 246290604621824, (certNat% 16), (certNat% 22), (certNat% 14)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), (certNat% 25), (certNat% 26), 70866960384]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 24), (certNat% 14), (certNat% 28), (certNat% 29), 70866960384]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c13 c0
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c16 c17
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c16 c18
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), 74766790688768, (certNat% 31), (certNat% 32), (certNat% 4)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), (certNat% 35), (certNat% 36), (certNat% 37)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 34), (certNat% 8), (certNat% 36), (certNat% 39), (certNat% 40)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c24 c21
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c16 c15
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c16 c26
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c16 c27
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c16 c28
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 3), (certNat% 42), (certNat% 43)]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 4), (certNat% 34), (certNat% 31), (certNat% 45)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 47), (certNat% 48), (certNat% 34), (certNat% 49), (certNat% 5)]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c16 c15
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c16 c36
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c16 c37
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨107, by decide⟩ c16 c38
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), 105553116266496, (certNat% 19), (certNat% 51)]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 49), (certNat% 5), 215504279044096, (certNat% 53)]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c42 c41
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), (certNat% 9), (certNat% 36), (certNat% 8), (certNat% 55), (certNat% 45)]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), (certNat% 58), (certNat% 59), (certNat% 60)]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 62), (certNat% 63), (certNat% 64), 268435456]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 58), (certNat% 60), (certNat% 66), 275146342400, (certNat% 67)]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c48 c47
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c49 c46
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 59), (certNat% 69), (certNat% 14)]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), (certNat% 62), (certNat% 72), (certNat% 73)]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c52 c51
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 75), (certNat% 76), (certNat% 77), (certNat% 78), 70369012613120]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c54 c53
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), (certNat% 80), (certNat% 81), (certNat% 82), 1152921504606846976]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), 215504279044096, (certNat% 47), (certNat% 84), (certNat% 85), (certNat% 86)]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c57 c56
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), (certNat% 88), (certNat% 51), (certNat% 53), (certNat% 89)]
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 90), (certNat% 51), (certNat% 53), (certNat% 91), (certNat% 92), (certNat% 93)]
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c60 c59
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 94), (certNat% 86), (certNat% 91), 4648739457204224, (certNat% 95), (certNat% 96)]
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), (certNat% 60), (certNat% 45), (certNat% 84), (certNat% 98)]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 99), (certNat% 88), (certNat% 100), (certNat% 91), (certNat% 101)]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 102), 387028629848064, (certNat% 67), (certNat% 48), (certNat% 51), (certNat% 73)]
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c65 c64
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c66 c63
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 103), (certNat% 24), (certNat% 104), (certNat% 86), (certNat% 95), (certNat% 105)]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 106), (certNat% 71), (certNat% 62), (certNat% 67), (certNat% 107), (certNat% 37)]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 108), (certNat% 48), (certNat% 109), (certNat% 8), (certNat% 110), (certNat% 77)]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 111), (certNat% 112), (certNat% 113), (certNat% 67), (certNat% 95), (certNat% 114)]
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 115), (certNat% 116), (certNat% 107), (certNat% 117), (certNat% 67), (certNat% 37)]
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 118), (certNat% 84), (certNat% 95), (certNat% 107), (certNat% 100), (certNat% 119), (certNat% 120)]
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c73 c72
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c74 c71
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c75 c70
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c76 c69
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c77 c68
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c78 c67
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c79 c62
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c80 c61
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c81 c58
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c82 c55
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c83 c50
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c84 c45
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c85 c35
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c86 c25
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c87 c14
  c88
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004
def vertexColumn : Fields := ⟨10, (certNat% 121)⟩
def kindColumn : Fields := ⟨3, (certNat% 122)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨78, by decide⟩, ⟨83, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨99, by decide⟩, ⟨102, by decide⟩, ⟨106, by decide⟩, ⟨109, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 123), (certNat% 124), (certNat% 125), (certNat% 126), 36028797018963968]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 127), 54078379900534784, (certNat% 128), (certNat% 129), 144115188075855872]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 130), 1759218604441600, 180143985094819840, (certNat% 128), (certNat% 131)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 132), 1759218872877056, (certNat% 133), (certNat% 134), 146366987889541120, (certNat% 135)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 136), (certNat% 125), (certNat% 124), 2814749767106560, (certNat% 137)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 138), 54078379900534784, 2814749767106560, (certNat% 139), (certNat% 140)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 141), (certNat% 125), 1759218604441600, 2251799813685248, 18049582881570816]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 142), (certNat% 143), 18049862054445056, (certNat% 144), (certNat% 145), (certNat% 146)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c11 c9
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c12 c8
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c13 c7
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 147), (certNat% 124), (certNat% 125), (certNat% 148), (certNat% 149)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 150), (certNat% 151), (certNat% 129), (certNat% 128), (certNat% 59)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 152), (certNat% 153), (certNat% 129), (certNat% 43), (certNat% 154)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 155), (certNat% 156), (certNat% 133), (certNat% 157), (certNat% 158), (certNat% 159)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 160), 2533274790395904, (certNat% 161), (certNat% 162)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 163), 18331057858281472, (certNat% 164), (certNat% 140), (certNat% 162)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 165), (certNat% 131), 316659348799488, (certNat% 124), (certNat% 137)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 166), (certNat% 167), (certNat% 168), 36063981391052800, (certNat% 169), (certNat% 170)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c27 c24
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 171), (certNat% 172), (certNat% 173), 1970324836974592, (certNat% 174), (certNat% 131)]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 175), (certNat% 176), (certNat% 177), (certNat% 178), (certNat% 179), (certNat% 180), 949978046398464]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c31 c28
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c32 c21
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c33 c14
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c34 c6
  c35
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record004
