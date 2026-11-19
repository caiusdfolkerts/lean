module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00041Data
public import GraphInputsRow29Part00041Frames
public import GraphInputsRow29Part00041Leaves
public import GraphInputsRow29Part00041Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

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
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "358ae0bc1f352d2aaac6a5a56a3a1eb86c59564d876338ae1b85e0fb51ac749aa719a6659566392e479e1715a55352d475334ad1b49d1743de0f43a8f1394d538cd331cf0b92d4b32e2b1ae1b46c5b0ef07a1d8731d2719e1745c570dc8f13c2f07d54a28aa518a6c4551a24a9864590e5452951515435c0e8350ca382c8b12c2b41c8711c27"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6da6db6da6da6da6d249249a69269b49249a6da49249a492493492499249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 36), (facetIndex 71), (facetIndex 73)]))
 (.branch 2
 (.leaf ([(facetIndex 93), (facetIndex 94)]))
 (.leaf ([(facetIndex 64), (facetIndex 83)]))))
 (.branch 4
 (.leaf ([(facetIndex 104), (facetIndex 105)]))
 (.branch 5
 (.leaf ([(facetIndex 45), (facetIndex 57), (facetIndex 82)]))
 (.leaf ([(facetIndex 97), (facetIndex 98), (facetIndex 101)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 99), (facetIndex 102), (facetIndex 106)]))
 (.branch 8
 (.leaf ([(facetIndex 29), (facetIndex 65), (facetIndex 67)]))
 (.leaf ([(facetIndex 85), (facetIndex 87), (facetIndex 89)]))))
 (.branch 10
 (.leaf ([(facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 86)]))
 (.branch 11
 (.leaf ([(facetIndex 90), (facetIndex 91), (facetIndex 96)]))
 (.leaf ([(facetIndex 95), (facetIndex 103)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "633b650655ab110aa8089802400000000000000707200000040999000000040000000000000007z1d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [1, 2]
def grouped3_0006 : List Nat := [2]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4, 5]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [4, 5]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [7, 8]
def grouped3_0017 : List Nat := [8]
def grouped3_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [9, 10, 11]
def grouped3_0020 : List Nat := [10]
def grouped3_0021 : List Nat := [10, 11]
def grouped3_0022 : List Nat := [11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record003" 98

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record003" "{\"ridges\":[[5,74],[11,769],[11,770],[12,52],[17,56],[18,88],[19,536],[23,784],[31,74],[33,52],[36,534],[42,769],[42,770],[43,56],[44,88],[46,536],[47,74],[49,74],[50,74],[51,74],[52,770],[53,114],[54,306],[55,562],[57,594],[58,770],[58,784],[60,770],[61,769],[61,770],[62,52],[63,88],[64,156],[68,52],[69,52],[70,52],[71,660],[72,784],[74,56],[74,88],[75,56],[76,56],[76,536],[77,88],[78,88],[78,536],[79,536],[80,536],[80,784],[83,688],[84,784],[85,30],[86,30],[91,306],[96,562],[99,282],[102,594],[103,108],[104,156],[105,688],[106,840]],\"owners\":[[5,74,[86,87,89,95,97,98,101],[31,44,47,49,50,51]],[31,74,[95,97,98,101],[5,44,47,49,50,51,86,87,89]],[47,74,[86,89,97,98,101],[5,31,44,49,50,51,87,95]],[49,74,[86,87,95,97,98,101],[5,31,44,47,50,51,89]],[50,74,[86,87,89,95,98],[5,31,44,47,49,51,97,101]],[51,74,[86,87,89,95,97],[5,31,44,47,49,50,98,101]],[11,769,[23,72,73,80,82,84],[42,52,60,61]],[42,769,[23,80,82,84],[11,52,60,61,72,73]],[61,769,[23,72,80,82,84],[11,42,52,60,73]],[11,770,[93,94,99,101,102],[42,52,58,60,61]],[42,770,[99,101,102],[11,52,58,60,61,93,94]],[52,770,[93,94,102],[11,42,58,60,61,99,101]],[58,770,[94,101],[11,42,52,60,61,93,99,102]],[60,770,[93,94,99],[11,42,52,58,61,101,102]],[61,770,[93,99,101,102],[11,42,52,58,60,94]],[12,52,[85,90,91,103,104],[33,62,68,69,70]],[33,52,[103,104],[12,62,68,69,70,85,90,91]],[62,52,[90,91],[12,33,68,69,70,85,103,104]],[68,52,[85,91,104],[12,33,62,69,70,90,103]],[69,52,[85,90,91,103],[12,33,62,68,70,104]],[70,52,[85,90,103,104],[12,33,62,68,69,91]],[17,56,[85,95,96,103,104,105],[43,62,74,75,76]],[43,56,[103,104,105],[17,62,74,75,76,85,95,96]],[74,56,[85,96,104,105],[17,43,62,75,76,95,103]],[75,56,[85,95,96,103],[17,43,62,74,76,104,105]],[76,56,[85,95,103,104],[17,43,62,74,75,96,105]],[18,88,[86,95,97,98,103,106],[44,63,74,77,78]],[44,88,[103,106],[18,63,74,77,78,86,95,97,98]],[63,88,[95,97,98,106],[18,44,74,77,78,86,103]],[74,88,[86,97,98,106],[18,44,63,77,78,95,103]],[77,88,[86,95,98,103],[18,44,63,74,78,97,106]],[78,88,[86,95,97,103],[18,44,63,74,77,98,106]],[19,536,[96,98,99,105,106],[46,76,78,79,80]],[46,536,[105,106],[19,76,78,79,80,96,98,99]],[76,536,[98,99,106],[19,46,78,79,80,96,105]],[78,536,[96,99,105],[19,46,76,79,80,98,106]],[79,536,[96,98,99,106],[19,46,76,78,80,105]],[80,536,[96,98,105],[19,46,76,78,79,99,106]],[23,784,[93,99,102,106],[58,72,80,84]],[58,784,[106],[23,72,80,84,93,99,102]],[72,784,[99,102,106],[23,58,80,84,93]],[80,784,[93,102],[23,58,72,84,99,106]],[84,784,[93,99],[23,58,72,80,102,106]],[85,30,[29,86],[]],[86,30,[29,85],[]],[36,534,[93],[]],[99,282,[45,97],[]],[53,114,[90,95],[]],[54,306,[91],[]],[91,306,[54],[]],[55,562,[96],[]],[96,562,[55],[]],[57,594,[98,102],[]],[102,594,[57,98],[]],[64,156,[104],[]],[104,156,[64],[]],[103,108,[65,87],[]],[71,660,[],[]],[106,840,[82,101],[]],[83,688,[105],[]],[105,688,[83],[]]],\"edges\":[[24,[17,18,19,29,43,44,45,46,62,63,64,74,75,76,77,78,79,80,85,86,95,96,97,98,99,103,104,105,106]],[26,[5,18,31,44,47,49,50,51,63,65,67,74,77,78,82,86,87,89,95,97,98,101,103,106]],[30,[12,17,33,43,53,54,55,62,68,69,70,74,75,76,83,85,90,91,95,96,103,104,105]],[34,[19,23,36,46,55,57,58,71,72,76,78,79,80,83,84,93,96,98,99,102,105,106]],[44,[11,23,42,52,58,60,61,72,73,80,82,84,93,94,99,101,102,106]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-56,-54],[-58,-56],[-61,-47],[-62,-10],[-62,-13],[-63,-61],[-64,-10],[-64,-13],[-1,51,52,53,58,60,61,63],[-9,58,60,61,63],[-17,51,53,60,61,63],[-18,51,52,58,60,61,63],[-19,51,52,53,58,61],[-20,51,52,53,58,60],[-2,7,38,39,46,47,49],[-12,7,46,47,49],[-28,7,38,46,47,49],[-2,56,57,62,63,64],[-12,62,63,64],[-21,56,57,64],[-26,57,63],[-27,56,57,62],[-28,56,62,63,64],[-3,50,54,55,65,66],[-10,65,66],[-29,54,55],[-34,50,55,66],[-35,50,54,55,65],[-36,50,54,65,66],[-4,50,58,59,65,66,67],[-13,65,66,67],[-40,50,59,66,67],[-41,50,58,59,65],[-42,50,58,65,66],[-5,51,58,60,61,65,68],[-14,65,68],[-30,58,60,61,68],[-40,51,60,61,68],[-43,51,58,61,65],[-44,51,58,60,65],[-6,59,61,62,67,68],[-16,67,68],[-42,61,62,68],[-44,59,62,67],[-45,59,61,62,68],[-46,59,61,67],[-7,56,62,64,68],[-26,68],[-38,62,64,68],[-46,56,64],[-49,56,62],[-50,8,51],[-51,8,50],[-11,56],[-62,15,60],[-22,54,58],[-23,55],[-55,23],[-24,59],[-59,24],[-25,61,64],[-64,25,61],[-31,66],[-66,31],[-65,32,52],[-37],[-68,47,63],[-48,67],[-67,48],[-11,69],[-39,69],[-56,70],[-57,70],[-31,71],[-48,71],[-72,66,67],[-66,72],[-67,72],[-15,73],[-25,73],[-47,73],[-60,74],[-61,74],[-63,74],[-75,62,64,68],[-62,75],[-64,75],[-68,75],[-8,76],[-32,76],[-33,76],[-50,77],[-52,77],[-53,77],[-78,22,23,24,51],[-22,78],[-23,78],[-24,78],[-51,78],[-54,79],[-55,79],[-59,79],[-58,80],[-65,80],[-71,81],[-70,81],[-81,82],[-69,82],[-74,83],[-73,83],[-83,84],[-72,84],[-72,-83,85],[-84,86],[-85,87],[-82,86],[-82,-84,87],[-82,-85,88],[-77,89],[-76,89],[-76,-77,90],[-89,91],[-90,92],[-75,91],[-80,93],[-79,93],[-93,94],[-78,94],[-78,-93,95],[-94,96],[-95,97],[-91,96],[-91,-94,97],[-92,97],[-86,-97,98],[-87,-96,98],[-88,98],[-98],[4,5,6,8,13,14,15,16,29,30,31,40,41,42,43,44,45,46,50,51,58,59,60,61,62,65,66,67,68],[1,5,9,14,17,18,19,20,30,32,33,40,43,44,47,51,52,53,58,60,61,63,65,68],[3,4,10,13,22,23,24,29,34,35,36,40,41,42,48,50,54,55,58,59,65,66,67],[6,7,11,16,24,25,26,37,38,42,44,45,46,48,49,56,59,61,62,64,67,68],[2,7,12,21,26,27,28,38,39,46,47,49,56,57,62,63,64,68]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":93,\"b\":90},{\"tag\":\"incompatible\",\"a\":95,\"b\":93},{\"tag\":\"incompatible\",\"a\":98,\"b\":82},{\"tag\":\"incompatible\",\"a\":99,\"b\":33},{\"tag\":\"incompatible\",\"a\":99,\"b\":43},{\"tag\":\"incompatible\",\"a\":101,\"b\":98},{\"tag\":\"incompatible\",\"a\":102,\"b\":33},{\"tag\":\"incompatible\",\"a\":102,\"b\":43},{\"tag\":\"mate\",\"ridge\":74,\"a\":5,\"owners\":[86,87,89,95,97,98,101]},{\"tag\":\"mate\",\"ridge\":74,\"a\":31,\"owners\":[95,97,98,101]},{\"tag\":\"mate\",\"ridge\":74,\"a\":47,\"owners\":[86,89,97,98,101]},{\"tag\":\"mate\",\"ridge\":74,\"a\":49,\"owners\":[86,87,95,97,98,101]},{\"tag\":\"mate\",\"ridge\":74,\"a\":50,\"owners\":[86,87,89,95,98]},{\"tag\":\"mate\",\"ridge\":74,\"a\":51,\"owners\":[86,87,89,95,97]},{\"tag\":\"mate\",\"ridge\":769,\"a\":11,\"owners\":[23,72,73,80,82,84]},{\"tag\":\"mate\",\"ridge\":769,\"a\":42,\"owners\":[23,80,82,84]},{\"tag\":\"mate\",\"ridge\":769,\"a\":61,\"owners\":[23,72,80,82,84]},{\"tag\":\"mate\",\"ridge\":770,\"a\":11,\"owners\":[93,94,99,101,102]},{\"tag\":\"mate\",\"ridge\":770,\"a\":42,\"owners\":[99,101,102]},{\"tag\":\"mate\",\"ridge\":770,\"a\":52,\"owners\":[93,94,102]},{\"tag\":\"mate\",\"ridge\":770,\"a\":58,\"owners\":[94,101]},{\"tag\":\"mate\",\"ridge\":770,\"a\":60,\"owners\":[93,94,99]},{\"tag\":\"mate\",\"ridge\":770,\"a\":61,\"owners\":[93,99,101,102]},{\"tag\":\"mate\",\"ridge\":52,\"a\":12,\"owners\":[85,90,91,103,104]},{\"tag\":\"mate\",\"ridge\":52,\"a\":33,\"owners\":[103,104]},{\"tag\":\"mate\",\"ridge\":52,\"a\":62,\"owners\":[90,91]},{\"tag\":\"mate\",\"ridge\":52,\"a\":68,\"owners\":[85,91,104]},{\"tag\":\"mate\",\"ridge\":52,\"a\":69,\"owners\":[85,90,91,103]},{\"tag\":\"mate\",\"ridge\":52,\"a\":70,\"owners\":[85,90,103,104]},{\"tag\":\"mate\",\"ridge\":56,\"a\":17,\"owners\":[85,95,96,103,104,105]},{\"tag\":\"mate\",\"ridge\":56,\"a\":43,\"owners\":[103,104,105]},{\"tag\":\"mate\",\"ridge\":56,\"a\":74,\"owners\":[85,96,104,105]},{\"tag\":\"mate\",\"ridge\":56,\"a\":75,\"owners\":[85,95,96,103]},{\"tag\":\"mate\",\"ridge\":56,\"a\":76,\"owners\":[85,95,103,104]},{\"tag\":\"mate\",\"ridge\":88,\"a\":18,\"owners\":[86,95,97,98,103,106]},{\"tag\":\"mate\",\"ridge\":88,\"a\":44,\"owners\":[103,106]},{\"tag\":\"mate\",\"ridge\":88,\"a\":63,\"owners\":[95,97,98,106]},{\"tag\":\"mate\",\"ridge\":88,\"a\":74,\"owners\":[86,97,98,106]},{\"tag\":\"mate\",\"ridge\":88,\"a\":77,\"owners\":[86,95,98,103]},{\"tag\":\"mate\",\"ridge\":88,\"a\":78,\"owners\":[86,95,97,103]},{\"tag\":\"mate\",\"ridge\":536,\"a\":19,\"owners\":[96,98,99,105,106]},{\"tag\":\"mate\",\"ridge\":536,\"a\":46,\"owners\":[105,106]},{\"tag\":\"mate\",\"ridge\":536,\"a\":76,\"owners\":[98,99,106]},{\"tag\":\"mate\",\"ridge\":536,\"a\":78,\"owners\":[96,99,105]},{\"tag\":\"mate\",\"ridge\":536,\"a\":79,\"owners\":[96,98,99,106]},{\"tag\":\"mate\",\"ridge\":536,\"a\":80,\"owners\":[96,98,105]},{\"tag\":\"mate\",\"ridge\":784,\"a\":23,\"owners\":[93,99,102,106]},{\"tag\":\"mate\",\"ridge\":784,\"a\":58,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":784,\"a\":72,\"owners\":[99,102,106]},{\"tag\":\"mate\",\"ridge\":784,\"a\":80,\"owners\":[93,102]},{\"tag\":\"mate\",\"ridge\":784,\"a\":84,\"owners\":[93,99]},{\"tag\":\"mate\",\"ridge\":30,\"a\":85,\"owners\":[29,86]},{\"tag\":\"mate\",\"ridge\":30,\"a\":86,\"owners\":[29,85]},{\"tag\":\"mate\",\"ridge\":534,\"a\":36,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":282,\"a\":99,\"owners\":[45,97]},{\"tag\":\"mate\",\"ridge\":114,\"a\":53,\"owners\":[90,95]},{\"tag\":\"mate\",\"ridge\":306,\"a\":54,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":306,\"a\":91,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":562,\"a\":55,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":562,\"a\":96,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":594,\"a\":57,\"owners\":[98,102]},{\"tag\":\"mate\",\"ridge\":594,\"a\":102,\"owners\":[57,98]},{\"tag\":\"mate\",\"ridge\":156,\"a\":64,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":156,\"a\":104,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":108,\"a\":103,\"owners\":[65,87]},{\"tag\":\"mate\",\"ridge\":660,\"a\":71,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":840,\"a\":106,\"owners\":[82,101]},{\"tag\":\"mate\",\"ridge\":688,\"a\":83,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":688,\"a\":105,\"owners\":[83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":36,\"full_literals\":[-11,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":73,\"full_literals\":[-39,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":93,\"full_literals\":[-56,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":94,\"full_literals\":[-57,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":64,\"full_literals\":[-31,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":83,\"full_literals\":[-48,71]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[104,105],\"full_literals\":[-72,66,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":104,\"full_literals\":[-66,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":105,\"full_literals\":[-67,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":45,\"full_literals\":[-15,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":57,\"full_literals\":[-25,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":82,\"full_literals\":[-47,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":97,\"full_literals\":[-60,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":98,\"full_literals\":[-61,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":101,\"full_literals\":[-63,74]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[99,102,106],\"full_literals\":[-75,62,64,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":99,\"full_literals\":[-62,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":102,\"full_literals\":[-64,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":106,\"full_literals\":[-68,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":29,\"full_literals\":[-8,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":65,\"full_literals\":[-32,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":67,\"full_literals\":[-33,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":85,\"full_literals\":[-50,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":87,\"full_literals\":[-52,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":89,\"full_literals\":[-53,77]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[53,54,55,86],\"full_literals\":[-78,22,23,24,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":53,\"full_literals\":[-22,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":54,\"full_literals\":[-23,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":55,\"full_literals\":[-24,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":86,\"full_literals\":[-51,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":90,\"full_literals\":[-54,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":91,\"full_literals\":[-55,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":96,\"full_literals\":[-59,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":95,\"full_literals\":[-58,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":103,\"full_literals\":[-65,80]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-81,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-72,-83,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-84,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-85,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-82,-84,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-82,-85,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-77,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-89,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-90,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-80,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-79,false,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-93,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-78,-93,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-94,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-95,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-91,false,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-91,-94,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-92,false,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-86,-97,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-87,-96,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-88,false,98],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":24,\"owners\":[17,18,19,29,43,44,45,46,62,63,64,74,75,76,77,78,79,80,85,86,95,96,97,98,99,103,104,105,106]},{\"tag\":\"edge\",\"edge\":26,\"owners\":[5,18,31,44,47,49,50,51,63,65,67,74,77,78,82,86,87,89,95,97,98,101,103,106]},{\"tag\":\"edge\",\"edge\":30,\"owners\":[12,17,33,43,53,54,55,62,68,69,70,74,75,76,83,85,90,91,95,96,103,104,105]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[19,23,36,46,55,57,58,71,72,76,78,79,80,83,84,93,96,98,99,102,105,106]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[11,23,42,52,58,60,61,72,73,80,82,84,93,94,99,101,102,106]}]}"
  "144 -88 0 138 137 0\n145 6 7 11 16 24 25 26 38 42 44 45 46 48 49 56 59 61 62 64 67 68 0 66 142 0\n146 86 0 114 116 111 107 108 109 110 106 71 82 83 84 79 80 81 72 73 55 62 67 21 18 20 22 19 49 23 47 51 50 143 0\n147 -97 0 146 138 135 0\n148 -95 0 147 131 0\n149 -92 0 147 134 0\n150 -90 0 149 123 0\n151 56 84 24 75 0 112 78 60 111 109 83 46 88 86 45 41 43 44 42 68 110 80 48 87 49 54 47 51 145 0\n152 84 78 91 0 98 60 97 58 124 88 122 120 90 119 93 65 36 89 92 53 86 111 112 109 110 77 78 82 83 79 63 31 32 42 44 43 41 45 46 151 1 2 26 37 30 33 35 39 139 0\n153 61 56 48 11 24 75 0 60 86 69 44 88 42 87 50 51 47 48 49 61 43 41 45 145 0\n154 78 91 87 0 124 88 48 87 86 49 98 152 117 107 108 105 106 70 71 75 72 73 47 51 50 20 22 153 3 6 15 17 16 143 0\n155 91 87 0 148 122 119 120 92 89 53 154 129 125 126 103 100 101 102 56 57 59 95 0\n156 72 -64 50 94 0 8 7 127 125 104 126 101 100 28 102 103 33 26 128 98 97 96 77 78 27 32 30 34 29 24 68 141 0\n157 -64 50 87 0 147 155 133 115 156 113 109 110 83 80 62 0\n158 83 -62 0 109 110 82 79 55 0\n159 -62 50 87 0 147 155 133 127 125 104 126 101 100 28 102 103 33 26 128 98 97 96 115 4 5 158 113 77 78 27 32 30 34 29 24 68 141 0\n160 72 50 94 0 127 125 104 126 101 100 28 102 103 33 26 128 98 97 96 77 78 25 31 27 32 30 34 29 24 68 141 0\n161 50 87 0 147 155 133 128 98 115 157 159 160 112 113 117 109 110 107 108 84 81 105 106 70 67 83 75 72 85 153 0\n162 -50 51 0 150 52 92 89 121 0\n163 87 0 147 155 133 128 99 161 162 0\n164 -96 0 163 138 136 0\n165 -94 0 164 130 0\n166 -91 0 164 132 0\n167 -93 0 165 127 0\n168 -78 0 165 128 0\n169 -89 0 166 122 0\n170 -75 0 166 124 0\n171 -80 0 167 125 0\n172 -51 0 168 99 0\n173 -77 0 169 119 0\n174 -76 0 169 120 0\n175 -68 0 170 88 0\n176 -58 0 171 103 0\n177 -65 0 171 104 0\n178 -50 0 172 162 0\n179 -52 0 173 93 0\n180 -53 0 173 94 0\n181 -32 0 174 90 0\n182 -33 0 174 91 0\n183 -14 0 175 177 36 0\n184 72 0 178 165 160 0\n185 83 0 175 177 176 180 179 172 182 181 183 109 110 82 83 84 81 40 37 35 38 14 13 39 10 12 9 11 140 0\n186 85 0 185 184 113 0\n187 -82 0 186 144 118 0\n188 -81 0 187 107 0\n189 -71 0 188 105 0\n190 -31 0 189 74 0\n191 -48 0 189 75 0\n192 -66 0 190 64 0\n193 -67 0 191 69 0\n194 0 193 192 184 76 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record003
