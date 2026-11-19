module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00000Data
public import GraphInputsRow23Part00000Frames
public import GraphInputsRow23Part00000Leaves
public import GraphInputsRow23Part00000Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00000.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 7205794588164882432, (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6), (certNat% 7)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [11240914232453103616, 7205829772536971264, (certNat% 8), (certNat% 4), (certNat% 5), (certNat% 6), (certNat% 7)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 10), (certNat% 11), (certNat% 12), 576469548396445696]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17), 7599824371187712, 432346663739195392, 1729408645189337088, 6917634580757348352]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00000.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00000.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022
def vertexColumn : Fields := ⟨10, (certNat% 18)⟩
def kindColumn : Fields := ⟨3, (certNat% 19)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), (certNat% 23), (certNat% 24), (certNat% 25)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 22), 648518346341351424, (certNat% 27), (certNat% 28), 1297054284868747264]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 22), 5476377146882523136, (certNat% 27), (certNat% 23), 1297054284868747264]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), (certNat% 27), (certNat% 28), 936748722493063168, 1297054284868747264, (certNat% 32)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), (certNat% 35), (certNat% 36), (certNat% 37), (certNat% 38)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), (certNat% 35), (certNat% 36), (certNat% 37), (certNat% 38)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), 936748722493063168, (certNat% 35), (certNat% 36), (certNat% 37), (certNat% 38), (certNat% 32)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), 648518346341351424, (certNat% 43), (certNat% 44), (certNat% 45), (certNat% 46), (certNat% 47)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 24), (certNat% 49), (certNat% 35), (certNat% 50), (certNat% 51), (certNat% 37)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), 5476377146882523136, (certNat% 53), (certNat% 50), (certNat% 54), (certNat% 24), (certNat% 55)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 40), (certNat% 57), (certNat% 54), 5476377146882523136, (certNat% 55)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), (certNat% 36), (certNat% 54), 72075186223972352, (certNat% 59), 864691128455135232, (certNat% 32)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), (certNat% 24), (certNat% 61), (certNat% 50), 72075186223972352, (certNat% 62)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 61), (certNat% 35), (certNat% 31), (certNat% 45), (certNat% 64), (certNat% 32), (certNat% 65)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c23 c12
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c24 c11
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c25 c6
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), (certNat% 67), (certNat% 68), (certNat% 23), (certNat% 38), (certNat% 69)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 68), 1297036692682702848, (certNat% 34), (certNat% 71), 649081296294772736]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), (certNat% 68), 12682136550675316736, (certNat% 34), (certNat% 23), 649081296294772736]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), (certNat% 62), (certNat% 34), (certNat% 71), 649081296294772736, 3602879701896396800, (certNat% 49)]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c31 c28
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c32 c27
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 27), (certNat% 35), (certNat% 50), (certNat% 75), (certNat% 24)]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), (certNat% 46), (certNat% 35), (certNat% 50), (certNat% 75), (certNat% 24)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), 3602879701896396800, (certNat% 35), (certNat% 50), (certNat% 75), (certNat% 24), (certNat% 49)]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c36 c35
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c37 c34
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), 1297036692682702848, (certNat% 79), (certNat% 80), (certNat% 81), (certNat% 40), (certNat% 82)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), (certNat% 32), (certNat% 38), (certNat% 35), (certNat% 36), (certNat% 84), (certNat% 75)]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), 12682136550675316736, (certNat% 86), (certNat% 36), (certNat% 87), (certNat% 38), (certNat% 55)]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 88), (certNat% 46), (certNat% 65), (certNat% 87), 12682136550675316736, (certNat% 55)]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 89), (certNat% 50), (certNat% 87), 144678138029277184, (certNat% 90), 3458764513820540928, (certNat% 49)]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c43 c42
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 91), (certNat% 92), (certNat% 38), (certNat% 36), 144678138029277184, (certNat% 31)]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 93), (certNat% 92), (certNat% 35), (certNat% 62), (certNat% 81), (certNat% 94), (certNat% 49), (certNat% 57)]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c47 c44
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c48 c41
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c49 c40
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c50 c39
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c51 c38
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c52 c33
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 95), (certNat% 22), (certNat% 87), (certNat% 24), (certNat% 96), (certNat% 25)]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), (certNat% 27), (certNat% 98), 1297089469240836096, (certNat% 99), (certNat% 96), (certNat% 25)]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c55 c54
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 100), (certNat% 54), (certNat% 68), (certNat% 24), (certNat% 25), (certNat% 101)]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 102), (certNat% 36), (certNat% 103), 1297089469240836096, (certNat% 99), (certNat% 25), (certNat% 101)]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c58 c57
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 104), (certNat% 103), (certNat% 105), (certNat% 25), (certNat% 87), (certNat% 106), (certNat% 107), 1152956688978935808]
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c60 c59
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c61 c56
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 108), (certNat% 68), (certNat% 54), (certNat% 38), (certNat% 109), (certNat% 69)]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 110), (certNat% 67), (certNat% 111), (certNat% 112), (certNat% 113), (certNat% 109), (certNat% 69)]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c64 c63
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 114), 6755399441055744, (certNat% 35), (certNat% 37), (certNat% 38), (certNat% 69)]
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 115), 42784196460019712, (certNat% 81), (certNat% 38), (certNat% 22), (certNat% 69), (certNat% 54)]
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c67 c66
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 116), (certNat% 38), (certNat% 22), (certNat% 69), (certNat% 54), (certNat% 117), (certNat% 118)]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 119), (certNat% 120), (certNat% 69), (certNat% 87), (certNat% 121), (certNat% 122), (certNat% 123), (certNat% 124)]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c70 c69
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c71 c68
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c72 c65
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 125), (certNat% 27), (certNat% 68), (certNat% 109), (certNat% 23)]
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 126), (certNat% 22), (certNat% 21), (certNat% 127), (certNat% 128), (certNat% 23)]
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c75 c74
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 129), (certNat% 68), (certNat% 36), (certNat% 54), (certNat% 130), (certNat% 27)]
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 131), (certNat% 132), (certNat% 44), (certNat% 45), (certNat% 46), (certNat% 47), (certNat% 23)]
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c78 c77
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c79 c76
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 133), (certNat% 50), (certNat% 134), (certNat% 24), (certNat% 53), (certNat% 35), (certNat% 135)]
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 136), (certNat% 137), 144167964633989120, (certNat% 38), (certNat% 22), (certNat% 69), (certNat% 138)]
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 139), (certNat% 38), (certNat% 140), (certNat% 45), (certNat% 69), (certNat% 141), 144167964633989120, (certNat% 118)]
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c83 c82
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c84 c81
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c85 c80
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 142), (certNat% 143), (certNat% 80), (certNat% 81), (certNat% 23), (certNat% 144), (certNat% 145)]
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 146), (certNat% 147), (certNat% 80), (certNat% 68), (certNat% 148), (certNat% 144), (certNat% 149)]
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 150), (certNat% 80), (certNat% 27), (certNat% 36), (certNat% 86), (certNat% 35), (certNat% 151)]
  let c90 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 152), (certNat% 24), (certNat% 81), (certNat% 153), (certNat% 25), 72620543991349248, (certNat% 154), (certNat% 105)]
  let c91 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c90 c89
  let c92 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c91 c88
  let c93 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c92 c87
  let c94 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 155), (certNat% 106), (certNat% 156), (certNat% 107), (certNat% 132), (certNat% 157), (certNat% 87), (certNat% 158), (certNat% 159)]
  let c95 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c94 c93
  let c96 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c95 c86
  let c97 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c96 c73
  let c98 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c97 c62
  let c99 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c98 c53
  let c100 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c99 c26
  c100
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00000.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00000.record046
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046
def vertexColumn : Fields := ⟨10, (certNat% 160)⟩
def kindColumn : Fields := ⟨3, (certNat% 161)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 162), (certNat% 163), (certNat% 164), (certNat% 165), (certNat% 166), 135107988821114880, (certNat% 167), 982963395231744]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00000.record046
