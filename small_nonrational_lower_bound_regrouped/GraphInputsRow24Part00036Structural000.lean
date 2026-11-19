module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00036Data
public import GraphInputsRow24Part00036Frames
public import GraphInputsRow24Part00036Leaves
public import GraphInputsRow24Part00036Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 4609152743636992, 2449958197289549824, (certNat% 3), 562949953421312]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), (certNat% 5), (certNat% 3), 668503069687808, 4503599627370496]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 598134325510144, (certNat% 7), (certNat% 3), 2305843009213693952]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 10), 45035996273704960, (certNat% 11)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 7), (certNat% 14), 2306405959167115264, (certNat% 5)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), 738871813865472, 3026418949592973312, (certNat% 17)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 18436610974547968, 2882303761517117440, (certNat% 19), 562949953421312]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 19), 985162418487296, 18014398509481984]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 703687441776640, (certNat% 23), (certNat% 19), 2305843009213693952]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), (certNat% 10), 45035996273704960, (certNat% 26)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), 18313465672237056, (certNat% 23), (certNat% 28), 2306405959167115264, (certNat% 21)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 54325770016784384, 3026418949592973312, (certNat% 17), 567347999932416, 175921860444160]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), 567347999932416, 13581305065242624, 54325770016784384, (certNat% 16), 175921860444160]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), (certNat% 33), (certNat% 17), 2305847407260205056, 720575940379279360]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 2305847407260205056, 45038470174867456, (certNat% 9), (certNat% 25), 720575940379279360]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), 18436610974547968, (certNat% 7), (certNat% 36), (certNat% 37), 576460752303423488]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), 4538783999459328, (certNat% 3), 567347999932416]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 4503874505277440, (certNat% 7), (certNat% 17), 2306410357213626368, 35184372088832]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 41)]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c30 c23
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c32 c27
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), 4503737066323968, (certNat% 26), (certNat% 43)]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 45), 4573968371548160, (certNat% 28), 567347999932416]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c36 c35
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 13510936321064960, 18017697044365312, (certNat% 47), (certNat% 48)]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 50), (certNat% 51), (certNat% 52), 18436610974547968]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 10), 13581305065242624, (certNat% 19), 4398046511104, 18436610974547968]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c41 c38
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c42 c37
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 18437710486175744, (certNat% 23), (certNat% 55), 2306410357213626368, 35184372088832]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), (certNat% 14), (certNat% 58), 2305847407260205056, (certNat% 9)]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), 4609290182590464, 54327969040039936, (certNat% 32), (certNat% 23), (certNat% 17), 2306410357213626368]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c47 c44
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c48 c43
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c49 c31
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c50 c22
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c51 c21
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c52 c20
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c53 c19
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c54 c18
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c55 c9
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c56 c8
  c57
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007
def vertexColumn : Fields := ⟨10, (certNat% 60)⟩
def kindColumn : Fields := ⟨3, (certNat% 61)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c1 c2
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), (certNat% 19), (certNat% 63)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), 6605659701248, (certNat% 65), (certNat% 66)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 68), (certNat% 69), (certNat% 63), 6768868458496]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c9 c0
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), (certNat% 72), (certNat% 73), (certNat% 74), 33019708571648]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c12 c0
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), (certNat% 73), 15401752723456, 4611686018427387904, 19281035904679936, (certNat% 37)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c0 c14
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), (certNat% 77), 32985348833280, (certNat% 78)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), (certNat% 68), (certNat% 80), 30820685316096]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 81), (certNat% 52), (certNat% 77), (certNat% 82), 31026843746304, (certNat% 83)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 84), (certNat% 66), (certNat% 85), (certNat% 86), 17592186044416]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), 40550126271332352, (certNat% 88), (certNat% 89), (certNat% 19), (certNat% 90)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 91), (certNat% 92), (certNat% 93), 22058952032256, (certNat% 94)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 95), 33054068310016, (certNat% 96), (certNat% 11), (certNat% 97)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 98), (certNat% 88), 31404800868352, (certNat% 99), (certNat% 16), (certNat% 100)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c28 c25
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 101), 36046526643961856, 4611969701017288704, (certNat% 102), 13228499271680]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 103), (certNat% 71), (certNat% 104), (certNat% 96), 30820685316096, 19703248369745920]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c31 c30
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 105), (certNat% 106), (certNat% 107), (certNat% 104), (certNat% 108)]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 109), (certNat% 110), (certNat% 111), (certNat% 99), 31439160606720, 22025416927608832, (certNat% 112)]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c35 c32
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c36 c29
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c37 c24
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c38 c21
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c39 c16
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c40 c13
  c41
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018
def vertexColumn : Fields := ⟨10, (certNat% 113)⟩
def kindColumn : Fields := ⟨3, (certNat% 114)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 115), (certNat% 116), (certNat% 117), 2234913514105864192, 261134011596800, 61361544922923008, (certNat% 118)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019
def vertexColumn : Fields := ⟨10, (certNat% 119)⟩
def kindColumn : Fields := ⟨3, (certNat% 120)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 121), 3940649673949184, (certNat% 122), (certNat% 123)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 124), 3975834046038016, (certNat% 125), 18015223143202816, 72057594037927936]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c2 c0
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 126), 74309393851613184, (certNat% 127), (certNat% 128)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 129), 74311592874868736, (certNat% 130), (certNat% 131), (certNat% 128)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c6 c4
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 132), 4046202790215680, (certNat% 133), (certNat% 134)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 135), (certNat% 136), 4046202790215680, 31525197391593472, (certNat% 137)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 138), (certNat% 136), 1724034232352768, 13510798882111488, (certNat% 130)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 139), 4046202790215680, (certNat% 134), (certNat% 140), (certNat% 133), 18015498021109760]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c15 c3
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 141), (certNat% 142), 49539595901075456, (certNat% 143), (certNat% 144), (certNat% 145)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 146), 4011018418126848, (certNat% 147), (certNat% 133), (certNat% 148)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 149), 13835058055282163712, (certNat% 150)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 151), 13835058055282163712, (certNat% 136), 31526296903221248, (certNat% 152)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 153), 18084767253659648, 13835058192721117184, 3940649673949184]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 154), (certNat% 155), 13835058192721117184, 3940649673949184]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 156), (certNat% 157), 22518273014759424, (certNat% 158)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 159), (certNat% 157), 13835058192721117184, 1688849860263936]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 160), 22518273014759424, 13835058192721117184, (certNat% 155), 1688849860263936]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c27 c24
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c28 c23
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c29 c22
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 161), (certNat% 162), 74379762595790848, (certNat% 163), 1688849860263936]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 164), (certNat% 165), 4011087137603584, (certNat% 166), (certNat% 167), 90075291082293248]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c33 c30
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c34 c21
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c35 c18
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 168), (certNat% 169), 49592372459208704, 16429131509367046144, 2040693581152256, (certNat% 170)]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 171), (certNat% 147), (certNat% 133), 1811995162574848, 2251799813685248]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 172), 74309531290566656, (certNat% 127), (certNat% 173), (certNat% 174)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 175), (certNat% 176), 3940855832379392, (certNat% 177), 13835058055282163712]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 178), (certNat% 140), (certNat% 166), 4046271509692416, (certNat% 133), (certNat% 179)]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c42 c39
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c43 c38
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 180), (certNat% 169), 2005646648016896, (certNat% 181), (certNat% 182), 14987979559889010688]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 183), 4011018418126848, (certNat% 133), 15420325124116578304, (certNat% 123)]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 184), (certNat% 185), 3940649673949184]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 186), (certNat% 122), (certNat% 187), 3940718393425920, (certNat% 123)]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c48 c47
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 188), (certNat% 150), 14123288431433875456]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 189), 1689056018694144, (certNat% 190), (certNat% 136), 13835058055282163712]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c51 c50
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 191), (certNat% 140), 4011087137603584, 90071992547409920, (certNat% 192), (certNat% 193)]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c53 c52
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c54 c49
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c55 c46
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 194), (certNat% 169), 4327746486403072, 67571586596601856, (certNat% 195), (certNat% 196), 5222680231936]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c57 c56
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c58 c45
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c59 c44
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c60 c37
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c61 c36
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c62 c17
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c63 c16
  c64
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00036.record019
