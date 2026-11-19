module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00034Data
public import GraphInputsRow23Part00034Frames
public import GraphInputsRow23Part00034Leaves
public import GraphInputsRow23Part00034Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 9570149208162304, (certNat% 4), (certNat% 5), (certNat% 6), (certNat% 7)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), 652036783550234624, (certNat% 9), (certNat% 10), (certNat% 11), 4503599627370496]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 5), (certNat% 14), 669488232106295296, (certNat% 15), (certNat% 16), (certNat% 17)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 20), (certNat% 21), 94729798680576, (certNat% 13), (certNat% 22)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 3), 306244774661193728, (certNat% 24), (certNat% 25), (certNat% 26)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 14), (certNat% 28), (certNat% 29), (certNat% 30), 144115188075855872]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), (certNat% 33), 669488232106295296, (certNat% 34), (certNat% 35), (certNat% 36), (certNat% 37)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 4), 78340203479040, (certNat% 39), (certNat% 21), (certNat% 33), (certNat% 40)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), (certNat% 43), (certNat% 44), (certNat% 45), (certNat% 46)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 24), (certNat% 48), (certNat% 49), (certNat% 37), (certNat% 50)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 13), (certNat% 52), (certNat% 5), (certNat% 6), (certNat% 53), (certNat% 54), (certNat% 55)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), (certNat% 58), 576537752477106176, (certNat% 45), (certNat% 59), 74872343805034496, (certNat% 60)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 62), (certNat% 45), (certNat% 63), (certNat% 64), 669347494617939968, (certNat% 65)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), (certNat% 67), (certNat% 24), (certNat% 68), (certNat% 30), (certNat% 26), (certNat% 69), (certNat% 70)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), (certNat% 45), (certNat% 72), (certNat% 73), (certNat% 33), (certNat% 74), (certNat% 75), (certNat% 76)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 78), 576537992995274752, (certNat% 58), (certNat% 63), (certNat% 30), 92323792361095168, (certNat% 10)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), 576538027355013120, (certNat% 80), (certNat% 81), (certNat% 63), (certNat% 82), (certNat% 46), (certNat% 83), 378302368699121664]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c23 c20
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c24 c19
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c25 c18
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c26 c17
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c27 c16
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c28 c11
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c29 c10
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c30 c5
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c31 c4
  c32
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003
def vertexColumn : Fields := ⟨10, (certNat% 84)⟩
def kindColumn : Fields := ⟨3, (certNat% 85)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 86), (certNat% 87), (certNat% 88), (certNat% 89), (certNat% 90), (certNat% 91)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 92), 126874845752328192, (certNat% 93), (certNat% 94), 69836168232960, 5910974510923776]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 95), (certNat% 96), (certNat% 97), 109071553475379200, (certNat% 98), (certNat% 99)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 100), (certNat% 101), (certNat% 102), (certNat% 103), (certNat% 104), (certNat% 105)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 106), (certNat% 107), (certNat% 108), (certNat% 109), 68736656605184, 117656540265054208, 4503599627370496]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 110), (certNat% 111), (certNat% 109), 69836168232960, 5348024557502464, 135107988821114880]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 112), (certNat% 113), (certNat% 114), (certNat% 115), 61572651155456]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 116), (certNat% 117), (certNat% 118), (certNat% 114), (certNat% 115), 61572651155456]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 119), (certNat% 105), 109001184731201536, (certNat% 111), (certNat% 120), 61589831024640, (certNat% 121), 4503599627370496]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 122), (certNat% 123), (certNat% 124), (certNat% 125), (certNat% 126), 65970697666560, 288230376151711744]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 127), 61591978508288, 9516106012633858048, (certNat% 104)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 128), 109001186878685184, (certNat% 129), 62689342652416, 292733975779082240, (certNat% 130), (certNat% 90)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 131), (certNat% 94), (certNat% 124), (certNat% 132), (certNat% 133), 5910974510923776, (certNat% 134), 69844758167552, 562949953421312]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c19 c4
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006
def vertexColumn : Fields := ⟨10, (certNat% 135)⟩
def kindColumn : Fields := ⟨3, (certNat% 136)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 137), 2308129993399468032, (certNat% 138), (certNat% 139), 54043195528445952, (certNat% 140), 864691128455135232]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 141), (certNat% 142), (certNat% 143), (certNat% 144), (certNat% 145)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 146), 2305878193585782784, (certNat% 147), (certNat% 143), (certNat% 144), (certNat% 140)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 148), 2308129993399468032, (certNat% 149), 54043195528445952, (certNat% 150), (certNat% 151), 576465150349934592]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 152), (certNat% 153), (certNat% 154), 2524303875024879616, (certNat% 155), 54887620458577920, (certNat% 156), 864697725524901888]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 157), (certNat% 158), 59109745109237760, (certNat% 159), (certNat% 160), (certNat% 147), (certNat% 161), (certNat% 162)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 163), (certNat% 164), (certNat% 165), 4395513236313604096, 41095621477662720, (certNat% 166), (certNat% 167), (certNat% 168)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 169), (certNat% 164), (certNat% 170), 4395513236313604096, 41095621477662720, (certNat% 171), (certNat% 167), (certNat% 172)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 173), (certNat% 174), (certNat% 175), 576476145466212352, (certNat% 176), (certNat% 177)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 178), (certNat% 179), (certNat% 180), (certNat% 181), (certNat% 182), (certNat% 183)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 184), 576476145466212352, (certNat% 185), (certNat% 186), (certNat% 187), (certNat% 166), (certNat% 188), (certNat% 177)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 189), 50665495807918080, 3458764513820540928, (certNat% 158), (certNat% 190), (certNat% 162)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 191), (certNat% 192), 3463268113447911424, (certNat% 158), (certNat% 190), (certNat% 161)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 193), (certNat% 194), (certNat% 195), (certNat% 196), (certNat% 4), (certNat% 197)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 198), 3458764513820540928, (certNat% 199), (certNat% 192), (certNat% 158), (certNat% 200), (certNat% 201)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 202), 180143985094819840, 3530822107858468864, (certNat% 203), (certNat% 204), (certNat% 205), (certNat% 206)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 207), (certNat% 208), (certNat% 209), (certNat% 210), (certNat% 204), 216172782113783808, 1152921504606846976]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 211), 3458764513820540928, (certNat% 158), (certNat% 179), (certNat% 212), (certNat% 194)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 213), (certNat% 209), (certNat% 214), 3530822107858468864, (certNat% 190), (certNat% 158), (certNat% 215), (certNat% 216)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c26 c21
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c27 c20
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c28 c19
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c29 c18
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c30 c17
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 217), (certNat% 218), (certNat% 174), 1459166279268040704, 2305895785771827200, (certNat% 219)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 220), (certNat% 221), (certNat% 222), 3819052484010180608, (certNat% 223), (certNat% 167), 35184372088832]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 224), (certNat% 225), (certNat% 226), (certNat% 227), 360287970189639680, (certNat% 228), 144115188075855872]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 229), (certNat% 225), 2522050975699566592, (certNat% 187), 1459166416706994176, (certNat% 228), (certNat% 230), (certNat% 231)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c36 c33
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c37 c32
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 232), 54043195528445952, 4323455642275676160, (certNat% 233), (certNat% 234), (certNat% 235)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 236), 3098476543630901248, (certNat% 237), (certNat% 238), (certNat% 181), (certNat% 239), (certNat% 240), (certNat% 241)]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 242), (certNat% 218), (certNat% 243), (certNat% 149), (certNat% 244), (certNat% 245), (certNat% 246)]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 247), (certNat% 248), (certNat% 158), (certNat% 149), (certNat% 249), (certNat% 250)]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 251), (certNat% 218), (certNat% 159), (certNat% 252), (certNat% 212), (certNat% 253), (certNat% 254)]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 255), (certNat% 256), (certNat% 174), 1459166416706994176, (certNat% 257), (certNat% 258), (certNat% 230), (certNat% 259)]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c45 c44
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c46 c43
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c47 c42
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 260), (certNat% 261), (certNat% 164), (certNat% 262), (certNat% 187), (certNat% 171), (certNat% 263), (certNat% 264)]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 265), (certNat% 218), (certNat% 266), 648659083829706752, (certNat% 267), 54043195528445952, (certNat% 268)]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 269), 58546795155816448, (certNat% 270), (certNat% 271), (certNat% 272), (certNat% 273), (certNat% 274)]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 275), 2089670227099910144, (certNat% 218), (certNat% 276), 59110019987144704, (certNat% 277), (certNat% 278), (certNat% 279)]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c52 c51
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c53 c50
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 280), 54043195528445952, 3242591731706757120, (certNat% 281), (certNat% 282), (certNat% 283), (certNat% 279)]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 284), 2315026130328879104, 54043195528445952, (certNat% 285), (certNat% 286), (certNat% 267), 576473946442956800, (certNat% 287)]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c56 c55
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 288), 54043195528445952, 4107282860161892352, (certNat% 289), (certNat% 290), (certNat% 291), (certNat% 279)]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 292), (certNat% 276), (certNat% 293), 54043195528445952, 576473946442956800, (certNat% 286), 2314885392840523776, (certNat% 287)]
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c59 c58
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 294), 864691128455135232, (certNat% 158), (certNat% 295), (certNat% 296), (certNat% 297)]
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 298), 4323455642275676160, (certNat% 299), 59110157426098176, (certNat% 233), (certNat% 230), (certNat% 300), (certNat% 7)]
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c62 c61
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 301), 936753120539574272, (certNat% 302), (certNat% 303), (certNat% 187), 1170953632741326848, (certNat% 304), (certNat% 259)]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 305), 864691128455135232, (certNat% 306), (certNat% 158), (certNat% 307), (certNat% 308), (certNat% 309)]
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 310), (certNat% 311), (certNat% 248), (certNat% 158), (certNat% 312), (certNat% 177), (certNat% 309)]
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 313), 936748722493063168, (certNat% 314), (certNat% 226), (certNat% 315), (certNat% 201), (certNat% 267), (certNat% 283)]
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c67 c66
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c68 c65
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 316), (certNat% 187), (certNat% 317), 59110157426098176, (certNat% 318), (certNat% 319), (certNat% 304), (certNat% 300), (certNat% 320)]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c70 c69
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c71 c64
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c72 c63
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c73 c60
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c74 c57
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c75 c54
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c76 c49
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c77 c48
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c78 c41
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c79 c38
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c80 c31
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c81 c16
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c82 c11
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c83 c10
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c84 c9
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c85 c8
  c86
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012
def vertexColumn : Fields := ⟨10, (certNat% 321)⟩
def kindColumn : Fields := ⟨3, (certNat% 322)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 323), (certNat% 324), 440226863575465984, (certNat% 325), (certNat% 326), (certNat% 327), 545563925807104, (certNat% 328)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00034.record012
