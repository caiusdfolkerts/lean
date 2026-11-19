module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00025Data
public import GraphInputsRow23Part00025Frames
public import GraphInputsRow23Part00025Leaves
public import GraphInputsRow23Part00025Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 865113340920201216, (certNat% 5), (certNat% 6), (certNat% 7), 1152921504606846976]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), 141863388262170624, (certNat% 9), 865113340920201216, (certNat% 5), (certNat% 10), (certNat% 11), (certNat% 12)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 114841790497947648, (certNat% 14), (certNat% 15), (certNat% 16), 576460752303423488, (certNat% 17)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 20), (certNat% 21), (certNat% 22), 123850089264316416, 865113340920201216, (certNat% 23)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), (certNat% 26), 115967690404790272, (certNat% 27), (certNat% 28), (certNat% 29), 1873778919962836992, (certNat% 30)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record035
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035
def vertexColumn : Fields := ⟨10, (certNat% 31)⟩
def kindColumn : Fields := ⟨3, (certNat% 32)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), 1337006139375616, 8070450532247928832, (certNat% 35), (certNat% 36), (certNat% 37)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), 5699868278390784, 8070591269736284160, (certNat% 40), (certNat% 36), (certNat% 37)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), 6917740133873614848, (certNat% 43), 5629499534213120, (certNat% 44), (certNat% 45)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 5699868278390784, 8070591269736284160, (certNat% 47), (certNat% 48), (certNat% 49), (certNat% 50), (certNat% 51)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 53), (certNat% 54), 8088464930757410816, (certNat% 55), (certNat% 56), (certNat% 57), (certNat% 58)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), (certNat% 60), 6917740133873614848, (certNat% 61), (certNat% 62), 7881299347898368, (certNat% 63)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), (certNat% 60), 8070520900992106496, 5629499534213120, (certNat% 61), (certNat% 65), 144115188075855872]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), (certNat% 67), 7951668092076032, 8088605668245766144, (certNat% 68), (certNat% 69), (certNat% 70), (certNat% 63)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), 6917529027641081856, (certNat% 72), (certNat% 73), (certNat% 74), (certNat% 75), (certNat% 76)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 78), (certNat% 79), 6473924464345088, (certNat% 80), (certNat% 81), (certNat% 82)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), (certNat% 47), 5629499534213120, 8070450532247928832, (certNat% 84), (certNat% 76)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), (certNat% 60), 6473924464345088, (certNat% 80), (certNat% 55), (certNat% 86), 432345564227567616]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), 6482720557367296, (certNat% 88), (certNat% 89), (certNat% 90), (certNat% 91), (certNat% 92), (certNat% 76)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c19 c14
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c20 c13
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 93), (certNat% 94), (certNat% 95), 3597602046083072, 8088464930757410816, (certNat% 96), (certNat% 97), (certNat% 98)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 99), (certNat% 81), (certNat% 100), (certNat% 101), (certNat% 102), (certNat% 103), (certNat% 104), (certNat% 98)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 105), (certNat% 106), 1970324836974592, (certNat% 107), (certNat% 108), (certNat% 109), (certNat% 110), (certNat% 69)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 111), (certNat% 107), (certNat% 75), 8070450532247928832, (certNat% 112), (certNat% 113)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 114), 4611826755915743232, 7881299347898368, (certNat% 73), (certNat% 109), (certNat% 115), (certNat% 116)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 117), 7951668092076032, (certNat% 112), 8079598468991025152, (certNat% 118), (certNat% 119), (certNat% 56), (certNat% 120)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c28 c25
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 121), 4611826755915743232, 7881299347898368, (certNat% 73), (certNat% 122), (certNat% 115), (certNat% 47)]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 123), (certNat% 124), 4611826755915743232, (certNat% 125), (certNat% 126), 3377699720527872]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 127), 4611826755915743232, (certNat% 106), (certNat% 128), (certNat% 110), 5629499534213120, (certNat% 126)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 129), (certNat% 130), (certNat% 55), 3659174697238528, (certNat% 80), (certNat% 126)]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 131), (certNat% 109), (certNat% 106), (certNat% 130), 1407374883553280, (certNat% 80)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 132), (certNat% 130), (certNat% 55), (certNat% 106), (certNat% 133), 5629499534213120, (certNat% 122)]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c36 c35
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c37 c34
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 134), (certNat% 106), (certNat% 135), (certNat% 136), 6482720557367296, (certNat% 101), (certNat% 137), (certNat% 138)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c40 c33
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c41 c30
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 139), 8097683236244684800, (certNat% 140), 7890095440920576, (certNat% 113), (certNat% 110), (certNat% 141), (certNat% 22), (certNat% 142)]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c43 c42
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c44 c29
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c45 c24
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c46 c23
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c47 c22
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c48 c21
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c49 c12
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c50 c7
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c51 c6
  c52
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record035

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record047
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047
def vertexColumn : Fields := ⟨10, (certNat% 143)⟩
def kindColumn : Fields := ⟨3, (certNat% 144)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 145), (certNat% 146), (certNat% 147), (certNat% 148), (certNat% 149), (certNat% 150), (certNat% 151), (certNat% 152), 281474976710656]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record047

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record050
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050
def vertexColumn : Fields := ⟨10, (certNat% 153)⟩
def kindColumn : Fields := ⟨3, (certNat% 154)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 155), (certNat% 80), (certNat% 156), (certNat% 157), (certNat% 158), 1688849860263936]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 159), (certNat% 160), (certNat% 161), (certNat% 162), 1688849860263936, (certNat% 107), (certNat% 163)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 164), 4107775441371136, 8097472130012151808, (certNat% 165), (certNat% 166), (certNat% 167), (certNat% 168), (certNat% 169)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 170), (certNat% 171), (certNat% 172), 8088464930757410816, (certNat% 173), (certNat% 174), (certNat% 175), (certNat% 176)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 177), 1477743627730944, (certNat% 178), 6917529027641081856, (certNat% 107), (certNat% 173), (certNat% 179)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 180), 1477743627730944, (certNat% 178), (certNat% 181), 4611686018427387904, (certNat% 107), (certNat% 182)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 183), 1477743627730944, (certNat% 80), (certNat% 178), (certNat% 179), 8070450532247928832, (certNat% 184)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 185), (certNat% 186), (certNat% 187), 8088464930757410816, (certNat% 188), (certNat% 189), (certNat% 103), (certNat% 190)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 191), 5819072931027746816, (certNat% 192), 8453045394341888, (certNat% 193), (certNat% 194), (certNat% 195), (certNat% 196)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 197), (certNat% 198), 8070591269736284160, (certNat% 199), (certNat% 190), (certNat% 200), 8444249301319680, (certNat% 201)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 202), 8070520900992106496, 6201245580656640, (certNat% 203), (certNat% 193), (certNat% 190), (certNat% 196)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 204), (certNat% 205), (certNat% 206), 1697645953286144, 504403158265495552, (certNat% 207)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 208), (certNat% 195), (certNat% 209), 8070450532247928832, (certNat% 107), (certNat% 210), 288230376151711744]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 211), (certNat% 212), 216744528160227328, (certNat% 205), 1125899906842624, (certNat% 213), (certNat% 214)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 215), 5981343255101440, 6917529027641081856, (certNat% 216), (certNat% 217), (certNat% 218), (certNat% 219)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 220), 6917599396385259520, (certNat% 221), (certNat% 222), (certNat% 212), 1688849860263936]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 223), (certNat% 224), (certNat% 214), (certNat% 225), 1688849860263936, 360287970189639680, 8070450532247928832]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 226), (certNat% 222), 6482720557367296, (certNat% 227), (certNat% 228), 288230376151711744, (certNat% 107), (certNat% 229)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c24 c19
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c25 c18
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c26 c17
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c27 c16
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 230), (certNat% 160), (certNat% 212), (certNat% 186), (certNat% 231), (certNat% 179), (certNat% 232)]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 233), (certNat% 234), 8070450532247928832, (certNat% 107), (certNat% 187), (certNat% 56), (certNat% 235), (certNat% 236)]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 237), (certNat% 238), (certNat% 239), (certNat% 240), 8088605668245766144, (certNat% 235), (certNat% 241), (certNat% 242), (certNat% 243)]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c31 c30
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c32 c29
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c33 c28
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c34 c15
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c35 c14
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c36 c13
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c37 c12
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c38 c5
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c39 c4
  c40
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record050
