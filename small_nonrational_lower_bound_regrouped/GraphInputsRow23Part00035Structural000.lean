module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00035Data
public import GraphInputsRow23Part00035Frames
public import GraphInputsRow23Part00035Leaves
public import GraphInputsRow23Part00035Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6), 2218264709038080, 540431955284459520, (certNat% 7)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022
def vertexColumn : Fields := ⟨10, (certNat% 8)⟩
def kindColumn : Fields := ⟨3, (certNat% 9)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), (certNat% 13), (certNat% 14), (certNat% 15), 4467570830351532032, (certNat% 16)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 19), (certNat% 20), (certNat% 14), (certNat% 16), 4467570830351532032, (certNat% 15)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), (certNat% 12), 4467588422537576448, (certNat% 23), (certNat% 24), (certNat% 25), (certNat% 16)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), (certNat% 28), (certNat% 29), (certNat% 23), (certNat% 16), (certNat% 25), (certNat% 24)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), 6917529027641081856, (certNat% 32), (certNat% 33), (certNat% 34)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 36), (certNat% 37), (certNat% 38), (certNat% 39)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 4611967493404098560, (certNat% 36), (certNat% 33), (certNat% 34), (certNat% 41)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 37), (certNat% 43), (certNat% 44), (certNat% 45), (certNat% 46)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 31), (certNat% 36), (certNat% 41), (certNat% 48), (certNat% 33), (certNat% 49)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 51), (certNat% 52), (certNat% 53), (certNat% 54), 2305843009213693952, (certNat% 55)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), 4035278042682097664, (certNat% 58), (certNat% 59), (certNat% 60), (certNat% 61)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 1224979098644774912, (certNat% 63), 6917529027641081856, (certNat% 64), 577023702256844800]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 66), (certNat% 67), (certNat% 68), (certNat% 69)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), (certNat% 68), 4612037862148276224, (certNat% 61), (certNat% 72)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), (certNat% 74), (certNat% 75), 1224979098644774912, 6917529027641081856]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), 1224979098644774912, (certNat% 77), (certNat% 71), 6917529027641081856, 914793674309632]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), (certNat% 68), (certNat% 75), (certNat% 79), 6917529027641081856, (certNat% 61), (certNat% 80)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c23 c18
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c24 c15
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 81), 6917529027641081856, (certNat% 82), (certNat% 55), (certNat% 83), (certNat% 61)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 84), (certNat% 82), 6917529027641081856, (certNat% 36), (certNat% 85), (certNat% 86), (certNat% 83)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), 6917529027641081856, (certNat% 36), (certNat% 88), (certNat% 89), (certNat% 54), (certNat% 90), (certNat% 91)]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c30 c25
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c31 c14
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c32 c13
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c33 c12
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 92), (certNat% 93), (certNat% 19), 4469822630165217280, (certNat% 94), (certNat% 95), (certNat% 96), (certNat% 15)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), (certNat% 66), (certNat% 98), (certNat% 99), (certNat% 36)]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 100), (certNat% 101), (certNat% 32), (certNat% 33), (certNat% 99), (certNat% 61)]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 102), (certNat% 31), (certNat% 36), (certNat% 103), (certNat% 104), (certNat% 105), (certNat% 106)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 107), (certNat% 103), (certNat% 108), (certNat% 109), (certNat% 110), (certNat% 111), 3458764513820540928]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 112), (certNat% 113), 4035225266123964416, 4620904323914661888, (certNat% 36), (certNat% 75)]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 114), (certNat% 66), (certNat% 115), (certNat% 116), (certNat% 105)]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 117), (certNat% 118), (certNat% 116), 3458764513820540928, (certNat% 119), (certNat% 120)]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 121), (certNat% 122), 577023702256844800, (certNat% 113), (certNat% 36)]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 123), 2882303761517117440, (certNat% 113), (certNat% 118), (certNat% 36), 774056185954304]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c47 c46
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 124), (certNat% 116), 577023702256844800, 3458764513820540928, (certNat% 125), (certNat% 36), 4611897124659920896]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c49 c48
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c50 c45
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c51 c42
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 126), (certNat% 36), (certNat% 127), (certNat% 128), (certNat% 129), 3458764513820540928]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 130), 6917529027641081856, (certNat% 127), (certNat% 36), (certNat% 131), (certNat% 132), (certNat% 129)]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c54 c53
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 133), (certNat% 36), 6917529027641081856, (certNat% 134), (certNat% 89), (certNat% 135), (certNat% 136), 9219404998901760]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c56 c55
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c57 c52
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c58 c41
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c59 c40
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 137), (certNat% 138), (certNat% 28), (certNat% 139), (certNat% 140), (certNat% 95), (certNat% 94), (certNat% 141)]
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 142), (certNat% 143), (certNat% 144), (certNat% 63), (certNat% 55), 576460752303423488]
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 145), (certNat% 146), (certNat% 31), (certNat% 147), (certNat% 67), (certNat% 115)]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 148), (certNat% 36), (certNat% 31), (certNat% 127), (certNat% 149), (certNat% 150), (certNat% 144)]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c64 c63
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c65 c62
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 151), (certNat% 152), 4035225266123964416, (certNat% 153), (certNat% 128), (certNat% 154)]
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 155), 4611756387171565568, (certNat% 31), (certNat% 156), (certNat% 67), (certNat% 115)]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 157), (certNat% 158), (certNat% 31), (certNat% 82), (certNat% 159), (certNat% 150), (certNat% 153)]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c69 c68
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c70 c67
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 160), (certNat% 36), (certNat% 31), (certNat% 54), (certNat% 135), (certNat% 161), (certNat% 162), (certNat% 163)]
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c72 c71
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c73 c66
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 164), (certNat% 165), (certNat% 166), (certNat% 167), (certNat% 89), (certNat% 54), (certNat% 135), (certNat% 168), (certNat% 169)]
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c75 c74
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c76 c61
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c77 c60
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c78 c35
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c79 c34
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c80 c3
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c81 c2
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c82 c1
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c83 c0
  c84
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024
def vertexColumn : Fields := ⟨10, (certNat% 170)⟩
def kindColumn : Fields := ⟨3, (certNat% 171)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 172), (certNat% 173), (certNat% 174), (certNat% 175), (certNat% 176), (certNat% 177), (certNat% 178), 17557001672327168, (certNat% 179)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record024
