module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00094Data
public import GraphInputsRow29Part00094Frames
public import GraphInputsRow29Part00094Leaves
public import GraphInputsRow29Part00094Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00094.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩, ⟨93, by decide⟩, ⟨97, by decide⟩, ⟨107, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 1108101562368, (certNat% 3), (certNat% 4)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 1125281431552, 92358976733184, (certNat% 6), (certNat% 7)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 6), 3848290697216, 373834490314752, (certNat% 9), 562949953421312]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), (certNat% 13), (certNat% 14), 2305913377957871616]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), (certNat% 17), (certNat% 18), (certNat% 19)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 13), (certNat% 22), 563018672898048, (certNat% 23)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), (certNat% 26), (certNat% 27), 1099511627776]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), (certNat% 30), (certNat% 31), (certNat% 32)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), (certNat% 31), (certNat% 35), (certNat% 32), (certNat% 36)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c12 c10
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c13 c9
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), (certNat% 40), (certNat% 36)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 21), (certNat% 42), (certNat% 43), (certNat% 14), (certNat% 44)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 42), (certNat% 46), (certNat% 47), 288230376151711744]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 43), (certNat% 49), (certNat% 23), 373835027185664, (certNat% 50)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 25), (certNat% 52), (certNat% 53), (certNat% 54), 70368744177664]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), (certNat% 46), (certNat% 56), (certNat% 57), (certNat% 58), (certNat% 59)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), (certNat% 49), (certNat% 61), (certNat% 23), 373835027185664, (certNat% 62)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 64), (certNat% 65), (certNat% 66)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 57), (certNat% 66), (certNat% 68), (certNat% 65), (certNat% 69)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), (certNat% 72), (certNat% 49), (certNat% 73)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 26), 2594073385902276608, (certNat% 46), (certNat% 73), (certNat% 75)]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), (certNat% 77), 282025269395456, (certNat% 78)]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), (certNat% 80), (certNat% 81), (certNat% 82), (certNat% 64)]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), (certNat% 84), (certNat% 85), (certNat% 43), (certNat% 14), 2594073385365405696]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c33 c30
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 86), (certNat% 71), (certNat% 87), (certNat% 88), (certNat% 89)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 90), (certNat% 91), (certNat% 92), (certNat% 68), (certNat% 93)]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 94), (certNat% 95), (certNat% 43), (certNat% 96)]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), 2594073385365405696, (certNat% 98), 373833953443840, (certNat% 93)]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 99), (certNat% 100), (certNat% 101), (certNat% 98)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 102), (certNat% 98), 373833953443840, (certNat% 103), (certNat% 104), (certNat% 93)]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨107, by decide⟩ c41 c38
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c42 c37
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c43 c36
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 105), (certNat% 61), (certNat% 38), (certNat% 14), (certNat% 29), (certNat% 75), 2306194853471453184]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c45 c44
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c46 c35
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c47 c34
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c48 c29
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c49 c26
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c50 c23
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c51 c22
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c52 c21
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c53 c20
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c54 c17
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c55 c14
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c56 c8
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c57 c5
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c58 c4
  c59
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00094.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00094.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003
def vertexColumn : Fields := ⟨10, (certNat% 106)⟩
def kindColumn : Fields := ⟨3, (certNat% 107)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨83, by decide⟩, ⟨90, by decide⟩, ⟨97, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩, ⟨107, by decide⟩, ⟨110, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 108), (certNat% 109), 166914661189419008, (certNat% 110), (certNat% 111)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 112), (certNat% 113), 452611762550734848, (certNat% 114), (certNat% 115)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 116), (certNat% 113), 452611762550734848, (certNat% 114), (certNat% 117)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 118), (certNat% 113), 452611762550734848, (certNat% 114), (certNat% 119)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 120), (certNat% 113), 13088586417045504, (certNat% 121), 450359962737049600, (certNat% 122)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 123), (certNat% 124), 16747761114284032, 306244774661193728, (certNat% 125), (certNat% 126)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 127), (certNat% 128), 450361062248677376, (certNat% 129), (certNat% 130), (certNat% 109)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 131), (certNat% 124), 17732923532771328, 432345564227567616, (certNat% 132), (certNat% 125)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 133), 17873661021126656, (certNat% 113), (certNat% 134), (certNat% 135), (certNat% 132), 162138451397836800]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00094.record003
