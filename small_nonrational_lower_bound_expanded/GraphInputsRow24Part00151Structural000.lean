module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00151Data
public import GraphInputsRow24Part00151Frames
public import GraphInputsRow24Part00151Leaves
public import GraphInputsRow24Part00151Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨90, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 447314132992, 1410676639662080]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), 2161727821154615296, (certNat% 8), 140746078289920]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 5), (certNat% 10), 515429629952, (certNat% 11), 1971427569827840]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 14), (certNat% 15), (certNat% 16), 16777216]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 1585267068834414592, (certNat% 18), (certNat% 19), 515463184384]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), 1972523860230144, (certNat% 23)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), (certNat% 5), (certNat% 26), 379097972736, 4611686018427387904]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), 1585267068851191808, (certNat% 29), (certNat% 30), (certNat% 31)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 33), 378024230912, 1973623371857920, 432345564227567616, (certNat% 34)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), 2043992116035584, (certNat% 36), (certNat% 37), (certNat% 38), (certNat% 39), 390925910016]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003
def vertexColumn : Fields := ⟨10, (certNat% 40)⟩
def kindColumn : Fields := ⟨3, (certNat% 41)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), (certNat% 44), 288230376151711744]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 46), (certNat% 47), (certNat% 48), (certNat% 49)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), 1128100012228608, (certNat% 51), (certNat% 52), 324259173170675712, (certNat% 53)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 1266637395197952, (certNat% 55), (certNat% 43), (certNat% 56)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), 1128102151323648, (certNat% 55), (certNat% 59), (certNat% 60)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 61)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c0 c12
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 288230376151711744, (certNat% 63)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), (certNat% 65), 288230376302706688, (certNat% 66)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c17 c15
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 46), (certNat% 68), 1266637395197952, 481120223232]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), (certNat% 65), (certNat% 70), (certNat% 71), 481103446016]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), (certNat% 65), (certNat% 43), (certNat% 73), (certNat% 74), 498417532928]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c23 c20
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), (certNat% 76), (certNat% 77), (certNat% 78), (certNat% 49)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), (certNat% 46), (certNat% 80), (certNat% 81), 515463184384]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 82), (certNat% 46), (certNat% 65), 532777271296, (certNat% 83), (certNat% 84)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c28 c25
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), (certNat% 86), (certNat% 87), (certNat% 84), (certNat% 88), (certNat% 89)]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 90), (certNat% 91), (certNat% 92), (certNat% 93), 498434310144, (certNat% 70)]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 94), (certNat% 95), 532710162432, (certNat% 92), (certNat% 96), (certNat% 97)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 98), (certNat% 59), (certNat% 99), (certNat% 100), (certNat% 101)]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 102), (certNat% 81), 1125970782191616, (certNat% 103), 412316860416]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c0 c1
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c0 c35
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c0 c1
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 104), (certNat% 105), 103079215104]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c38 c37
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c39 c36
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 106), (certNat% 43), 240518168576, 1125902054326272]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 107), (certNat% 108), 1125970782191616, (certNat% 103), 171798691840]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c43 c42
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 109), (certNat% 110), (certNat% 76), (certNat% 111)]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c0 c35
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 112), (certNat% 47), (certNat% 113), (certNat% 111)]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c47 c46
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 114), (certNat% 115), (certNat% 116), (certNat% 103)]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 117), (certNat% 111), (certNat% 118), (certNat% 116), 36028797018963968]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c50 c49
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c51 c48
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c52 c45
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c0 c1
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 119), (certNat% 47), (certNat% 120), 206158430208]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c55 c54
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 121), 208314302464, 1125899906842624, (certNat% 116), (certNat% 103)]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c57 c56
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 122), (certNat% 123), (certNat% 111), (certNat% 118), 171932909568, (certNat% 124)]
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c59 c58
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c60 c53
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c61 c44
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c62 c34
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c63 c33
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 125), (certNat% 126), (certNat% 127), (certNat% 84), 532777271296, 324259173187452928, (certNat% 128)]
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c65 c64
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c66 c32
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c67 c31
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c68 c30
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c69 c29
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c70 c24
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c71 c11
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c72 c8
  c73
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5d26c3713c1f1729a8da4e87ac9a665999695956359361da4e33a2e4b8ae1b91e2785e0fa694e479c9665656554d4759362d4b4ad1b51d1743dc8e6364e534cc7392e2b4acab1ad1b16c3bc1e8761e4789d2729c6785d1725c570de0f43c8f13c2f07e641b09c172621a89a1689989525454952342d0762348d1324c8b0ac1b"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a4d349a69b6db6db6d349b6d24d36924924934da49249b6d26da4db69a449249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 23), (facetIndex 31), (facetIndex 32), (facetIndex 53), (facetIndex 67)]))
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 94), (facetIndex 99)])))
 (.branch 3
 (.leaf ([(facetIndex 45), (facetIndex 48), (facetIndex 54), (facetIndex 95)]))
 (.branch 4
 (.leaf ([(facetIndex 24), (facetIndex 42), (facetIndex 46), (facetIndex 47), (facetIndex 55)]))
 (.leaf ([(facetIndex 59), (facetIndex 62), (facetIndex 68), (facetIndex 100)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 51), (facetIndex 56), (facetIndex 65), (facetIndex 92), (facetIndex 97)]))
 (.leaf ([(facetIndex 57), (facetIndex 58), (facetIndex 60)])))
 (.branch 8
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 61), (facetIndex 69)]))
 (.branch 9
 (.leaf ([(facetIndex 26), (facetIndex 77), (facetIndex 90)]))
 (.leaf ([(facetIndex 43), (facetIndex 44)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "41050210508000000000000801100007400500476466532005002332993000077000000000803z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 25), (facetIndex 49), (facetIndex 50), (facetIndex 52)]))
 (.leaf ([(facetIndex 30), (facetIndex 63), (facetIndex 64), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 29), (facetIndex 70), (facetIndex 71), (facetIndex 96)]))
 (.leaf ([(facetIndex 28), (facetIndex 34), (facetIndex 72)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 73), (facetIndex 93), (facetIndex 101)]))
 (.leaf ([(facetIndex 27), (facetIndex 83), (facetIndex 98)])))
 (.branch 7
 (.leaf ([(facetIndex 33), (facetIndex 35), (facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 76), (facetIndex 80), (facetIndex 81), (facetIndex 84), (facetIndex 86)]))
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 82), (facetIndex 85), (facetIndex 87), (facetIndex 88), (facetIndex 89), (facetIndex 91)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "20142020e3ffbebf6fc6023480041200000000000000036d80cf0053az14;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0002 : List Nat := [5, 6]
def grouped2_0003 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0004 : List Nat := [7]
def grouped2_0005 : List Nat := [7, 8, 9]
def grouped2_0006 : List Nat := [8]
def grouped2_0007 : List Nat := [8, 9]
def grouped2_0008 : List Nat := [9]
def grouped3_0009 : List Nat := [0]
def grouped3_0010 : List Nat := [0, 1]
def grouped3_0011 : List Nat := [0, 1, 2, 3]
def grouped3_0013 : List Nat := [1]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [2, 3]
def grouped3_0016 : List Nat := [3]
def grouped3_0017 : List Nat := [4]
def grouped3_0018 : List Nat := [4, 5]
def grouped3_0019 : List Nat := [4, 5, 6, 7]
def grouped3_0020 : List Nat := [5]
def grouped3_0021 : List Nat := [6]
def grouped3_0022 : List Nat := [6, 7]
def grouped3_0023 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record005" 100

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record005" "{\"ridges\":[[4,274],[5,290],[6,515],[11,276],[12,292],[13,517],[19,84],[21,76],[22,580],[27,270],[28,526],[32,276],[33,534],[36,292],[37,517],[38,71],[40,646],[41,774],[43,82],[44,274],[47,290],[48,515],[51,274],[51,290],[53,274],[54,515],[55,290],[55,515],[57,84],[58,276],[59,76],[61,292],[62,517],[65,276],[65,292],[67,276],[68,517],[68,580],[69,292],[69,517],[71,312],[74,84],[77,76],[79,270],[84,54],[86,326],[89,326],[90,580],[91,774],[93,312],[96,368],[98,312],[99,84],[100,580],[101,368]],\"owners\":[[4,274,[76,84,86,88,93,96],[32,44,51,53]],[44,274,[84,86,88,96],[4,32,51,53,76,93]],[51,274,[76,86,88],[4,32,44,53,84,93,96]],[53,274,[76,84,86,93,96],[4,32,44,51,88]],[5,290,[79,84,89,91,93,96],[36,47,51,55]],[47,290,[84,89,91,96],[5,36,51,55,79,93]],[51,290,[79,89,91],[5,36,47,55,84,93,96]],[55,290,[79,84,89,93,96],[5,36,47,51,91]],[6,515,[28,33,38,40,41,49,52],[37,48,54,55]],[48,515,[33,38,40,41,52],[6,28,37,49,54,55]],[54,515,[28,33,40,41],[6,37,38,48,49,52,55]],[55,515,[28,33,38,40,49,52],[6,37,41,48,54]],[11,276,[76,84,86,88,98,101],[32,58,65,67]],[32,276,[98,101],[11,58,65,67,76,84,86,88]],[58,276,[84,86,88,101],[11,32,65,67,76,98]],[65,276,[76,86,88],[11,32,58,67,84,98,101]],[67,276,[76,84,86,98,101],[11,32,58,65,88]],[12,292,[79,84,89,91,98,101],[36,61,65,69]],[36,292,[98,101],[12,61,65,69,79,84,89,91]],[61,292,[84,89,91,101],[12,36,65,69,79,98]],[65,292,[79,89,91],[12,36,61,69,84,98,101]],[69,292,[79,84,89,98,101],[12,36,61,65,91]],[13,517,[28,33,38,40,41,63,66],[37,62,68,69]],[37,517,[63,66],[13,28,33,38,40,41,62,68,69]],[62,517,[33,38,40,41,66],[13,28,37,63,68,69]],[68,517,[28,33,40,41],[13,37,38,62,63,66,69]],[69,517,[28,33,38,40,63,66],[13,37,41,62,68]],[43,82,[83,85,86,87,96],[15,30,50,52,74,92,94]],[21,76,[19,25,57,63,74,81,82,99],[59,77,100]],[59,76,[19,74,81,82,99],[21,25,57,63,77,100]],[77,76,[19,57,63,99],[21,25,59,74,81,82,100]],[19,84,[30,64,66,83,85,86,87,101],[57,74,97,99]],[57,84,[83,85,86,87,101],[19,30,64,66,74,97,99]],[74,84,[64,66,101],[19,30,57,83,85,86,87,97,99]],[99,84,[30,64,66,83,86,87,101],[19,57,74,85,97]],[22,580,[38,63,66,82,87],[68,90,100]],[68,580,[82,87],[22,38,63,66,90,100]],[90,580,[63,66],[22,38,68,82,87,100]],[100,580,[38,66,87],[22,63,68,82,90]],[38,71,[25,30,34],[]],[27,270,[76,79],[]],[79,270,[27,76],[]],[28,526,[80,82],[]],[84,54,[29,73,83],[]],[33,534,[87],[]],[40,646,[],[]],[41,774,[91],[]],[91,774,[41],[]],[71,312,[93,98],[]],[93,312,[71,98],[]],[98,312,[71,93],[]],[86,326,[89],[]],[89,326,[86],[]],[96,368,[101],[]],[101,368,[96],[]]],\"edges\":[[8,[6,13,28,33,37,38,40,41,48,49,52,54,55,62,63,66,68,69,72]],[15,[4,5,27,32,36,39,41,44,47,51,53,55,76,79,84,86,88,89,91,93,96]],[20,[19,21,22,25,30,34,38,57,59,63,64,66,68,74,77,81,82,83,85,86,87,89,90,97,99,100,101]],[23,[13,22,28,33,37,38,40,41,62,63,66,68,69,80,82,87,90,91,100]],[33,[4,11,32,44,51,53,58,65,67,71,76,84,86,88,93,96,98,101]],[37,[5,12,36,47,51,55,61,65,69,71,79,84,89,91,93,96,98,101]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-26,-14],[-26,-17],[-30,-24],[-32,-17],[-36,-17],[-38,-14],[-42,-24],[-44,-17],[-46,-14],[-47,-41],[-51,-17],[-51,-24],[-57,-47],[-58,-11],[-58,-20],[-58,-52],[-59,-58],[-60,-17],[-60,-24],[-61,-58],[-62,-17],[-62,-24],[-64,-58],[-68,-47],[-72,-71],[-1,51,58,60,62,66,67],[-26,58,60,62,67],[-30,51,60,62],[-32,51,58,60,66,67],[-2,53,58,63,65,66,67],[-27,58,63,65,67],[-30,53,63,65],[-34,53,58,63,66,67],[-3,13,17,21,23,24,29,31],[-28,17,21,23,24,31],[-33,13,17,23,24],[-34,13,17,21,23,29,31],[-4,51,58,60,62,69,72],[-16,69,72],[-36,58,60,62,72],[-42,51,60,62],[-44,51,58,60,69,72],[-5,53,58,63,65,69,72],[-19,69,72],[-38,58,63,65,72],[-42,53,63,65],[-46,53,58,63,69,72],[-6,13,17,21,23,24,40,43],[-20,40,43],[-39,17,21,23,24,43],[-45,13,17,23,24],[-46,13,17,21,23,40,43],[-25,57,59,60,61,67],[-8,7,10,35,40,50,55,56,70],[-37,7,50,55,56,70],[-52,7,35,40,70],[-7,15,41,43,57,59,60,61,72],[-35,57,59,60,61,72],[-50,41,43,72],[-70,15,41,43,57,60,61,72],[-9,21,40,43,56,61],[-45,56,61],[-64,40,43],[-71,21,43,61],[-21,10,15,18],[-12,51,53],[-53,12,51],[-13,54,56],[-58,14,49,57],[-17,61],[-23],[-24,65],[-65,24],[-47,66,69],[-66,47,69],[-69,47,66],[-60,63],[-63,60],[-67,72],[-72,67],[-73,19,20,38,46],[-74,11,52,64],[-75,25,26],[-76,74,75],[-77,73,76],[-78,77],[-79,78],[79],[-10,80],[-29,80],[-31,80],[-15,81],[-40,81],[-43,81],[-14,82],[-47,82],[-67,82],[-13,83],[-18,83],[-48,83],[-49,84],[-66,84],[-72,84],[-12,85],[-57,85],[-69,85],[-17,86],[-21,86],[-22,86],[-24,86],[-51,86],[-54,86],[-55,86],[-58,86],[-60,86],[-53,87],[-56,87],[-59,87],[-61,87],[-62,87],[-63,87],[-65,87],[-81,88],[-80,88],[-83,89],[-82,89],[-82,-83,90],[-89,91],[-90,92],[-88,91],[-88,-89,92],[-85,93],[-84,93],[-84,-85,94],[-87,95],[-86,95],[-86,-87,96],[-96,98],[-93,97],[-93,-95,98],[-93,-96,99],[-94,98],[-99,100],[-91,-98,100],[-92,-97,100],[-100],[3,6,13,17,20,21,23,24,28,29,31,33,34,39,40,43,45,46,48],[1,2,12,16,19,22,24,26,27,30,32,34,51,53,58,60,62,63,65,66,67],[7,8,9,10,15,18,21,35,37,40,41,43,45,50,52,55,56,57,59,60,61,63,64,68,70,71,72],[6,9,13,17,20,21,23,24,39,40,43,45,46,54,56,61,64,65,71],[1,4,16,26,30,32,36,42,44,47,51,58,60,62,66,67,69,72],[2,5,19,27,30,34,38,42,46,47,53,58,63,65,66,67,69,72]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":44,\"b\":29},{\"tag\":\"incompatible\",\"a\":44,\"b\":33},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":53,\"b\":33},{\"tag\":\"incompatible\",\"a\":58,\"b\":33},{\"tag\":\"incompatible\",\"a\":61,\"b\":29},{\"tag\":\"incompatible\",\"a\":65,\"b\":41},{\"tag\":\"incompatible\",\"a\":67,\"b\":33},{\"tag\":\"incompatible\",\"a\":69,\"b\":29},{\"tag\":\"incompatible\",\"a\":71,\"b\":64},{\"tag\":\"incompatible\",\"a\":76,\"b\":33},{\"tag\":\"incompatible\",\"a\":76,\"b\":41},{\"tag\":\"incompatible\",\"a\":83,\"b\":71},{\"tag\":\"incompatible\",\"a\":84,\"b\":26},{\"tag\":\"incompatible\",\"a\":84,\"b\":37},{\"tag\":\"incompatible\",\"a\":84,\"b\":77},{\"tag\":\"incompatible\",\"a\":85,\"b\":84},{\"tag\":\"incompatible\",\"a\":86,\"b\":33},{\"tag\":\"incompatible\",\"a\":86,\"b\":41},{\"tag\":\"incompatible\",\"a\":87,\"b\":84},{\"tag\":\"incompatible\",\"a\":88,\"b\":33},{\"tag\":\"incompatible\",\"a\":88,\"b\":41},{\"tag\":\"incompatible\",\"a\":90,\"b\":84},{\"tag\":\"incompatible\",\"a\":97,\"b\":71},{\"tag\":\"incompatible\",\"a\":101,\"b\":100},{\"tag\":\"mate\",\"ridge\":274,\"a\":4,\"owners\":[76,84,86,88,93,96]},{\"tag\":\"mate\",\"ridge\":274,\"a\":44,\"owners\":[84,86,88,96]},{\"tag\":\"mate\",\"ridge\":274,\"a\":51,\"owners\":[76,86,88]},{\"tag\":\"mate\",\"ridge\":274,\"a\":53,\"owners\":[76,84,86,93,96]},{\"tag\":\"mate\",\"ridge\":290,\"a\":5,\"owners\":[79,84,89,91,93,96]},{\"tag\":\"mate\",\"ridge\":290,\"a\":47,\"owners\":[84,89,91,96]},{\"tag\":\"mate\",\"ridge\":290,\"a\":51,\"owners\":[79,89,91]},{\"tag\":\"mate\",\"ridge\":290,\"a\":55,\"owners\":[79,84,89,93,96]},{\"tag\":\"mate\",\"ridge\":515,\"a\":6,\"owners\":[28,33,38,40,41,49,52]},{\"tag\":\"mate\",\"ridge\":515,\"a\":48,\"owners\":[33,38,40,41,52]},{\"tag\":\"mate\",\"ridge\":515,\"a\":54,\"owners\":[28,33,40,41]},{\"tag\":\"mate\",\"ridge\":515,\"a\":55,\"owners\":[28,33,38,40,49,52]},{\"tag\":\"mate\",\"ridge\":276,\"a\":11,\"owners\":[76,84,86,88,98,101]},{\"tag\":\"mate\",\"ridge\":276,\"a\":32,\"owners\":[98,101]},{\"tag\":\"mate\",\"ridge\":276,\"a\":58,\"owners\":[84,86,88,101]},{\"tag\":\"mate\",\"ridge\":276,\"a\":65,\"owners\":[76,86,88]},{\"tag\":\"mate\",\"ridge\":276,\"a\":67,\"owners\":[76,84,86,98,101]},{\"tag\":\"mate\",\"ridge\":292,\"a\":12,\"owners\":[79,84,89,91,98,101]},{\"tag\":\"mate\",\"ridge\":292,\"a\":36,\"owners\":[98,101]},{\"tag\":\"mate\",\"ridge\":292,\"a\":61,\"owners\":[84,89,91,101]},{\"tag\":\"mate\",\"ridge\":292,\"a\":65,\"owners\":[79,89,91]},{\"tag\":\"mate\",\"ridge\":292,\"a\":69,\"owners\":[79,84,89,98,101]},{\"tag\":\"mate\",\"ridge\":517,\"a\":13,\"owners\":[28,33,38,40,41,63,66]},{\"tag\":\"mate\",\"ridge\":517,\"a\":37,\"owners\":[63,66]},{\"tag\":\"mate\",\"ridge\":517,\"a\":62,\"owners\":[33,38,40,41,66]},{\"tag\":\"mate\",\"ridge\":517,\"a\":68,\"owners\":[28,33,40,41]},{\"tag\":\"mate\",\"ridge\":517,\"a\":69,\"owners\":[28,33,38,40,63,66]},{\"tag\":\"mate\",\"ridge\":82,\"a\":43,\"owners\":[83,85,86,87,96]},{\"tag\":\"mate\",\"ridge\":76,\"a\":21,\"owners\":[19,25,57,63,74,81,82,99]},{\"tag\":\"mate\",\"ridge\":76,\"a\":59,\"owners\":[19,74,81,82,99]},{\"tag\":\"mate\",\"ridge\":76,\"a\":77,\"owners\":[19,57,63,99]},{\"tag\":\"mate\",\"ridge\":84,\"a\":19,\"owners\":[30,64,66,83,85,86,87,101]},{\"tag\":\"mate\",\"ridge\":84,\"a\":57,\"owners\":[83,85,86,87,101]},{\"tag\":\"mate\",\"ridge\":84,\"a\":74,\"owners\":[64,66,101]},{\"tag\":\"mate\",\"ridge\":84,\"a\":99,\"owners\":[30,64,66,83,86,87,101]},{\"tag\":\"mate\",\"ridge\":580,\"a\":22,\"owners\":[38,63,66,82,87]},{\"tag\":\"mate\",\"ridge\":580,\"a\":68,\"owners\":[82,87]},{\"tag\":\"mate\",\"ridge\":580,\"a\":90,\"owners\":[63,66]},{\"tag\":\"mate\",\"ridge\":580,\"a\":100,\"owners\":[38,66,87]},{\"tag\":\"mate\",\"ridge\":71,\"a\":38,\"owners\":[25,30,34]},{\"tag\":\"mate\",\"ridge\":270,\"a\":27,\"owners\":[76,79]},{\"tag\":\"mate\",\"ridge\":270,\"a\":79,\"owners\":[27,76]},{\"tag\":\"mate\",\"ridge\":526,\"a\":28,\"owners\":[80,82]},{\"tag\":\"mate\",\"ridge\":54,\"a\":84,\"owners\":[29,73,83]},{\"tag\":\"mate\",\"ridge\":534,\"a\":33,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":646,\"a\":40,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":774,\"a\":41,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":774,\"a\":91,\"owners\":[41]},{\"tag\":\"mate\",\"ridge\":312,\"a\":71,\"owners\":[93,98]},{\"tag\":\"mate\",\"ridge\":312,\"a\":93,\"owners\":[71,98]},{\"tag\":\"mate\",\"ridge\":312,\"a\":98,\"owners\":[71,93]},{\"tag\":\"mate\",\"ridge\":326,\"a\":86,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":326,\"a\":89,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":368,\"a\":96,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":368,\"a\":101,\"owners\":[96]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[36,37,61,69],\"full_literals\":[-73,19,20,38,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[26,77,90],\"full_literals\":[-74,11,52,64]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[43,44],\"full_literals\":[-75,25,26]},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-76,74,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0005\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,73,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,false,77],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-79,false,78],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":25,\"full_literals\":[-10,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-29,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":52,\"full_literals\":[-31,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":30,\"full_literals\":[-15,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":63,\"full_literals\":[-40,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-43,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":29,\"full_literals\":[-14,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":71,\"full_literals\":[-47,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":96,\"full_literals\":[-67,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":28,\"full_literals\":[-13,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":34,\"full_literals\":[-18,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-48,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":73,\"full_literals\":[-49,84]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":93,\"full_literals\":[-66,84]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":101,\"full_literals\":[-72,84]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":27,\"full_literals\":[-12,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-57,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":98,\"full_literals\":[-69,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":33,\"full_literals\":[-17,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":38,\"full_literals\":[-21,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":39,\"full_literals\":[-22,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":41,\"full_literals\":[-24,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":76,\"full_literals\":[-51,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-54,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":81,\"full_literals\":[-55,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-58,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-60,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":79,\"full_literals\":[-53,87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":82,\"full_literals\":[-56,87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":85,\"full_literals\":[-59,87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":87,\"full_literals\":[-61,87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":88,\"full_literals\":[-62,87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":89,\"full_literals\":[-63,87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":91,\"full_literals\":[-65,87]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-81,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-80,false,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-82,-83,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-89,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-90,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-88,false,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-88,-89,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-85,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-84,false,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-84,-85,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-86,false,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-86,-87,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-96,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-93,false,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-93,-95,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-93,-96,99],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-94,false,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-99,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-91,-98,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-92,-97,100],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":8,\"owners\":[6,13,28,33,37,38,40,41,48,49,52,54,55,62,63,66,68,69,72]},{\"tag\":\"edge\",\"edge\":15,\"owners\":[4,5,27,32,36,39,41,44,47,51,53,55,76,79,84,86,88,89,91,93,96]},{\"tag\":\"edge\",\"edge\":20,\"owners\":[19,21,22,25,30,34,38,57,59,63,64,66,68,74,77,81,82,83,85,86,87,89,90,97,99,100,101]},{\"tag\":\"edge\",\"edge\":23,\"owners\":[13,22,28,33,37,38,40,41,62,63,66,68,69,80,82,87,90,91,100]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[4,11,32,44,51,53,58,65,67,71,76,84,86,88,93,96,98,101]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[5,12,36,47,51,55,61,65,69,71,79,84,89,91,93,96,98,101]}]}"
  "153 78 0 88 87 0\n154 77 0 153 86 0\n155 -99 0 146 143 0\n156 3 6 13 17 20 21 24 28 29 31 33 34 39 40 43 45 46 48 0 71 147 0\n157 6 9 13 17 20 21 24 39 40 43 45 46 54 56 61 64 65 71 0 71 150 0\n158 17 24 91 0 71 130 123 94 93 49 92 124 89 128 125 99 65 91 90 100 98 52 37 34 36 51 48 50 35 156 0\n159 -17 93 82 0 132 105 95 133 101 69 97 80 106 39 102 96 2 4 5 8 11 18 21 26 28 38 41 151 0\n160 93 91 0 128 126 97 80 96 95 132 133 105 106 101 102 39 69 159 158 3 7 12 19 22 26 29 38 42 27 40 151 0\n161 -24 96 0 72 110 122 137 0\n162 91 0 155 160 141 161 158 70 107 119 137 0\n163 -98 0 162 146 144 0\n164 -96 0 163 138 0\n165 -94 0 163 142 0\n166 -24 0 164 161 0\n167 -65 0 166 73 0\n168 69 47 32 72 95 0 167 166 136 115 135 120 114 79 27 121 31 116 111 66 32 109 39 44 75 26 30 33 148 0\n169 -69 47 0 165 76 106 102 134 0\n170 47 32 95 72 0 168 169 0\n171 -47 72 -93 0 146 163 140 135 119 117 62 136 115 113 108 121 118 139 145 129 10 13 24 96 58 126 127 131 99 123 124 92 93 94 89 57 60 63 61 64 59 54 55 56 149 0\n172 72 -93 0 163 140 136 115 114 111 79 171 170 169 29 75 0\n173 -93 0 163 146 71 167 166 139 140 145 135 136 117 119 107 108 112 62 68 172 25 80 97 126 131 123 93 94 49 63 61 52 48 50 157 0\n174 -85 0 173 132 0\n175 -84 0 173 133 0\n176 -12 0 174 104 0\n177 -57 0 174 105 0\n178 -69 0 174 106 0\n179 -49 0 175 101 0\n180 -66 0 175 102 0\n181 -72 0 175 103 0\n182 -19 0 178 181 44 0\n183 -47 0 180 178 74 0\n184 -67 0 181 79 0\n185 53 58 63 0 181 178 184 180 167 183 182 31 45 32 46 43 47 30 33 152 0\n186 -53 0 176 164 67 116 111 137 0\n187 60 0 186 179 184 177 182 154 78 185 14 15 16 17 20 23 69 82 53 1 6 9 83 81 84 85 0\n188 63 0 187 77 0\n189 86 0 187 115 0\n190 87 0 188 121 0\n191 0 189 190 164 137 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9b13c2f07c9a93a2e87ac9a66599968d9362d876938ce8b92e2b86e4789e1783e9a5391e72599565656354d475934cd8b52d1b51d1743dc8e6358d938cd331ce4b32e2b4ac6b46c5b0ef07a1d8791d4731e2749c6785d1725c570de0f43c8f13c2f07e644d06c2703c989321a89a0e899915152548d1341d90d1324c8b12c1b"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1249249a6da6db6da69a6db4d34d26d249a69a6936924db4db6da4db693449249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 23), (facetIndex 31), (facetIndex 32), (facetIndex 54), (facetIndex 69)]))
 (.leaf ([(facetIndex 50), (facetIndex 65), (facetIndex 97), (facetIndex 101)])))
 (.branch 3
 (.leaf ([(facetIndex 25), (facetIndex 26), (facetIndex 49), (facetIndex 64)]))
 (.leaf ([(facetIndex 43), (facetIndex 45), (facetIndex 95), (facetIndex 96)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 58), (facetIndex 60), (facetIndex 99), (facetIndex 100)]))
 (.leaf ([(facetIndex 46), (facetIndex 52), (facetIndex 56), (facetIndex 61), (facetIndex 67), (facetIndex 71)])))
 (.branch 7
 (.leaf ([(facetIndex 44), (facetIndex 59), (facetIndex 94), (facetIndex 98)]))
 (.leaf ([(facetIndex 39), (facetIndex 76), (facetIndex 78), (facetIndex 80), (facetIndex 88), (facetIndex 92)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "c98b7870070000071c7000a00a0a02cd0500505015e600e0000000009z13;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record006" 42

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record006" "{\"ridges\":[[41,646],[50,515],[65,517],[68,561],[71,517],[72,801],[89,534],[93,774],[97,546],[101,548]],\"owners\":[[50,515,[33,36,41,42,53,57],[5,28,39,48,56]],[65,517,[33,36,41,42,68,72],[11,28,39,63,71]],[71,517,[28,33,41,42],[11,36,39,63,65,68,72]],[97,546,[36,53,57,89,93],[17,48,56,83,92]],[101,548,[36,68,72,89,93],[22,63,71,83,92]],[89,534,[33],[]],[41,646,[],[]],[93,774,[42],[]],[68,561,[53],[]],[72,801,[57],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-5,-1],[-5,-3],[-5,-4],[-9,-7],[-10,-6],[-11,-2],[-11,-7],[-11,-10],[-12,-6],[-13,-10],[-13,-12],[-14,-5],[-15,-6],[-15,-11],[-15,-13],[-16,-10],[-16,-12],[-16,-15],[-17,-6],[-17,-13],[-17,-16],[-19,-6],[-19,-13],[-19,-16],[-21,-5],[-22,-6],[-22,-13],[-22,-16],[-24,-9],[-25,-9],[-26,-9],[-27,-9],[-29,-9],[-11,5,6,8,9,13,16],[-18,5,6,8,9,20,23],[-22,2,5,8,9],[-31,6,13,16,28,30],[-32,6,20,23,28,30],[-28,5],[-8],[-30,9],[-20,13],[-23,16],[-33,1,3,4,14,21],[-34,11,18,31,32],[-35,10,12,15,17,19,22],[-36,7,24,25,26,27,29],[-37,33],[-37,34],[-38,37],[-39,35],[-40,36],[-41,39],[-41,40],[-42,38],[-42,41],[42]],\"atoms\":[{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":33,\"b\":23},{\"tag\":\"incompatible\",\"a\":33,\"b\":31},{\"tag\":\"incompatible\",\"a\":33,\"b\":32},{\"tag\":\"incompatible\",\"a\":42,\"b\":39},{\"tag\":\"incompatible\",\"a\":46,\"b\":36},{\"tag\":\"incompatible\",\"a\":50,\"b\":28},{\"tag\":\"incompatible\",\"a\":50,\"b\":39},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":36},{\"tag\":\"incompatible\",\"a\":53,\"b\":46},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":33},{\"tag\":\"incompatible\",\"a\":56,\"b\":36},{\"tag\":\"incompatible\",\"a\":56,\"b\":50},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":46},{\"tag\":\"incompatible\",\"a\":57,\"b\":52},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":61,\"b\":36},{\"tag\":\"incompatible\",\"a\":61,\"b\":53},{\"tag\":\"incompatible\",\"a\":61,\"b\":57},{\"tag\":\"incompatible\",\"a\":67,\"b\":36},{\"tag\":\"incompatible\",\"a\":67,\"b\":53},{\"tag\":\"incompatible\",\"a\":67,\"b\":57},{\"tag\":\"incompatible\",\"a\":69,\"b\":33},{\"tag\":\"incompatible\",\"a\":71,\"b\":36},{\"tag\":\"incompatible\",\"a\":71,\"b\":53},{\"tag\":\"incompatible\",\"a\":71,\"b\":57},{\"tag\":\"incompatible\",\"a\":76,\"b\":42},{\"tag\":\"incompatible\",\"a\":78,\"b\":42},{\"tag\":\"incompatible\",\"a\":80,\"b\":42},{\"tag\":\"incompatible\",\"a\":88,\"b\":42},{\"tag\":\"incompatible\",\"a\":92,\"b\":42},{\"tag\":\"mate\",\"ridge\":515,\"a\":50,\"owners\":[33,36,41,42,53,57]},{\"tag\":\"mate\",\"ridge\":517,\"a\":65,\"owners\":[33,36,41,42,68,72]},{\"tag\":\"mate\",\"ridge\":517,\"a\":71,\"owners\":[28,33,41,42]},{\"tag\":\"mate\",\"ridge\":546,\"a\":97,\"owners\":[36,53,57,89,93]},{\"tag\":\"mate\",\"ridge\":548,\"a\":101,\"owners\":[36,68,72,89,93]},{\"tag\":\"mate\",\"ridge\":534,\"a\":89,\"owners\":[33]},{\"tag\":\"mate\",\"ridge\":646,\"a\":41,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":774,\"a\":93,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":561,\"a\":68,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":801,\"a\":72,\"owners\":[57]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[23,31,32,54,69],\"full_literals\":[-33,1,3,4,14,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[50,65,97,101],\"full_literals\":[-34,11,18,31,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[46,52,56,61,67,71],\"full_literals\":[-35,10,12,15,17,19,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[39,76,78,80,88,92],\"full_literals\":[-36,7,24,25,26,27,29]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-37,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-38,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-39,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-40,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-41,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-42,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-42,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "58 38 0 57 55 0\n59 41 0 57 56 0\n60 37 0 58 50 0\n61 39 0 59 53 0\n62 40 0 59 54 0\n63 33 0 60 48 0\n64 34 0 60 49 0\n65 35 0 61 51 0\n66 36 0 62 52 0\n67 -6 15 22 0 65 5 9 19 22 46 0\n68 -6 22 0 13 67 0\n69 -5 4 0 63 1 2 12 25 44 0\n70 -6 0 26 68 0\n71 -5 0 3 69 0\n72 -28 0 71 39 0\n73 -13 22 -11 0 65 14 8 11 20 23 46 0\n74 9 -11 0 71 40 70 65 14 8 6 36 73 34 17 21 24 46 0\n75 -11 0 66 7 74 29 30 31 32 33 47 0\n76 -9 0 66 4 29 30 31 32 33 47 0\n77 -30 0 76 41 0\n78 13 16 0 76 40 71 72 70 77 75 64 43 42 37 35 38 45 0\n79 -13 0 65 10 11 15 20 23 27 46 0\n80 16 0 79 78 0\n81 -10 0 80 16 0\n82 -12 0 80 17 0\n83 -15 0 80 18 0\n84 -17 0 80 21 0\n85 -19 0 80 24 0\n86 -22 0 80 28 0\n87 0 84 85 65 82 81 83 86 46 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5a8dac9a669587663a4e4b86e4785e5a4d9c9665954756364d4b46d4745dc8d6394cd31cd8b92d4b32d2b1ad1bc1e8761e4729c6785d1715c3783c4f0bc9c9889a16a26498964388e07a6126459895252550d2341d90e2348c6324c5342c8b12c1b81d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6926d34d26926d34d2492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 51), (facetIndex 56), (facetIndex 70), (facetIndex 82)]))
 (.leaf ([(facetIndex 35), (facetIndex 61), (facetIndex 63), (facetIndex 65)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 39), (facetIndex 42), (facetIndex 44), (facetIndex 60), (facetIndex 68), (facetIndex 72), (facetIndex 80)]))
 (.leaf ([(facetIndex 38), (facetIndex 43), (facetIndex 47), (facetIndex 59), (facetIndex 69), (facetIndex 81)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 73), (facetIndex 75), (facetIndex 77)]))
 (.leaf ([(facetIndex 49), (facetIndex 52), (facetIndex 53), (facetIndex 55), (facetIndex 57), (facetIndex 58)])))
 (.branch 7
 (.leaf ([(facetIndex 37), (facetIndex 40), (facetIndex 41), (facetIndex 45), (facetIndex 46)]))
 (.leaf ([(facetIndex 50), (facetIndex 54)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a02082201a00820a768bed1e87b26b64f22z1a;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 62), (facetIndex 71)]))
 (.leaf ([(facetIndex 74), (facetIndex 83)])))
 (.branch 3
 (.leaf ([(facetIndex 64), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 76), (facetIndex 78), (facetIndex 79)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "40f31000a2z20;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
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
def grouped2_0008 : List Nat := [4, 5]
def grouped2_0009 : List Nat := [4, 5, 6, 7]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0016 : List Nat := [1]
def grouped3_0017 : List Nat := [2]
def grouped3_0018 : List Nat := [2, 3]
def grouped3_0019 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record007" 48

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record007" "{\"ridges\":[[54,265],[60,73],[61,265],[71,265],[72,74],[83,360]],\"owners\":[[60,73,[7,49,51,52,53,71],[22,36,62,64,70]],[72,74,[7,49,51,52,53,83],[31,36,74,76,82]],[83,360,[71],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-4,-3],[-5,-4],[-6,-3],[-6,-5],[-7,-3],[-7,-5],[-8,-4],[-8,-6],[-8,-7],[-9,-4],[-9,-6],[-9,-7],[-10,-3],[-10,-5],[-10,-8],[-10,-9],[-11,-3],[-11,-5],[-11,-8],[-11,-9],[-13,-2],[-13,-3],[-13,-6],[-13,-8],[-13,-10],[-17,-1],[-17,-3],[-17,-4],[-17,-10],[-17,-12],[-17,-14],[-17,-15],[-17,-16],[-19,-18],[-20,-18],[-21,-13],[-23,-17],[-23,-18],[-26,-20],[-26,-22],[-26,-24],[-26,-25],[-27,-2],[-27,-13],[-27,-21],[-28,-20],[-28,-22],[-28,-24],[-28,-25],[-29,-18],[-29,-26],[-29,-28],[-30,-20],[-30,-22],[-30,-24],[-30,-25],[-30,-29],[-18,1,12,14,15,16,27],[-28,1,12,14,15,16,31],[-17,-19,-27],[-31,27],[-32,2,19,21,23],[-33,3,5,8,9,18,26,28,30],[-34,4,6,7,10,11],[-35,13,17],[-36,32],[-37,33],[-38,36],[-38,37],[-39,34],[-39,35],[-40,39],[-41,38],[-41,40],[41],[-42,20,27],[-27,42],[-43,29,31],[-31,43],[-44,22,24,25],[-45,42,43],[-43,45],[-42,45],[-46,44],[-47,45,46],[-45,-46,48],[47],[-48]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":39,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":36},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":41,\"b\":36},{\"tag\":\"incompatible\",\"a\":41,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":40},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":37},{\"tag\":\"incompatible\",\"a\":44,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":45,\"b\":36},{\"tag\":\"incompatible\",\"a\":45,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":42},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":36},{\"tag\":\"incompatible\",\"a\":46,\"b\":39},{\"tag\":\"incompatible\",\"a\":46,\"b\":42},{\"tag\":\"incompatible\",\"a\":46,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":35},{\"tag\":\"incompatible\",\"a\":50,\"b\":36},{\"tag\":\"incompatible\",\"a\":50,\"b\":40},{\"tag\":\"incompatible\",\"a\":50,\"b\":42},{\"tag\":\"incompatible\",\"a\":50,\"b\":45},{\"tag\":\"incompatible\",\"a\":54,\"b\":7},{\"tag\":\"incompatible\",\"a\":54,\"b\":36},{\"tag\":\"incompatible\",\"a\":54,\"b\":37},{\"tag\":\"incompatible\",\"a\":54,\"b\":45},{\"tag\":\"incompatible\",\"a\":54,\"b\":49},{\"tag\":\"incompatible\",\"a\":54,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":63,\"b\":50},{\"tag\":\"incompatible\",\"a\":65,\"b\":54},{\"tag\":\"incompatible\",\"a\":65,\"b\":60},{\"tag\":\"incompatible\",\"a\":68,\"b\":62},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":71,\"b\":35},{\"tag\":\"incompatible\",\"a\":71,\"b\":50},{\"tag\":\"incompatible\",\"a\":71,\"b\":63},{\"tag\":\"incompatible\",\"a\":72,\"b\":62},{\"tag\":\"incompatible\",\"a\":72,\"b\":64},{\"tag\":\"incompatible\",\"a\":72,\"b\":66},{\"tag\":\"incompatible\",\"a\":72,\"b\":67},{\"tag\":\"incompatible\",\"a\":74,\"b\":60},{\"tag\":\"incompatible\",\"a\":74,\"b\":68},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"incompatible\",\"a\":80,\"b\":62},{\"tag\":\"incompatible\",\"a\":80,\"b\":64},{\"tag\":\"incompatible\",\"a\":80,\"b\":66},{\"tag\":\"incompatible\",\"a\":80,\"b\":67},{\"tag\":\"incompatible\",\"a\":80,\"b\":74},{\"tag\":\"mate\",\"ridge\":73,\"a\":60,\"owners\":[7,49,51,52,53,71]},{\"tag\":\"mate\",\"ridge\":74,\"a\":72,\"owners\":[7,49,51,52,53,83]},{\"tag\":\"three\",\"ridge\":265,\"vertices\":[54,61,71]},{\"tag\":\"mate\",\"ridge\":360,\"a\":83,\"owners\":[71]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[35,61,63,65],\"full_literals\":[-32,2,19,21,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[36,39,42,44,60,68,72,80],\"full_literals\":[-33,3,5,8,9,18,26,28,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[37,40,41,45,46],\"full_literals\":[-34,4,6,7,10,11]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[50,54],\"full_literals\":[-35,13,17]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-36,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-38,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-39,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-41,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-41,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[62,71],\"full_literals\":[-42,20,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":71,\"full_literals\":[-27,42]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[74,83],\"full_literals\":[-43,29,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-31,43]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[64,66,67],\"full_literals\":[-44,22,24,25]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,44,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-45,-46,48],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "89 38 0 75 73 0\n90 40 0 75 74 0\n91 36 0 89 68 0\n92 37 0 89 69 0\n93 39 0 90 72 0\n94 32 0 91 66 0\n95 33 0 92 67 0\n96 34 0 93 70 0\n97 35 0 93 71 0\n98 -26 -44 0 40 41 42 80 0\n99 -30 -44 0 54 55 56 80 0\n100 -5 6 -17 0 96 29 28 6 18 64 0\n101 -8 6 -17 0 96 29 28 9 19 64 0\n102 6 28 18 -17 -44 0 95 96 29 28 27 99 98 100 101 63 12 20 64 0\n103 -17 -46 0 88 95 84 99 98 86 83 77 82 79 26 27 30 31 32 33 58 59 102 4 8 11 63 0\n104 -18 -13 0 94 36 21 34 38 62 0\n105 -28 -44 0 47 48 49 80 0\n106 -5 -13 0 96 25 23 2 6 18 64 0\n107 -46 0 97 95 96 84 98 99 103 65 22 23 24 25 104 105 106 63 10 12 20 64 0\n108 45 0 107 87 85 0\n109 -9 0 96 10 11 12 16 20 64 0\n110 -27 0 97 94 43 44 45 65 37 60 62 0\n111 -31 0 110 61 0\n112 -26 0 110 111 108 39 51 76 78 81 0\n113 -30 0 110 111 108 53 57 76 78 81 0\n114 -18 0 110 111 108 35 50 76 78 81 0\n115 -28 0 110 111 108 46 52 76 78 81 0\n116 -5 0 96 2 4 6 14 18 64 0\n117 -8 0 96 7 8 9 15 19 64 0\n118 3 0 117 95 116 114 112 113 109 115 63 0\n119 -4 0 118 1 0\n120 -6 0 118 3 0\n121 -7 0 118 5 0\n122 -10 0 118 13 0\n123 -11 0 118 17 0\n124 0 121 123 96 119 120 122 64 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record010
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2749b19c9c99a568da9999695a361d98e4b8ae1b91e2785e9c6696655936665c5695656558d4756364d8b52d2b46d4749d1766364e5354cd38cc7362d4b32d2b2ad1b26c5b61e4789d2729c6785c570dc4f07c6a458964388e0ba619446989615454954348d0b46344c9314d0b22c4b0ad0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db69b69249349b6924934d249269249a4924924d2492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 70), (facetIndex 74), (facetIndex 75)]))
 (.leaf ([(facetIndex 33), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 79), (facetIndex 80), (facetIndex 81), (facetIndex 82)]))
 (.leaf ([(facetIndex 29), (facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 32), (facetIndex 48), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53)]))
 (.leaf ([(facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 63)])))
 (.branch 7
 (.leaf ([(facetIndex 39), (facetIndex 77), (facetIndex 78), (facetIndex 86)]))
 (.branch 8
 (.leaf ([(facetIndex 31), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37)]))
 (.leaf ([(facetIndex 56), (facetIndex 57)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "6000222266000000011111050555588004444043333333360777714723z1d;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 38), (facetIndex 49), (facetIndex 64)]))
 (.leaf ([(facetIndex 55), (facetIndex 71), (facetIndex 72), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 83), (facetIndex 84), (facetIndex 85)]))
 (.leaf ([(facetIndex 76), (facetIndex 88), (facetIndex 89), (facetIndex 90)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 87), (facetIndex 91), (facetIndex 94)]))
 (.leaf ([(facetIndex 92)])))
 (.branch 7
 (.leaf ([(facetIndex 62)]))
 (.leaf ([(facetIndex 93)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "13d8db8124000030092000001800002z29;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
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
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1]
def grouped3_0019 : List Nat := [0, 1, 2, 3]
def grouped3_0021 : List Nat := [1]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [2, 3]
def grouped3_0024 : List Nat := [3]
def grouped3_0025 : List Nat := [4]
def grouped3_0026 : List Nat := [4, 5]
def grouped3_0027 : List Nat := [4, 5, 6, 7]
def grouped3_0028 : List Nat := [5]
def grouped3_0029 : List Nat := [6]
def grouped3_0030 : List Nat := [6, 7]
def grouped3_0031 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record010" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record010" 115

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record010" "{\"ridges\":[[7,138],[8,266],[9,82],[14,140],[15,268],[16,145],[17,273],[18,532],[19,545],[19,548],[21,81],[21,577],[21,592],[22,608],[26,146],[27,274],[32,82],[33,532],[37,548],[40,82],[41,138],[42,266],[43,138],[44,266],[45,138],[46,266],[47,138],[47,266],[48,82],[50,82],[51,82],[52,82],[52,592],[54,608],[55,92],[56,140],[56,145],[57,268],[57,273],[58,44],[59,44],[59,140],[60,44],[60,268],[61,44],[61,545],[61,548],[63,140],[63,268],[64,116],[65,532],[65,548],[66,532],[66,592],[67,145],[67,273],[68,145],[68,532],[69,273],[69,532],[70,548],[70,608],[71,216],[72,344],[73,408],[74,608],[75,592],[75,608],[76,92],[77,146],[78,274],[83,116],[84,562],[85,582],[88,216],[89,344],[90,408],[91,562],[91,592],[94,116]],\"owners\":[[7,138,[24,77,80,82,88,90],[41,43,45,47]],[41,138,[24,80,82],[7,43,45,47,77,88,90]],[43,138,[24,77,82,88,90],[7,41,45,47,80]],[45,138,[24,77,80,82,90],[7,41,43,47,88]],[47,138,[24,77,80,88],[7,41,43,45,82,90]],[8,266,[25,78,81,82,89,90],[42,44,46,47]],[42,266,[25,81,82],[8,44,46,47,78,89,90]],[44,266,[25,78,82,89,90],[8,42,46,47,81]],[46,266,[25,78,81,82,90],[8,42,44,47,89]],[47,266,[25,78,81,89],[8,42,44,46,82,90]],[21,81,[9,32,40,48,50,51,55,64,71,72],[66,75]],[9,82,[76,83,85,88,89,91],[32,40,48,50,51,52]],[32,82,[88,89,91],[9,40,48,50,51,52,76,83,85]],[40,82,[83,85,91],[9,32,48,50,51,52,76,88,89]],[48,82,[76,85,88,89],[9,32,40,50,51,52,83,91]],[50,82,[76,83,85,89,91],[9,32,40,48,51,52,88]],[51,82,[76,83,85,88,91],[9,32,40,48,50,52,89]],[52,82,[76,83,88,89],[9,32,40,48,50,51,85,91]],[16,145,[10,41,50,53,71,73],[56,67,68]],[56,145,[10,50,53],[16,41,67,68,71,73]],[67,145,[10,41,50,71],[16,53,56,68,73]],[68,145,[10,41,50,53,71,73],[16,56,67]],[26,146,[10,41,50,53,88,90],[77,86]],[77,146,[10,50,53],[26,41,86,88,90]],[17,273,[11,42,51,53,72,73],[57,67,69]],[57,273,[11,51,53],[17,42,67,69,72,73]],[67,273,[11,42,51,72],[17,53,57,69,73]],[69,273,[11,42,51,53,72,73],[17,57,67]],[27,274,[11,42,51,53,89,90],[78,86]],[78,274,[11,51,53],[27,42,86,89,90]],[58,44,[23,80,81],[13,59,60,61,79,93]],[59,44,[23,79,81,93],[13,58,60,61,80]],[60,44,[23,79,80,93],[13,58,59,61,81]],[61,44,[23,79,80,81],[13,58,59,60,93]],[14,140,[24,77,80,82,92],[56,59,63]],[56,140,[24,80,82],[14,59,63,77,92]],[59,140,[24,77,82,92],[14,56,63,80]],[63,140,[24,77,80],[14,56,59,82,92]],[15,268,[25,78,81,82,92],[57,60,63]],[57,268,[25,81,82],[15,60,63,78,92]],[60,268,[25,78,82,92],[15,57,63,81]],[63,268,[25,78,81],[15,57,60,82,92]],[18,532,[84,85,94],[33,65,66,68,69]],[33,532,[94],[18,65,66,68,69,84,85]],[65,532,[85],[18,33,66,68,69,84,94]],[66,532,[84],[18,33,65,68,69,85,94]],[68,532,[84,85,94],[18,33,65,66,69]],[69,532,[84,85,94],[18,33,65,66,68]],[19,545,[22,49,54,74,75],[37,61,65]],[61,545,[22,49,54,75],[19,37,65,74]],[19,548,[84,87,93,94],[37,61,65,70]],[37,548,[93,94],[19,61,65,70,84,87]],[61,548,[84,87,94],[19,37,65,70,93]],[65,548,[87,93],[19,37,61,70,84,94]],[70,548,[84],[19,37,61,65,87,93,94]],[21,577,[22,38,54,62,70,74],[52,66]],[21,592,[85,91,94],[52,66,75]],[52,592,[94],[21,66,75,85,91]],[66,592,[91],[21,52,75,85,94]],[75,592,[85],[21,52,66,91,94]],[91,592,[21,66],[52,75,85,94]],[22,608,[87,91,93,94],[54,70,74,75]],[54,608,[93,94],[22,70,74,75,87,91]],[70,608,[91],[22,54,74,75,87,93,94]],[74,608,[87,91,94],[22,54,70,75,93]],[75,608,[87,93],[22,54,70,74,91,94]],[85,582,[38,87],[]],[84,562,[49,91],[]],[91,562,[49,84],[]],[55,92,[76],[]],[76,92,[55],[]],[64,116,[83,94],[]],[83,116,[64,94],[]],[94,116,[64,83],[]],[71,216,[88],[]],[88,216,[71],[]],[72,344,[89],[]],[89,344,[72],[]],[73,408,[90,92],[]],[90,408,[73,92],[]]],\"edges\":[[23,[18,19,33,37,38,61,62,65,66,68,69,70,84,85,87,93,94]],[27,[7,14,24,41,43,45,47,56,59,63,71,73,77,80,82,88,90,92]],[28,[8,15,25,42,44,46,47,57,60,63,72,73,78,81,82,89,90,92]],[31,[9,21,32,40,48,50,51,52,55,64,66,71,72,75,76,83,85,88,89,91,94]],[32,[10,16,26,41,50,53,56,67,68,71,73,77,86,88,90,92]],[33,[11,17,27,42,51,53,57,67,69,72,73,78,86,89,90,92]],[34,[18,21,33,49,52,65,66,68,69,75,84,85,91,94]],[38,[19,22,37,49,54,61,65,70,74,75,84,87,91,93,94]],[41,[21,22,38,52,54,62,66,70,74,75,85,87,91,93,94]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record010" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record010\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-20,-19],[-26,-20],[-27,-20],[-28,-20],[-29,-20],[-30,-20],[-31,-20],[-32,-20],[-33,-20],[-35,-24],[-36,-5],[-36,-28],[-37,-4],[-37,-27],[-37,-36],[-39,-3],[-39,-26],[-39,-36],[-39,-37],[-42,-25],[-43,-25],[-54,-50],[-55,-50],[-63,-42],[-63,-43],[-64,-42],[-64,-43],[-65,-21],[-65,-24],[-65,-52],[-66,-16],[-66,-63],[-66,-64],[-67,-15],[-67,-63],[-67,-66],[-68,-14],[-68,-49],[-68,-63],[-68,-66],[-68,-67],[-70,-24],[-72,-22],[-72,-53],[-72,-68],[-72,-69],[-72,-70],[-72,-71],[-73,-20],[-73,-44],[-73,-65],[-77,-34],[-80,-20],[-80,-65],[-1,15,63,66,68,74,76],[-27,15,66,68],[-29,15,63,68,74,76],[-31,15,63,66,68,76],[-33,15,63,66,74],[-2,16,64,67,68,75,76],[-28,16,67,68],[-30,16,64,68,75,76],[-32,16,64,67,68,76],[-33,16,64,67,75],[-12,3,21,26,34,36,37,41,50,57,58],[-3,62,69,71,74,75,77],[-21,74,75,77],[-26,69,71,77],[-34,62,71,74,75],[-36,62,69,71,75,77],[-37,62,69,71,74,77],[-38,62,69,74,75],[-8,4,27,36,39,57,59],[-42,4,36,39],[-53,4,27,36,57],[-54,4,27,36,39,57,59],[-17,4,27,36,39,74,76],[-63,4,36,39],[-9,5,28,37,39,58,59],[-43,5,37,39],[-53,5,28,37,58],[-55,5,28,37,39,58,59],[-18,5,28,37,39,75,76],[-64,5,37,39],[-44,14,66,67],[-45,14,65,67,79],[-46,14,65,66,79],[-47,14,65,66,67],[-6,15,63,66,68,78],[-42,15,66,68],[-45,15,63,68,78],[-49,15,63,66],[-7,16,64,67,68,78],[-43,16,67,68],[-46,16,64,68,78],[-49,16,64,67],[-10,70,71,80],[-22,80],[-51,71],[-52,70],[-54,70,71,80],[-55,70,71,80],[-11,13,35,40,60,61],[-47,13,35,40,61],[-11,70,73,79,80],[-23,79,80],[-47,70,73,80],[-51,73,79],[-56,70],[-12,13,24,40,48,56,60],[-12,71,77,80],[-38,80],[-52,77],[-61,71],[-77,12,52],[-13,73,77,79,80],[-40,79,80],[-56,77],[-60,73,77,80],[-61,73,79],[-71,24,73],[-70,35,77],[-77,35,70],[-41,62],[-62,41],[-50,69,80],[-69,50,80],[-80,50,69],[-57,74],[-74,57],[-58,75],[-75,58],[-59,76,78],[-76,59,78],[-81,22,51,52,53,54,55],[-82,20,65,66,67,68],[-83,19,26,27,28,29,30,31,32,33],[-84,21,34,36,37,38,39],[-85,44,45,46,47,49],[-86,25,63,64,72],[-87,42,43],[-88,81],[-89,82],[-89,83],[-90,88,89],[-91,89],[-92,84],[-92,85],[-93,87],[-94,86],[-94,93],[-95,92,94],[-96,94],[-97,90],[-97,91,96],[-97,95],[97],[-24,98],[-35,98],[-50,98],[-41,99],[-57,99],[-58,99],[-59,99],[-100,69,70,71],[-69,100],[-70,100],[-71,100],[-101,62,74,75,76],[-62,101],[-74,101],[-75,101],[-76,101],[-102,73,77,80],[-73,102],[-77,102],[-80,102],[-78,103],[-48,104],[-79,105],[-99,106],[-98,106],[-107,100,101],[-101,107],[-100,107],[-107,108],[-106,108],[-106,-107,109],[-103,110],[-102,110],[-102,-103,111],[-105,112],[-104,112],[-112,113],[-110,113],[-110,-112,114],[-111,114],[-108,-114,115],[-109,-113,115],[-115],[10,11,22,23,24,47,48,51,52,54,55,56,70,71,73,79,80],[1,6,15,27,29,31,33,42,45,49,57,59,63,66,68,74,76,78],[2,7,16,28,30,32,33,43,46,49,58,59,64,67,68,75,76,78],[3,12,21,26,34,36,37,38,41,50,52,57,58,61,62,69,71,74,75,77,80],[4,8,17,27,36,39,42,53,54,57,59,63,72,74,76,78],[5,9,18,28,37,39,43,53,55,58,59,64,72,75,76,78],[10,12,22,35,38,51,52,54,55,61,70,71,77,80],[11,13,23,35,40,47,51,56,60,61,70,73,77,79,80],[12,13,24,38,40,48,52,56,60,61,71,73,77,79,80]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":30,\"b\":29},{\"tag\":\"incompatible\",\"a\":40,\"b\":30},{\"tag\":\"incompatible\",\"a\":41,\"b\":30},{\"tag\":\"incompatible\",\"a\":42,\"b\":30},{\"tag\":\"incompatible\",\"a\":43,\"b\":30},{\"tag\":\"incompatible\",\"a\":44,\"b\":30},{\"tag\":\"incompatible\",\"a\":45,\"b\":30},{\"tag\":\"incompatible\",\"a\":46,\"b\":30},{\"tag\":\"incompatible\",\"a\":47,\"b\":30},{\"tag\":\"incompatible\",\"a\":49,\"b\":38},{\"tag\":\"incompatible\",\"a\":50,\"b\":11},{\"tag\":\"incompatible\",\"a\":50,\"b\":42},{\"tag\":\"incompatible\",\"a\":51,\"b\":10},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":53,\"b\":9},{\"tag\":\"incompatible\",\"a\":53,\"b\":40},{\"tag\":\"incompatible\",\"a\":53,\"b\":50},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":56,\"b\":39},{\"tag\":\"incompatible\",\"a\":57,\"b\":39},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":69,\"b\":64},{\"tag\":\"incompatible\",\"a\":77,\"b\":56},{\"tag\":\"incompatible\",\"a\":77,\"b\":57},{\"tag\":\"incompatible\",\"a\":78,\"b\":56},{\"tag\":\"incompatible\",\"a\":78,\"b\":57},{\"tag\":\"incompatible\",\"a\":79,\"b\":32},{\"tag\":\"incompatible\",\"a\":79,\"b\":38},{\"tag\":\"incompatible\",\"a\":79,\"b\":66},{\"tag\":\"incompatible\",\"a\":80,\"b\":25},{\"tag\":\"incompatible\",\"a\":80,\"b\":77},{\"tag\":\"incompatible\",\"a\":80,\"b\":78},{\"tag\":\"incompatible\",\"a\":81,\"b\":24},{\"tag\":\"incompatible\",\"a\":81,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":23},{\"tag\":\"incompatible\",\"a\":82,\"b\":63},{\"tag\":\"incompatible\",\"a\":82,\"b\":77},{\"tag\":\"incompatible\",\"a\":82,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":81},{\"tag\":\"incompatible\",\"a\":84,\"b\":38},{\"tag\":\"incompatible\",\"a\":86,\"b\":33},{\"tag\":\"incompatible\",\"a\":86,\"b\":67},{\"tag\":\"incompatible\",\"a\":86,\"b\":82},{\"tag\":\"incompatible\",\"a\":86,\"b\":83},{\"tag\":\"incompatible\",\"a\":86,\"b\":84},{\"tag\":\"incompatible\",\"a\":86,\"b\":85},{\"tag\":\"incompatible\",\"a\":87,\"b\":30},{\"tag\":\"incompatible\",\"a\":87,\"b\":58},{\"tag\":\"incompatible\",\"a\":87,\"b\":79},{\"tag\":\"incompatible\",\"a\":91,\"b\":48},{\"tag\":\"incompatible\",\"a\":94,\"b\":30},{\"tag\":\"incompatible\",\"a\":94,\"b\":79},{\"tag\":\"mate\",\"ridge\":138,\"a\":7,\"owners\":[24,77,80,82,88,90]},{\"tag\":\"mate\",\"ridge\":138,\"a\":41,\"owners\":[24,80,82]},{\"tag\":\"mate\",\"ridge\":138,\"a\":43,\"owners\":[24,77,82,88,90]},{\"tag\":\"mate\",\"ridge\":138,\"a\":45,\"owners\":[24,77,80,82,90]},{\"tag\":\"mate\",\"ridge\":138,\"a\":47,\"owners\":[24,77,80,88]},{\"tag\":\"mate\",\"ridge\":266,\"a\":8,\"owners\":[25,78,81,82,89,90]},{\"tag\":\"mate\",\"ridge\":266,\"a\":42,\"owners\":[25,81,82]},{\"tag\":\"mate\",\"ridge\":266,\"a\":44,\"owners\":[25,78,82,89,90]},{\"tag\":\"mate\",\"ridge\":266,\"a\":46,\"owners\":[25,78,81,82,90]},{\"tag\":\"mate\",\"ridge\":266,\"a\":47,\"owners\":[25,78,81,89]},{\"tag\":\"mate\",\"ridge\":81,\"a\":21,\"owners\":[9,32,40,48,50,51,55,64,71,72]},{\"tag\":\"mate\",\"ridge\":82,\"a\":9,\"owners\":[76,83,85,88,89,91]},{\"tag\":\"mate\",\"ridge\":82,\"a\":32,\"owners\":[88,89,91]},{\"tag\":\"mate\",\"ridge\":82,\"a\":40,\"owners\":[83,85,91]},{\"tag\":\"mate\",\"ridge\":82,\"a\":48,\"owners\":[76,85,88,89]},{\"tag\":\"mate\",\"ridge\":82,\"a\":50,\"owners\":[76,83,85,89,91]},{\"tag\":\"mate\",\"ridge\":82,\"a\":51,\"owners\":[76,83,85,88,91]},{\"tag\":\"mate\",\"ridge\":82,\"a\":52,\"owners\":[76,83,88,89]},{\"tag\":\"mate\",\"ridge\":145,\"a\":16,\"owners\":[10,41,50,53,71,73]},{\"tag\":\"mate\",\"ridge\":145,\"a\":56,\"owners\":[10,50,53]},{\"tag\":\"mate\",\"ridge\":145,\"a\":67,\"owners\":[10,41,50,71]},{\"tag\":\"mate\",\"ridge\":145,\"a\":68,\"owners\":[10,41,50,53,71,73]},{\"tag\":\"mate\",\"ridge\":146,\"a\":26,\"owners\":[10,41,50,53,88,90]},{\"tag\":\"mate\",\"ridge\":146,\"a\":77,\"owners\":[10,50,53]},{\"tag\":\"mate\",\"ridge\":273,\"a\":17,\"owners\":[11,42,51,53,72,73]},{\"tag\":\"mate\",\"ridge\":273,\"a\":57,\"owners\":[11,51,53]},{\"tag\":\"mate\",\"ridge\":273,\"a\":67,\"owners\":[11,42,51,72]},{\"tag\":\"mate\",\"ridge\":273,\"a\":69,\"owners\":[11,42,51,53,72,73]},{\"tag\":\"mate\",\"ridge\":274,\"a\":27,\"owners\":[11,42,51,53,89,90]},{\"tag\":\"mate\",\"ridge\":274,\"a\":78,\"owners\":[11,51,53]},{\"tag\":\"mate\",\"ridge\":44,\"a\":58,\"owners\":[23,80,81]},{\"tag\":\"mate\",\"ridge\":44,\"a\":59,\"owners\":[23,79,81,93]},{\"tag\":\"mate\",\"ridge\":44,\"a\":60,\"owners\":[23,79,80,93]},{\"tag\":\"mate\",\"ridge\":44,\"a\":61,\"owners\":[23,79,80,81]},{\"tag\":\"mate\",\"ridge\":140,\"a\":14,\"owners\":[24,77,80,82,92]},{\"tag\":\"mate\",\"ridge\":140,\"a\":56,\"owners\":[24,80,82]},{\"tag\":\"mate\",\"ridge\":140,\"a\":59,\"owners\":[24,77,82,92]},{\"tag\":\"mate\",\"ridge\":140,\"a\":63,\"owners\":[24,77,80]},{\"tag\":\"mate\",\"ridge\":268,\"a\":15,\"owners\":[25,78,81,82,92]},{\"tag\":\"mate\",\"ridge\":268,\"a\":57,\"owners\":[25,81,82]},{\"tag\":\"mate\",\"ridge\":268,\"a\":60,\"owners\":[25,78,82,92]},{\"tag\":\"mate\",\"ridge\":268,\"a\":63,\"owners\":[25,78,81]},{\"tag\":\"mate\",\"ridge\":532,\"a\":18,\"owners\":[84,85,94]},{\"tag\":\"mate\",\"ridge\":532,\"a\":33,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":532,\"a\":65,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":532,\"a\":66,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":532,\"a\":68,\"owners\":[84,85,94]},{\"tag\":\"mate\",\"ridge\":532,\"a\":69,\"owners\":[84,85,94]},{\"tag\":\"mate\",\"ridge\":545,\"a\":19,\"owners\":[22,49,54,74,75]},{\"tag\":\"mate\",\"ridge\":545,\"a\":61,\"owners\":[22,49,54,75]},{\"tag\":\"mate\",\"ridge\":548,\"a\":19,\"owners\":[84,87,93,94]},{\"tag\":\"mate\",\"ridge\":548,\"a\":37,\"owners\":[93,94]},{\"tag\":\"mate\",\"ridge\":548,\"a\":61,\"owners\":[84,87,94]},{\"tag\":\"mate\",\"ridge\":548,\"a\":65,\"owners\":[87,93]},{\"tag\":\"mate\",\"ridge\":548,\"a\":70,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":577,\"a\":21,\"owners\":[22,38,54,62,70,74]},{\"tag\":\"mate\",\"ridge\":592,\"a\":21,\"owners\":[85,91,94]},{\"tag\":\"mate\",\"ridge\":592,\"a\":52,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":592,\"a\":66,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":592,\"a\":75,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":592,\"a\":91,\"owners\":[21,66]},{\"tag\":\"mate\",\"ridge\":608,\"a\":22,\"owners\":[87,91,93,94]},{\"tag\":\"mate\",\"ridge\":608,\"a\":54,\"owners\":[93,94]},{\"tag\":\"mate\",\"ridge\":608,\"a\":70,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":608,\"a\":74,\"owners\":[87,91,94]},{\"tag\":\"mate\",\"ridge\":608,\"a\":75,\"owners\":[87,93]},{\"tag\":\"mate\",\"ridge\":582,\"a\":85,\"owners\":[38,87]},{\"tag\":\"mate\",\"ridge\":562,\"a\":84,\"owners\":[49,91]},{\"tag\":\"mate\",\"ridge\":562,\"a\":91,\"owners\":[49,84]},{\"tag\":\"mate\",\"ridge\":92,\"a\":55,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":92,\"a\":76,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":116,\"a\":64,\"owners\":[83,94]},{\"tag\":\"mate\",\"ridge\":116,\"a\":83,\"owners\":[64,94]},{\"tag\":\"mate\",\"ridge\":116,\"a\":94,\"owners\":[64,83]},{\"tag\":\"mate\",\"ridge\":216,\"a\":71,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":216,\"a\":88,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":344,\"a\":72,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":344,\"a\":89,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":408,\"a\":73,\"owners\":[90,92]},{\"tag\":\"mate\",\"ridge\":408,\"a\":90,\"owners\":[73,92]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[33,65,66,67,68,69],\"full_literals\":[-81,22,51,52,53,54,55]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[30,79,80,81,82],\"full_literals\":[-82,20,65,66,67,68]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[29,40,41,42,43,44,45,46,47],\"full_literals\":[-83,19,26,27,28,29,30,31,32,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[32,48,50,51,52,53],\"full_literals\":[-84,21,34,36,37,38,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[58,59,60,61,63],\"full_literals\":[-85,44,45,46,47,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[39,77,78,86],\"full_literals\":[-86,25,63,64,72]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[56,57],\"full_literals\":[-87,42,43]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-88,false,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-89,82,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-89,false,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-90,88,89],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-91,false,89],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-92,84,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-92,false,85],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-93,false,87],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-94,86,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-94,false,93],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-95,92,94],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-96,false,94],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-97,90,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-97,91,96],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-97,false,95],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":38,\"full_literals\":[-24,98]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-35,98]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":64,\"full_literals\":[-50,98]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":55,\"full_literals\":[-41,99]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":71,\"full_literals\":[-57,99]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":72,\"full_literals\":[-58,99]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-59,99]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[83,84,85],\"full_literals\":[-100,69,70,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":83,\"full_literals\":[-69,100]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":84,\"full_literals\":[-70,100]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":85,\"full_literals\":[-71,100]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[76,88,89,90],\"full_literals\":[-101,62,74,75,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-62,101]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":88,\"full_literals\":[-74,101]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-75,101]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":90,\"full_literals\":[-76,101]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[87,91,94],\"full_literals\":[-102,73,77,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":87,\"full_literals\":[-73,102]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":91,\"full_literals\":[-77,102]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":94,\"full_literals\":[-80,102]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":92,\"full_literals\":[-78,103]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":62,\"full_literals\":[-48,104]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":93,\"full_literals\":[-79,105]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-99,106],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-98,false,106],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-107,100,101],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-101,107],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-100,false,107],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-107,108],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-106,false,108],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-106,-107,109],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-103,110],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-102,false,110],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-102,-103,111],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-105,112],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-104,false,112],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-112,113],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-110,false,113],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-110,-112,114],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-111,false,114],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-108,-114,115],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-109,-113,115],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[18,19,33,37,38,61,62,65,66,68,69,70,84,85,87,93,94]},{\"tag\":\"edge\",\"edge\":27,\"owners\":[7,14,24,41,43,45,47,56,59,63,71,73,77,80,82,88,90,92]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[8,15,25,42,44,46,47,57,60,63,72,73,78,81,82,89,90,92]},{\"tag\":\"edge\",\"edge\":31,\"owners\":[9,21,32,40,48,50,51,52,55,64,66,71,72,75,76,83,85,88,89,91,94]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[10,16,26,41,50,53,56,67,68,71,73,77,86,88,90,92]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[11,17,27,42,51,53,57,67,69,72,73,78,86,89,90,92]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[18,21,33,49,52,65,66,68,69,75,84,85,91,94]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[19,22,37,49,54,61,65,70,74,75,84,87,91,93,94]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[21,22,38,52,54,62,66,70,74,75,85,87,91,93,94]}]}"
  "210 90 0 157 154 0\n211 95 0 157 156 0\n212 108 0 186 187 184 185 182 170 171 172 166 167 168 159 160 72 128 97 100 101 102 123 99 111 114 98 207 0\n213 -114 0 212 200 198 0\n214 -111 0 213 197 0\n215 107 102 0 177 112 176 113 184 185 170 171 172 166 168 69 124 129 67 66 71 131 70 126 68 111 114 204 0\n216 110 109 0 189 190 178 175 176 177 215 188 181 182 161 162 163 164 158 159 160 125 130 132 134 121 122 127 169 165 183 0\n217 102 24 112 0 193 179 192 180 175 176 177 119 116 120 121 113 118 112 117 110 209 0\n218 34 36 37 -84 -12 21 38 106 0 182 160 181 163 162 161 138 16 17 65 0\n219 37 34 -84 -12 72 21 38 78 106 0 181 164 134 163 132 218 11 12 18 79 80 82 84 81 83 206 0\n220 -37 72 78 59 57 0 134 130 13 14 15 19 73 74 76 78 75 77 205 0\n221 -43 63 -86 72 0 21 27 140 0\n222 63 -94 72 0 151 149 150 221 141 20 26 140 0\n223 -94 72 0 151 149 222 24 25 141 0\n224 -63 -82 65 20 0 32 35 39 136 0\n225 67 68 -82 65 20 78 59 58 0 134 132 136 31 33 60 61 62 63 64 93 94 95 96 203 0\n226 68 -82 65 20 78 59 58 57 0 224 134 130 225 34 36 55 56 89 92 57 59 58 91 90 202 0\n227 77 69 80 -100 -102 35 59 58 57 79 0 214 211 157 191 178 122 174 165 49 50 51 48 223 153 152 155 148 146 143 226 37 38 40 41 86 87 88 139 0\n228 -68 65 -85 79 0 37 38 40 41 86 87 88 85 139 0\n229 -20 -83 0 1 2 3 4 5 6 7 8 9 137 0\n230 65 94 78 59 58 57 79 0 211 157 153 155 146 144 229 143 152 148 228 226 0\n231 80 -100 -102 106 79 0 214 211 191 178 182 160 159 181 164 163 162 112 127 227 52 123 47 220 223 152 147 230 28 30 219 115 0\n232 -107 109 0 213 214 216 196 192 180 188 181 182 161 162 163 164 158 160 125 130 132 217 191 178 134 169 183 231 54 128 230 46 223 0\n233 -80 68 53 22 65 107 0 214 210 184 173 215 191 178 133 185 168 99 167 100 172 131 171 129 166 53 128 226 22 23 143 135 145 142 0\n234 65 109 0 213 214 210 232 184 173 215 191 178 133 185 168 99 167 100 172 131 171 129 216 196 192 180 230 223 43 44 45 233 101 102 135 142 145 143 144 226 229 0\n235 109 0 213 216 196 192 193 180 179 232 185 167 168 100 109 99 234 29 51 54 107 105 98 106 97 101 102 201 0\n236 -113 0 235 200 199 0\n237 -112 0 236 194 0\n238 -110 0 236 195 0\n239 -105 0 237 192 0\n240 -102 0 238 190 0\n241 -79 0 239 180 0\n242 -73 0 240 175 0\n243 -77 0 240 176 0\n244 -80 0 240 177 0\n245 24 0 240 237 217 0\n246 -13 0 242 243 241 244 116 0\n247 -51 0 242 241 108 0\n248 -61 0 242 241 120 0\n249 -56 0 243 118 0\n250 -60 0 243 242 244 119 0\n251 -23 0 244 241 106 0\n252 -40 0 244 241 117 0\n253 -35 0 245 10 0\n254 -70 0 245 42 0\n255 -11 0 246 253 252 250 248 103 0\n256 -47 0 246 253 252 248 104 0\n257 0 256 255 244 253 251 252 246 249 250 248 254 242 243 241 247 208 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record010
