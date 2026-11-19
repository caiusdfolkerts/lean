module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00157Data
public import GraphInputsRow24Part00157Frames
public import GraphInputsRow24Part00157Leaves
public import GraphInputsRow24Part00157Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00157.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 28147497671065600, 9223372036854775808]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), (certNat% 5), 1683627180032]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 6)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 11529215046068469760, (certNat% 8), 721554505728, 25895697857380352]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 10), (certNat% 11), 2333163674140672, 32673087530991616, 1890322481152]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), 9007336693694464, (certNat% 14), (certNat% 15), (certNat% 16)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 2260595906707456, (certNat% 16), (certNat% 18), (certNat% 5)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 13), 360639813910528, 2814749767106560, (certNat% 20)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 13), (certNat% 22), (certNat% 23), (certNat% 24), 562967133290496]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), (certNat% 27), (certNat% 28), (certNat% 3)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 30), (certNat% 31), 26458647810801664, (certNat% 32), (certNat% 33)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), (certNat% 36), (certNat% 37), (certNat% 38)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), 19171084741902336, (certNat% 41), (certNat% 42), (certNat% 43)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c22 c23
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c24 c24
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 45), (certNat% 46), (certNat% 8)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 48), (certNat% 46), (certNat% 49), 584115552256]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 51), 1962800054272, (certNat% 22), (certNat% 35), (certNat% 3)]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 45), (certNat% 53), (certNat% 49), 584115552256]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 360639813910528, (certNat% 53), 1924145348608, (certNat% 13)]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), 1962934272000, (certNat% 22), (certNat% 35), (certNat% 56), (certNat% 57)]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c35 c32
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), (certNat% 53), (certNat% 31), (certNat% 59), 25913290043424768]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), (certNat% 61), (certNat% 49), 721554505728, (certNat% 23), 25924285159702528]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), (certNat% 63), (certNat% 53), 23643898043695104, (certNat% 64)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 13), (certNat% 66), 362838837166080, 23661494524706816, (certNat% 27)]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), 2330964650885120, 4535485464576, (certNat% 68), (certNat% 14), (certNat% 69)]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), 2322168557862912, (certNat% 71), 1924145348608, (certNat% 13)]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), 2251834307641344, 1924145348608, (certNat% 13), (certNat% 73), 2305913377957871616]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 75), (certNat% 76), 9223372036854775808]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), 584115552256, 5629499534213120, (certNat% 78)]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), 584115552256, 13835058055282163712, 5647091720257536, (certNat% 80)]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c48 c47
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c49 c46
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 81), 281474976710656, (certNat% 78), (certNat% 76)]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 82), 584115552256, 1125899906842624, (certNat% 78)]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), 13835058055282163712, 307863255777280, (certNat% 80), 1125899906842624]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c53 c52
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c54 c51
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c55 c46
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c21 c56
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 84), 290271069732864, 13835058055282163712, 5629499534213120, (certNat% 80)]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c58 c47
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c59 c51
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c60 c46
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c21 c61
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c2 c62
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c63 c57
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), 16140901064495857664, (certNat% 75), (certNat% 86), 1649267441664, 25895697857380352]
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c65 c64
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c66 c50
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), (certNat% 88), 2096078258176, 14123288431433875456, (certNat% 89), 25924285159702528, (certNat% 56)]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c68 c67
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c69 c45
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c70 c42
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c71 c41
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c72 c38
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c73 c37
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c74 c36
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c75 c31
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c76 c20
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c77 c17
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c78 c14
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c79 c9
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c80 c8
  c81
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00157.record002
