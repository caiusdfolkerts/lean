module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow25Part00019Data
public import GraphInputsRow25Part00019Frames
public import GraphInputsRow25Part00019Leaves
public import GraphInputsRow25Part00019Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00019.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨90, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨106, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 5), (certNat% 8), 378302437418598400, (certNat% 6)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 4), (certNat% 10), (certNat% 11), (certNat% 12), 382805968326492160]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 15), (certNat% 16), (certNat% 12), 581395360488882176, 378355153847189504]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 590402559743623168, (certNat% 18), 180144539145601024, (certNat% 19), (certNat% 20), (certNat% 21)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), (certNat% 24), (certNat% 25), (certNat% 26), (certNat% 27)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 23), (certNat% 29), (certNat% 25), (certNat% 26), (certNat% 27)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), (certNat% 15), 633322992566272, (certNat% 32), (certNat% 33), (certNat% 34)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 36), (certNat% 18), (certNat% 37), 36029346774777856, (certNat% 38), (certNat% 39)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), 6322191859712, (certNat% 42), (certNat% 43)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 5497558138880, (certNat% 45), (certNat% 46), 13941807440199680, 540449547470503936]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 48), (certNat% 37), 6047313952768, (certNat% 18), 590402559743623168, 558463945979985920]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), 5913096224768, 590393763650600960, (certNat% 15), (certNat% 50), (certNat% 51), (certNat% 52)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), 5638218317824, (certNat% 54), (certNat% 55), 540484731842592768, (certNat% 3), 13941807440199680]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), 5910948741120, (certNat% 24), (certNat% 11), 558463945979985920, 590121084766912512]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), (certNat% 59), (certNat% 60), (certNat% 61), 585749426534875136, 558446353793941504, (certNat% 62)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 64), 5912022482944, (certNat% 65), (certNat% 8), 558481538166030336, 590261822255267840]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), (certNat% 67), (certNat% 68), (certNat% 19), 6328634310656, (certNat% 69), 558499130352074752, 590402559743623168]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c26 c21
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c27 c20
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c28 c19
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c29 c18
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c30 c13
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c31 c12
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c32 c7
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c33 c6
  c34
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00019.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00019.record031
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031
def vertexColumn : Fields := ⟨10, (certNat% 70)⟩
def kindColumn : Fields := ⟨3, (certNat% 71)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨96, by decide⟩, ⟨107, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), (certNat% 73), 571957152676052992, (certNat% 74), (certNat% 75), (certNat% 76)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 78), (certNat% 79), 553942754166571008, (certNat% 80), (certNat% 81)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 82), (certNat% 83), (certNat% 84), (certNat% 85), (certNat% 86), (certNat% 87)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 88), (certNat% 89), 85568402583715840, (certNat% 84), (certNat% 90), (certNat% 91)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 92), (certNat% 93), (certNat% 94), 400820366835974144, (certNat% 95), (certNat% 96)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), (certNat% 98), (certNat% 99), (certNat% 100), (certNat% 26)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 101), (certNat% 102), (certNat% 103), (certNat% 104), (certNat% 105), (certNat% 106), (certNat% 107)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 108), (certNat% 90), (certNat% 109), (certNat% 110), (certNat% 111), (certNat% 112), (certNat% 113)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 114), (certNat% 115), (certNat% 95), (certNat% 116), 337769972052787200, (certNat% 117), (certNat% 118)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00019.record031
