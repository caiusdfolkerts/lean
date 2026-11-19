module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00149Data
public import GraphInputsRow24Part00149Frames
public import GraphInputsRow24Part00149Leaves
public import GraphInputsRow24Part00149Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00149.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 422212465065984, (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), 4629700416936869888, (certNat% 8), 171798691840]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 10), (certNat% 7), (certNat% 11), (certNat% 12)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 15), (certNat% 8)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 14), (certNat% 10), (certNat% 15), 4611686162308792320, (certNat% 17)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), 4755801210798211072, (certNat% 20), 257698037760, (certNat% 21)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), (certNat% 24), (certNat% 25), (certNat% 26), (certNat% 27)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), 4638707616225165312, (certNat% 30), 11544872091648, (certNat% 31)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 15), 4639833516098453504, (certNat% 33), (certNat% 34), (certNat% 35)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), 206158430208, (certNat% 37), (certNat% 38), (certNat% 39)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 9223372586627366912, 240786604032, (certNat% 41), (certNat% 42), (certNat% 43)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 45), (certNat% 29), 174046838784, (certNat% 46), 9345848836096]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 48), 4621819117588971520, (certNat% 49)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 51), (certNat% 52), 4611686155866341376, (certNat% 53), (certNat% 35)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), (certNat% 55), (certNat% 56), (certNat% 57), 422212465065984]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), 4611686155866341376, (certNat% 59), 34644951040, (certNat% 48), 10133099161583616]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), (certNat% 25), 4620693217715683328, (certNat% 10), 2748795846656, (certNat% 61), 178241142784]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c23 c20
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c24 c19
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c25 c16
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c26 c15
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c27 c12
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c28 c11
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c29 c10
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c30 c9
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c31 c8
  c32
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00149.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00149.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004
def vertexColumn : Fields := ⟨10, (certNat% 62)⟩
def kindColumn : Fields := ⟨3, (certNat% 63)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨73, by decide⟩, ⟨81, by decide⟩, ⟨89, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), 1411772930064384, 2251799813685248, (certNat% 65), 184718154792960, (certNat% 66)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 65), 5782621921543716864, 9223372036854775808, 756604737599569920, (certNat% 66)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 69), 189115999977472, 774619135907725312, 4612811918334230528]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), 211106232532992, 9007233614479360, (certNat% 71), (certNat% 66)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), 9288674231451648, 5764607527329202176, (certNat% 73), (certNat% 74), (certNat% 75)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), 9225623836668461056, (certNat% 77), (certNat% 69), 4612811918334230528]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), (certNat% 79), 864691128488689664, (certNat% 80), (certNat% 81), 184717953466368]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 82), (certNat% 83), (certNat% 84), 9363441022140416, 612489549439827968, 184717953466368, (certNat% 85)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00149.record004
