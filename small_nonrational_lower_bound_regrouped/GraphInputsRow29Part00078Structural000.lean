module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00078Data
public import GraphInputsRow29Part00078Frames
public import GraphInputsRow29Part00078Leaves
public import GraphInputsRow29Part00078Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨95, by decide⟩, ⟨98, by decide⟩, ⟨103, by decide⟩, ⟨121, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 4467570873301204992]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), 578712552117108736]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 4), (certNat% 12), 17451451240415232]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17), (certNat% 18)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 15), (certNat% 21), (certNat% 17), (certNat% 18)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 7), (certNat% 9), (certNat% 23), 18253611008]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), (certNat% 26), (certNat% 27)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), (certNat% 9)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), (certNat% 32), (certNat% 33), 6192451635118080]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 6403557867651072, (certNat% 35), (certNat% 36), (certNat% 37)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), 568009424896, (certNat% 9), (certNat% 7)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), (certNat% 42), 2320479710150131712, (certNat% 43), 536870912]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 703687441776640, (certNat% 45), (certNat% 46)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 48), (certNat% 14), (certNat% 49), (certNat% 50), (certNat% 51)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 9), (certNat% 53), (certNat% 7)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 1585267120374022144, 15199652500471808, (certNat% 55), (certNat% 56), (certNat% 57)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), 1585267120374022144, (certNat% 59), (certNat% 60), (certNat% 61), 9007199254740992]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 6192450024505344, (certNat% 63), (certNat% 64)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), 1585267086014283776, (certNat% 64), 15199652500471808, (certNat% 66)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), 1585267120374022144, (certNat% 68), (certNat% 69), 6192452171988992, (certNat% 66)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), 1315051125551923200, (certNat% 72), 5207289753501696, (certNat% 9), (certNat% 73)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c27 c20
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c28 c19
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c29 c18
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c30 c17
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c31 c14
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c32 c13
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c33 c12
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c34 c5
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c35 c4
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c36 c3
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c37 c2
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c38 c1
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c39 c0
  c40
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record018
