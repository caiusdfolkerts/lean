module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow25Part00004Data
public import GraphInputsRow25Part00004Frames
public import GraphInputsRow25Part00004Leaves
public import GraphInputsRow25Part00004Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record031
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨93, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6), 562949953421312]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10), (certNat% 11), (certNat% 12)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 4), (certNat% 14), 7494552729897926656, (certNat% 15), (certNat% 16), (certNat% 17)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 11544872091648, 1154047404513689600, (certNat% 19), (certNat% 20), (certNat% 4)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), (certNat% 23), (certNat% 24), 1297036692682702848]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 12644383719424, (certNat% 27), (certNat% 28), 1297036692682702848]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 30), 1297046588287352832, (certNat% 31), (certNat% 32), (certNat% 33), 549755813888]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), 2594354860342116352, (certNat% 4), (certNat% 36), (certNat% 3)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), (certNat% 40), (certNat% 41), (certNat% 42), (certNat% 17)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), (certNat% 4), 5044042577771233280, (certNat% 45), 1729382256910270464, (certNat% 46)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 48), 8503921996382339072, (certNat% 49), (certNat% 50), 576465702253232128, (certNat% 51), (certNat% 52)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c19 c4
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record031
