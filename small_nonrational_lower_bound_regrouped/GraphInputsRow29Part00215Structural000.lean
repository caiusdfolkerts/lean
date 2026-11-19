module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00215Data
public import GraphInputsRow29Part00215Frames
public import GraphInputsRow29Part00215Leaves
public import GraphInputsRow29Part00215Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00215.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 13835060804061233152, (certNat% 3), (certNat% 4), (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), 13835060804061233152, (certNat% 12), (certNat% 5)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 12), 15046526355044827136, (certNat% 15), (certNat% 16)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 19), (certNat% 20)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), 720576017688690688, (certNat% 23), (certNat% 24)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), 720576017688690688, (certNat% 26), (certNat% 27), (certNat% 24)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), (certNat% 3), 1058345912432066560, (certNat% 30), (certNat% 31)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 33), 720576024131141632, (certNat% 34), (certNat% 35), (certNat% 36)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), (certNat% 40)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), (certNat% 43), (certNat% 44)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), 13835061903572860928, (certNat% 46), (certNat% 33), (certNat% 47), (certNat% 48)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), 16176930961026449408, (certNat% 50), (certNat% 51), (certNat% 52), (certNat% 33), (certNat% 53)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c23 c6
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00215.record000
