module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00093Data
public import GraphInputsRow29Part00093Frames
public import GraphInputsRow29Part00093Leaves
public import GraphInputsRow29Part00093Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00093.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨98, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10), (certNat% 11), (certNat% 12)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 10), (certNat% 20), (certNat% 8), (certNat% 21)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), (certNat% 24), (certNat% 25), (certNat% 26)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), (certNat% 14), (certNat% 16)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 28), (certNat% 30), (certNat% 19), (certNat% 20)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), (certNat% 33), (certNat% 34), (certNat% 35), 268435456]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), (certNat% 26), (certNat% 37), (certNat% 38), (certNat% 39), (certNat% 40)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 5), (certNat% 42), (certNat% 43), (certNat% 3), (certNat% 35)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 4), (certNat% 37), (certNat% 39)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 46), (certNat% 47), (certNat% 5), (certNat% 9), (certNat% 25)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 49), (certNat% 10), (certNat% 50), (certNat% 51), (certNat% 52)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 54), (certNat% 55), (certNat% 43), (certNat% 34), (certNat% 35), (certNat% 11)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c23 c12
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c24 c5
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c25 c2
  c26
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00093.record000
