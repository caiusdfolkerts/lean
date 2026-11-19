module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00209Data
public import GraphInputsRow29Part00209Frames
public import GraphInputsRow29Part00209Leaves
public import GraphInputsRow29Part00209Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00209.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩, ⟨82, by decide⟩, ⟨90, by decide⟩, ⟨95, by decide⟩, ⟨101, by decide⟩, ⟨104, by decide⟩, ⟨109, by decide⟩, ⟨112, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 5242471441235968, 1477743627730944]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), 2075877953241088, (certNat% 4), (certNat% 12), (certNat% 13)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), 5242471441235968, 1477743627730944]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 19), (certNat% 8), (certNat% 9)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), 1653665488175104, (certNat% 16), (certNat% 12), (certNat% 13)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 725849473024, (certNat% 23), (certNat% 24), 18014398509481984, 288230376151711744]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 24), (certNat% 26), (certNat% 27), (certNat% 28)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 22553182508941312, (certNat% 30), 1477744567255040, (certNat% 31)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 21), (certNat% 33), 1477743627730944, (certNat% 34)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 34), (certNat% 36), (certNat% 37), (certNat% 38), (certNat% 33)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 24), (certNat% 40), 1477744500146176, (certNat% 41)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), (certNat% 44), (certNat% 37), (certNat% 18), (certNat% 11)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 43), (certNat% 36), (certNat% 37), (certNat% 44), (certNat% 33)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 18), (certNat% 6), (certNat% 11), 1266637462306816, (certNat% 47)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 23), (certNat% 24), 1548112439017472, (certNat% 49), (certNat% 50), (certNat% 16)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c21 c16
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c22 c15
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c23 c14
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c24 c13
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c25 c12
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c26 c11
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c27 c10
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c28 c9
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c29 c4
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c30 c9
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c31 c4
  c32
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00209.record003
