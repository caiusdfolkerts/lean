module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00019Data
public import GraphInputsRow23Part00019Frames
public import GraphInputsRow23Part00019Leaves
public import GraphInputsRow23Part00019Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00019.record060
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record060
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 110338190870577152, 4503599627370496, (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6), (certNat% 7)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), 1157425104234217472, (certNat% 9), (certNat% 10), (certNat% 11), (certNat% 12), (certNat% 7)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 11), (certNat% 12), (certNat% 14), (certNat% 15)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 1157425104234217472, (certNat% 12), 144255925564211200, (certNat% 17), (certNat% 7), (certNat% 5)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 17), (certNat% 19), (certNat% 20), 110619665847287808, 4644337115725824, (certNat% 14), (certNat% 21)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 19), 6485273760805945344, (certNat% 23), (certNat% 24), (certNat% 25), (certNat% 7), 2287070085120000, 4513220354113536]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record060_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record060_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record060_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record060_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record060_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record060_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record060_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record060_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00019.record060_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00019.record060
