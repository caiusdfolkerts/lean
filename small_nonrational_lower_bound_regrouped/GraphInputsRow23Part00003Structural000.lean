module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00003Data
public import GraphInputsRow23Part00003Frames
public import GraphInputsRow23Part00003Leaves
public import GraphInputsRow23Part00003Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record027
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6), 18014535948435456, 601295421440]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10), (certNat% 11), 2305847407260205056, 90159953477632]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 14), 11817445422220181504, 598074195968, (certNat% 15), 244091581366272, 1729382256910270464]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), (certNat% 18), (certNat% 19), 22519372526387200, (certNat% 20), 721554505728]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 2078764171264, (certNat% 22), 175640385467449344, (certNat% 23), (certNat% 24), (certNat% 25)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), 72620543991349248, (certNat% 27), 87960930222080, 2305843043573432320, 18015910337970176, 549755813888]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), 1730789631793823744, 2305983746702049280, 18032128134479872, (certNat% 29), (certNat% 30), 70934606118912, 34359738368]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 22), 16429131440647569408, (certNat% 32), 31525197391593472, (certNat% 33), 90176059604992, (certNat% 34), 2113123909632]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record027
