module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00086Data
public import GraphInputsRow24Part00086Frames
public import GraphInputsRow24Part00086Leaves
public import GraphInputsRow24Part00086Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00086.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 64871186038784, 17005592192950992896, (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), 136064563937280, 10273871076786176]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 10), (certNat% 8), 139912854634496, 10273872083419136]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 109401406963712, (certNat% 8), (certNat% 12), (certNat% 13)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 1657324662872342528, 91534343012352, (certNat% 15)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 1585267068834414592, (certNat% 17)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 1266637395197952, 1657324662872342528, (certNat% 15)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 8), 106686987632640, 25013889531904, 1266637462306816]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 146834194432, 91534343012352, (certNat% 15), (certNat% 22), (certNat% 23)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 136339441844224, (certNat% 25), (certNat% 8), (certNat% 26)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), (certNat% 8), 185488900096, 289357375570182144, (certNat% 29), 139363098820608]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c16 c3
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c17 c2
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00086.record004
