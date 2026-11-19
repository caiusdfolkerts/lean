module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00034Data
public import GraphInputsRow24Part00034Frames
public import GraphInputsRow24Part00034Leaves
public import GraphInputsRow24Part00034Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 1729558178770714624, (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 4035225283303833600, (certNat% 8), (certNat% 4), (certNat% 9), (certNat% 3)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), 914840918949888, (certNat% 12), 4035225266123964416, (certNat% 13)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 11), (certNat% 15), 29273603736338432, (certNat% 16), (certNat% 17)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 20), 4035225266123964416, (certNat% 21), 351856605790208]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 19), (certNat% 15), (certNat% 16), (certNat% 23), 11259205226856448]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 4035225266123964416, (certNat% 16), 18577932578455552, (certNat% 4), (certNat% 3)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), 6917529062000820224, (certNat% 26), (certNat% 4), 914806559211520, 29273603736338432]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), 914806559211520, 29273603736338432, (certNat% 28), 4323455659455545344, (certNat% 3), (certNat% 8)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c9 c7
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c10 c6
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c11 c5
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c12 c4
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c13 c3
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c14 c2
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c15 c1
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c16 c0
  c17
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record016
