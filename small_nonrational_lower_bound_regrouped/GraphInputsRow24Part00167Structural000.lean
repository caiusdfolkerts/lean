module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00167Data
public import GraphInputsRow24Part00167Frames
public import GraphInputsRow24Part00167Leaves
public import GraphInputsRow24Part00167Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00167.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨86, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 18014398534647808, (certNat% 5), 5368709120]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), 4398063288320, (certNat% 10)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), (certNat% 13), (certNat% 14), (certNat% 15)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), (certNat% 18), 4402358255616]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 21), 6601373122560, (certNat% 22), 8796093022208]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), (certNat% 3), 13975420928, (certNat% 25), 31885837205504]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), (certNat% 3), (certNat% 28), (certNat% 29), 6601373122560, 26388295843840]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00167.record000
