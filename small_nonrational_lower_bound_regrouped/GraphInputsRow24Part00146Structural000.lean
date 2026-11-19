module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00146Data
public import GraphInputsRow24Part00146Frames
public import GraphInputsRow24Part00146Leaves
public import GraphInputsRow24Part00146Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00146.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 8640266240, (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), 40567617525645312, 84662462447616]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), (certNat% 13), (certNat% 5), (certNat% 14)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 10977524225933312, 54043206265864192, (certNat% 16), (certNat% 17)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 8), (certNat% 9), 40567617525645312, 10696050188746752]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 21), 18298081099382784, (certNat% 22), (certNat% 23)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), 85830634831872, (certNat% 26), 36028842401333248, 15200199706148864, (certNat% 27)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00146.record008
