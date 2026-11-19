module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00101Data
public import GraphInputsRow24Part00101Frames
public import GraphInputsRow24Part00101Leaves
public import GraphInputsRow24Part00101Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00101.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨83, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 1513211673819742208, 164944336352444416, (certNat% 4), 46302633668902912]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), 1513211673819742208, (certNat% 7), (certNat% 8), (certNat% 9)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), 44332308831928320, 648518346341351424, (certNat% 12)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 11), 1585269267857670144, (certNat% 14), (certNat% 15)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 941252322120433664, (certNat% 17), (certNat% 18), (certNat% 19)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), (certNat% 23), (certNat% 24), 1585267068834414592]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 14), 57420897396457472, (certNat% 26), (certNat% 27), (certNat% 28)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 30), (certNat% 31), (certNat% 32), (certNat% 33), (certNat% 34)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [14785739927702208512, 57983845202395136, (certNat% 35), (certNat% 18), (certNat% 36), (certNat% 17), (certNat% 37)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00101.record005
