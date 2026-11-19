module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00094Data
public import GraphInputsRow24Part00094Frames
public import GraphInputsRow24Part00094Leaves
public import GraphInputsRow24Part00094Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00094.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 237494729703424, 1152921504606846976]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), 90072069856821248, 167125767421952]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 10), 90076467903332352, 237494662594560, (certNat% 11)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), 54047593574957056, 72128040091516928, (certNat% 14), (certNat% 15)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), 1152921504606846976, (certNat% 18), (certNat% 19)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), 72128040158625792, (certNat% 22), (certNat% 23), (certNat% 24)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 54326869528412160, (certNat% 27)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), 9008298766368768, (certNat% 29), (certNat% 30), (certNat% 31)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), 9289773743079424, 54045394551701504, (certNat% 33), (certNat% 34), (certNat% 35)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), 238594157445120, (certNat% 34), 81064863085887488, (certNat% 37), (certNat% 38)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), (certNat% 41), (certNat% 30), 149533581377536]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), (certNat% 44), 224300523061248, 54326869528412160, 85899345920]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 46), (certNat% 47), (certNat% 48)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 46), (certNat% 50), (certNat% 27), 149533581377536]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), 52613349376, (certNat% 52), (certNat% 53)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), (certNat% 55), (certNat% 56), 241892558110720]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), (certNat% 59), (certNat% 60), 54329068551667712, 237494528376832]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c23 c20
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c24 c19
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), 54331267574923264, (certNat% 62), 238594174222336, (certNat% 63), (certNat% 64), 72057689600950272]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c27 c16
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c28 c13
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c29 c12
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c30 c7
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c31 c4
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c32 c3
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c33 c0
  c34
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00094.record006
