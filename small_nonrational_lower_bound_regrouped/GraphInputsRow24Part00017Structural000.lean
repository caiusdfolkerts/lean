module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00017Data
public import GraphInputsRow24Part00017Frames
public import GraphInputsRow24Part00017Leaves
public import GraphInputsRow24Part00017Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00017.record037
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 3377699720527872, (certNat% 4), 562958543355904]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), 2814758357041152, (certNat% 7), (certNat% 8), 1407374883553280]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 7516192768, (certNat% 6), (certNat% 10)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 108086391056891904, (certNat% 12), (certNat% 13), (certNat% 3)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), 6442450944, 81064793292668928]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 72057596185411584, 3659174697238528, 140741783322624, 9007199254740992]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), 7516192768, (certNat% 10)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), 72057596185411584, (certNat% 18), (certNat% 20), (certNat% 7), 4429185024]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), (certNat% 4), 6442450944, 2814758357041152]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 13), (certNat% 24), 2814758357041152, (certNat% 25)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), (certNat% 28), 7516192768, 2251808403619840, 252201579132747776]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 3659174697238528, (certNat% 7), (certNat% 30), (certNat% 31), (certNat% 32)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), 2819156403552256, (certNat% 35), (certNat% 36), (certNat% 31), (certNat% 37)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c23 c2
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00017.record037
