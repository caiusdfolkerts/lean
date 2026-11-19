module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00080Data
public import GraphInputsRow24Part00080Frames
public import GraphInputsRow24Part00080Leaves
public import GraphInputsRow24Part00080Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 4638707618339094528, (certNat% 4), 32178700288, 68410239090688, 72292889526272]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013
def vertexColumn : Fields := ⟨10, (certNat% 5)⟩
def kindColumn : Fields := ⟨3, (certNat% 6)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [1, 2, 3, 4]
def candidates : List (Fin raw.n) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 1
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨20, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c0 c2
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c0 c3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), 10737418240]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 35184372088832, 4612811918334230528, (certNat% 10)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c1 c0
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c0 c9
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c0 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 8), 13194139533312]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c7 c13
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 10), 8804682956800, 39584566083584, 18014398509481984]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c16 c8
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), 19703248369745920, (certNat% 15), 4611686018427387904]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), 4613374868287651840, (certNat% 18), 18014398509481984]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), 57174873079808, 4613374868287651840, (certNat% 20), (certNat% 21), 2323857407723175936]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c22 c17
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 39926015983616, (certNat% 23), 4613515605776007168, 9223389766479773696, 288230376151711744]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 28147497671065600, (certNat% 21), 4611686499463725056, 2199023255552]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), 8804682956800, 4611686499463725056, (certNat% 26), 21392098297118720, 39584566083584]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), 2305843028843036672, (certNat% 28), (certNat% 29), 57174604644352, 4611686430761025536, 22095785738895360]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c29 c24
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c30 c23
  c31
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record013
