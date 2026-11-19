module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00076Data
public import GraphInputsRow24Part00076Frames
public import GraphInputsRow24Part00076Leaves
public import GraphInputsRow24Part00076Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00076.record028
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record028
def vertexColumn : Fields := ⟨10, hexnat% "372aaa68da59956358ce8b92e2785e0faa9a64d959555354cd8b52d2745d0f6c370f23a8d63a4d5332d2b2ae1b16c3b31e2719d1725c3783d0f23c4f34a8a8a89a519261582e078d1a262926545494550b41da0d4330e2348c9314e0b22c2b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1a4924d24924924d2492492492492492492489249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3dfe4fe03bcfc00000000", hexnat% "180000400000000000", 27021597764222976, 110338190870577152, hexnat% "10004030000000000", hexnat% "20020010000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2defcee43fcfc00000000", hexnat% "100000020000000000000", hexnat% "1001000020000000000", 110338190870577152, hexnat% "10004010000000000", hexnat% "20020010000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ffe4fe033efc00000000", 22517998136852480, hexnat% "30000010000000000", 109212290963734528, hexnat% "80008c00000000000", hexnat% "100100020000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2dfe5cc063b8c00000000", hexnat% "80008c00000000000", 108086391056891904, 3602879701896396800, hexnat% "20020010001000000000", hexnat% "100100020002000000000", 18300546410610688]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24ffdfe03bcfc00000000", hexnat% "180000000400000000000", 27021597764222976, 110338190870577152, hexnat% "10000004030000000000", hexnat% "20020010000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24fedfe73fefc00000000", hexnat% "100100000000000000000", hexnat% "20020000010000000000", hexnat% "80000008000000000000", 109212290963734528, hexnat% "10000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "27ccfeed72f9c00000000", hexnat% "1001000004000000000", 83457330594709504, hexnat% "180000000400000000000", hexnat% "100000002000000000", hexnat% "2200000100000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24ccdef97288c00000000", hexnat% "30000000030000000000", hexnat% "80000008c00000000000", hexnat% "21000001000000000", hexnat% "100100020002000000000", 18036663619944448, hexnat% "3200000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c15 c6
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2dcedcf86288c00000000", 11470105300959232, hexnat% "20020010031000000000", hexnat% "100100000002000000000", 18318138596655104, 3458764513820540928, hexnat% "3000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c14 c17
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c14 c18
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c19 c16
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record028_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record028_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record028_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record028_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record028_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record028_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record028_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record028_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record028_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00076.record028
