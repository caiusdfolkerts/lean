module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00172Data
public import GraphInputsRow24Part00172Frames
public import GraphInputsRow24Part00172Leaves
public import GraphInputsRow24Part00172Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00172.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record003
def vertexColumn : Fields := ⟨10, hexnat% "dccc8da8e93ac9b16a599695956358ce8b92e2b86e8791e2785ecc4d98e539c9715a559595555354cd8b52d2b46d8751d2745dc8f13a4d9394d5334e334cccb8ad2b2ac6b86d1b0ef07a1d8791d4731ca719e1745c9715e0f43c1f2685a899262384e0b899166254948d1342d88d2384d1324c5322c4b0ac1b81d0721c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "da6d36db69249b49a6d36db69249b492492492492492492492492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨97, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1207c120303ffff07fc0000000", hexnat% "c0000c000000000000000", 17042430230528, hexnat% "4c0000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1207cd00283fffe07fc0000000", hexnat% "44c000000000000000", hexnat% "20100000000000000000", 34634616274944]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10038100203fffe07f40000000", hexnat% "c0000c000000000000000", hexnat% "44000000000000080000000", hexnat% "2000020000000100000000000", 17042430230528, hexnat% "5c0000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "203c0000800000000000", hexnat% "203c000000000000000000000", hexnat% "10040100400090008040000000", hexnat% "c0000c000001e00000000", 2310100318236442624, 2260877381684166656, 34503619772416]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c5 c4
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00172.record003
