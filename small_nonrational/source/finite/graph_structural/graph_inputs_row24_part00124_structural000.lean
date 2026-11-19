module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00124Data
public import GraphInputsRow24Part00124Frames
public import GraphInputsRow24Part00124Leaves
public import GraphInputsRow24Part00124Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00124.record026
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record026
def vertexColumn : Fields := ⟨10, hexnat% "d92e29996639956359362d94e3392e2b91e27b61b85e1745b1725a966745c9665594e5554d54d4b5534cd4b4ad276c3a8e6358ce354cd34ccb352ccb4acab46d4731d2729c6785d1725c570de0f43c8f13c2f4709a91a26079192664551625495154341d90cc388ca324c8b06e0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6d36db6db6936db6d24934d34d349269a69a692492492492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "401eaa4003fdec000000", hexnat% "200080000000000000", hexnat% "20000000014000000000000", hexnat% "20000000000210000000", 9381033208184832]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200080030000000000", hexnat% "60000000000000000000", hexnat% "20000060014001000000000", 27395431717666816, hexnat% "18aa00000000000000", 334671904768, 696053137408]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record026_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record026_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record026_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record026_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record026_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record026_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record026_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record026_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record026_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00124.record026
