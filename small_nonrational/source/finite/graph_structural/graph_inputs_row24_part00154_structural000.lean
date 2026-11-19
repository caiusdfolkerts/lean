module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00154Data
public import GraphInputsRow24Part00154Frames
public import GraphInputsRow24Part00154Leaves
public import GraphInputsRow24Part00154Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00154.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record003
def vertexColumn : Fields := ⟨10, hexnat% "1b45d0f49b13c2f07c6c9723ca5a4e8ba1e9a6598e665956359362d8764b8ae1b91e2785e0f9b19a6594e4b91e5a5995954d4b51d64d8b52d2b46d4749d1743d68d9394d332cc7392d2b2ac6b86d1b26c5b0ef07a1d8791d2729c6745c9715c3743c8f13c2f07c789306c9285a91a0e139312c439494a58342d44c9382c1b81d0721c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36d369b69b4db6db6db4da69b4926d269249b69a6934db49249249349b492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨98, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24080090107c4608f60f800000", hexnat% "200000810800000000", hexnat% "400000000000000000000000", 4510199918362624, hexnat% "4c30000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48008012180689f68f000000", hexnat% "204400000800000000", hexnat% "20000000002000000000000000", hexnat% "4c10040000000000000", 4510197779267584, hexnat% "4000010000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48008011180689f64f000000", hexnat% "204400000800000000", hexnat% "20000000002000000000000000", hexnat% "4c20040000000000000", 4510198853009408, hexnat% "4000010000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44000100300548f76cf800000", hexnat% "103c00000000000000", hexnat% "20000080004000000000000000", hexnat% "200000000800000000", hexnat% "4c00002008000000000", hexnat% "80000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44000100300528f76cf800000", hexnat% "103c00000000000000", hexnat% "20000080004000000000000000", hexnat% "200000000800000000", hexnat% "4c00004008000000000", hexnat% "80000000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4f33c560096c1000000", hexnat% "4080090000000000000000000", 446911479808, 16492682805248, hexnat% "400000000000800000000000", hexnat% "20000000004000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4f33c460486c9000000", hexnat% "4080090000000000000000000", 515496738816, 4515694263664640, hexnat% "400000000000800000000000", hexnat% "20000000004000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24480094a304408906c3800000", hexnat% "103800000000000000", 4611686052787126272, 481237663744, hexnat% "400006028000000000", 4507997673881600]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24000004907c40007ecf800000", hexnat% "430000000000000000", hexnat% "200000810000000000", hexnat% "480090000000000000000000", 4519542545973248, 1688849860263936]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44800948320508ff6cf800000", hexnat% "204400000800000000", hexnat% "101800000000000000", hexnat% "20000000000000000000000000", hexnat% "400006000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "240000848064000006c3800000", 515597402112, hexnat% "480010000000010000000000", hexnat% "131840000000000000", 6199596313214976, 149533581377536, hexnat% "600000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c16 c3
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c17 c2
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00154.record003
