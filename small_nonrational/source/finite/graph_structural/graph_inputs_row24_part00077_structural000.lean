module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00077Data
public import GraphInputsRow24Part00077Frames
public import GraphInputsRow24Part00077Leaves
public import GraphInputsRow24Part00077Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00077.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record003
def vertexColumn : Fields := ⟨10, hexnat% "2e8ad2ac3b23cb8ab2b2aaa9a8ea56a3a1e9c6a98e6a5a362da8e538ce8b8ae1ba1e4783eac571aa4e9566391e5c5594e54d4b5534cd2b46d475c3a8ce3a4d538ccb31ce8b52ccb8acab1ae1b46c5b0ed8751cc729c6725c3743c8f13c2f8e03c86916078e11a439295150d42d0754330d1312c1b41c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36da6db6da6db6db6db6926da6936926d249a69b6d26d2492493492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨84, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200328420defc00000", 1408611834134528, hexnat% "1000500000001200000000", hexnat% "10410000000000000", hexnat% "100000006000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000502535433fefc00000", 146366987889541120, hexnat% "10000000000000000", hexnat% "200000000000000000", hexnat% "100000004000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "101000506004433e23c00000", 7650410496, hexnat% "10401000000000000", hexnat% "200008000004000000", 225179981368524800, 4503599627370496]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100010233900272fc00000", hexnat% "100000004000000000000000", hexnat% "10400000000000000", hexnat% "600000001800000000", 1129201662951424, 70368744177664]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000d432defc00000", 225179981368524800, hexnat% "1000500000001200000000", hexnat% "10410000000000000", hexnat% "100000006000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [218426798369669120, 1196275093471232, hexnat% "100000006000000200000000", hexnat% "600000001800000000", hexnat% "10430000000000000", 1100610535424, hexnat% "1000100001002020000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00077.record003
