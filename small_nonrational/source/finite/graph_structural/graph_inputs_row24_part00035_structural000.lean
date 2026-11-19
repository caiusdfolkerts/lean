module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00035Data
public import GraphInputsRow24Part00035Frames
public import GraphInputsRow24Part00035Leaves
public import GraphInputsRow24Part00035Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00035.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record008
def vertexColumn : Fields := ⟨10, hexnat% "3e07c3c8ea368ba1eb168d876c392e1b89e1783e3c4e9364b91e7158d475c352d1b49d1743d38f13a4e538ccb3c2d8b52d2b2ac9b16c3b89d2719d1725c5783c8f13c1f348723286ac1a160d90e0b8d11c4c91a705854354342dc0cc318e1324c530cd0b22c4b0ae0741c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6d24d24924da493492493692492492492492492489249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fecfff1ff0f9c400000000", hexnat% "120000000002000000000", 2306126717573398528, 13835062453328674816, 3940718393425920, hexnat% "10000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fe4ffb3e10f24c00000000", 4222330809090048, 135109638088556544, hexnat% "48000000000000000", hexnat% "180000000080000000000", hexnat% "30000000040000000000", 4611686018427387904]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffc7fb3ff0f9c400000000", hexnat% "48000002000000000", hexnat% "8000001020800000000", hexnat% "30000000040000000000", 3940718393425920, 4611686018427387904]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fecff93e10f24c00000000", 4222330809090048, 135109638088556544, hexnat% "60000080000000000", hexnat% "120000000000000000000", 13835062453328674816, hexnat% "10000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ce4f393c0ff27c00000000", 139613237715927040, hexnat% "10004000040000000000", hexnat% "80020000080000000000", hexnat% "48000000000000000", hexnat% "3000c00200000000000000", hexnat% "120000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fe4ff93e1ff03c00000000", 135109912966463488, 13835062453328674816, hexnat% "60000080000000000", hexnat% "30000000000000000000", hexnat% "180000000000000000000", 2199023255552]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c6 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ce97381c0ff0bc00000000", 139612962838020096, 13835062453328674816, hexnat% "60000080000000000", hexnat% "120000000000000000000", hexnat% "3000c00200000000000000", hexnat% "48012000020000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fedf39fc00766c00000000", hexnat% "60000090000000000", hexnat% "c00210800000000000", 4222193370136576, 135108538576928768, hexnat% "120000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "fffffffffffffc00000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c17 c9
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c18 c8
  c19
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00035.record008
