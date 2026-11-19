module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00115Data
public import GraphInputsRow24Part00115Frames
public import GraphInputsRow24Part00115Leaves
public import GraphInputsRow24Part00115Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00115.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record012
def vertexColumn : Fields := ⟨10, hexnat% "25c8f1d26c8f2729aa3aa5a5693a1e996958d62d98e938ce2ba1e4785e0f9d16c4f1725a93a719965598e5391e6c565655356352d58d934cd8b4ad8751d1743d70da338d9394d5334d332cc7362e4b52ccb4acab1ae1b46c5b0ed8791cc785d1725c5783d0f23c4f07ca60d82e94649296150d60d0b58330ca344c530cd0b12c2b21c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6db4db4db4db6db4db6da6934d24da4924924924924d249a492492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨75, by decide⟩, ⟨83, by decide⟩, ⟨87, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80814a9054abdff800000", 2836739999662080, hexnat% "21000000000000000", hexnat% "88000000000000000000000", 63086678666903552, 4644337115725824]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80081098ee7f9517800000", hexnat% "80800000000000000000000", 2377900603385839616, 4925813703049216, 171798691840, hexnat% "60000000080000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88800000000040000800000", hexnat% "63100000000000000", hexnat% "8108800000000000000", 2269394281431040, 63086700175294464, 11785474146304, 6685032575926272]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00115.record012
