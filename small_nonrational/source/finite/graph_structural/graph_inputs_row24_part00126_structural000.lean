module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00126Data
public import GraphInputsRow24Part00126Frames
public import GraphInputsRow24Part00126Leaves
public import GraphInputsRow24Part00126Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00126.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record003
def vertexColumn : Fields := ⟨10, hexnat% "9c9ca568dad1ac671a56558d68d98e8b92e2b91e27a717255936745b15c595555356356362d4b4ad4749dd0ec370e6394d5334e331cd8b52ccb8ad2b2ad1b26c5bc1e8761e4751cc749ca785d1725c5783c3c0ea260d90e2382e07839894354348d0b41d90d4330e2314c3342c8b0ac1b81d0721c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6d24924db6db6da492492492492492492492492492449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4295871092410548224, 315814923869356032, hexnat% "2000100000000000000000", hexnat% "fc000000000000000", hexnat% "1f80000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4611680400610164736, 5615669739520, hexnat% "fc000000000000000", hexnat% "2000100000000000000000", hexnat% "1f80000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2e0017004f8fff80000000", hexnat% "8c000000000000000", hexnat% "1180000000000000000000", 4626744929681408, 4584664420663164928]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4611120729864273920, hexnat% "2000100000002000000000", hexnat% "800040002000000000000", hexnat% "1000080000020000000000", hexnat% "3c000000000000000", hexnat% "780000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4605634304280625152, 6051711999279104, hexnat% "2000100000000000000000", hexnat% "fc000000000000000", hexnat% "1f80000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4593108508903211008, 158913789952, 18577348462903296, hexnat% "fc000000000000000", hexnat% "2000100000000000000000", hexnat% "1f80000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200010026c10d800000000", hexnat% "200010000800080000000", 4431543132844195840, 5453577673768960, hexnat% "ec000000000000000", hexnat% "1d80000000000000000000", 15560666513408]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c11 c0
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c12 c0
  c13
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00126.record003
