module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00169Data
public import GraphInputsRow24Part00169Frames
public import GraphInputsRow24Part00169Leaves
public import GraphInputsRow24Part00169Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00169.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record002
def vertexColumn : Fields := ⟨10, hexnat% "26c6ca3a4e8ba69966399968b92e2b86e8791e2785ecc6b16c6698e5392e725a95a59956539715a55959362d4b4ad1b51d2745d68d6338d938cd332ce2b4acab86d1b26c5b0ed8751cc789d2729c6785c5783d0f23c2f8706a458961381e8a46986615454958344d0752328c6344c9312c2b06d0721c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6da6da4926da4db6db69249b49249269249249249a492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "19180048e1e60290000000", 9727775195120271360, hexnat% "70000000100000000", hexnat% "10600000000000000000000", 6218837766701056, 2046015045632]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10080048f7d3dd70000000", hexnat% "10008000000000000000", 48378511622144, hexnat% "70700000200000000", hexnat% "10f00000000000000000000", 2147483648]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "70701001300000000", hexnat% "1000004800000c10000000", hexnat% "18008000000000000000", hexnat% "10f00000000000000000000", 64952549899239424, 1927903444992, 4569570325037056]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00169.record002
