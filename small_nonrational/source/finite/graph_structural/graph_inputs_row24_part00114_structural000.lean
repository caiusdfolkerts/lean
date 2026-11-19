module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00114Data
public import GraphInputsRow24Part00114Frames
public import GraphInputsRow24Part00114Leaves
public import GraphInputsRow24Part00114Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001
def vertexColumn : Fields := ⟨10, hexnat% "1b8751b49713cb49d26ab1a66a5a719a6399969595635a4e8791e17ad16c5a9666594e4b9694e565655355352d64d4b61d4745d0f6c368ce3a4d9394cd362e4b8ad2b2ae1b46c9b16d8791cc749ca719e1745c9715e0f43c4f07d2c471a24a9264382e944d1864550b41d90cc328e0b0ac4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36da6d36da6db6da69b69b6da4db4924926d269249b6d24936d2491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨80, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4001f0683e3e00000", 18014673387388928, hexnat% "100010000a0000000000000", hexnat% "401800300000000000", hexnat% "2100000000010000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "144187c344302600000", 282026343137280, hexnat% "10000000080000000800000", 3298551660544, hexnat% "2100000002000080000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41078264201600000", hexnat% "10001000080000000800000", hexnat% "400800100002000000", hexnat% "2100000002010080000000", 1407379715391488, 550829555712]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2100000042210080400000", hexnat% "100000000a8000000800000", hexnat% "441810000000000000", 6871964450816, 1407388305326080, hexnat% "1000000100002200000", 550829555712]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00114.record001
