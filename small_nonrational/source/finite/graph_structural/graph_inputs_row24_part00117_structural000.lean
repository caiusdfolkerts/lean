module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00117Data
public import GraphInputsRow24Part00117Frames
public import GraphInputsRow24Part00117Leaves
public import GraphInputsRow24Part00117Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00117.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record023
def vertexColumn : Fields := ⟨10, hexnat% "2b86d2749b23c2f2b29caaa9a8eaa6a3a2ea6665a568d8b61d98e93a2e2b86e8789e0f9b19c6693a6392e5a5655352d475634ad2743d98ce394e332cc7362e4b32e2b2ac6b86c9b0ed8751ca719c9715c3743c8f0bc1f9a06c64a4a4584e644b12a469195150d44d0b58344c9322c4b41c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36d36db4db6d36db4da6da6934d249a69b6d349349a693492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨77, by decide⟩, ⟨83, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20800910a8028d0d2000000", hexnat% "20000010000404000000", 4611690416473899008, 91197892454252544, 9277800448, 2305845208236949504]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8001068102ed096000000", hexnat% "20000800000000000000000", 127226689473216512, hexnat% "10200000040000000", hexnat% "20000000000400000000", 9277800448]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [649691074259845120, 58546795155816448, hexnat% "10200000000000000", hexnat% "20000000000000000000", hexnat% "20000006000004000000000", hexnat% "800900000040000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2080090681426c003000000", 8883133218816, 18014401462272000, hexnat% "10380000000000000", hexnat% "20000000000000000000", 8724152320]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "12800209001000000", hexnat% "20800104000004000000000", 10995317604352, hexnat% "800000040000000000", hexnat% "20000290000440000000", 11576279040, 91197892454252544]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00117.record023
