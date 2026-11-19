module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00107Data
public import GraphInputsRow24Part00107Frames
public import GraphInputsRow24Part00107Leaves
public import GraphInputsRow24Part00107Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00107.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record023
def vertexColumn : Fields := ⟨10, hexnat% "ad26c9723c2f1aa668ba71a6695a362d98e538ae1b89e1783eac5a99a599966392e5c5a9665a56558d4b56364d5362d2b46d8749d1743d70da398d9394e332cd8b4acab1ad1b26c5b0ed8791d4731e2719e1715c3743c8f528a62584e0b81e52645894a5854951342d0758350ca324d0b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6d349249b6db6d249269249249269b492492492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5003f1fc05207d0000000", hexnat% "ac0000000000020000000", hexnat% "2000000000808000000000", 14637008026599424, 6917529233799512064, 49478023249920]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e00307d00197ff0000000", hexnat% "1c0000000000000000000", 14847805021487104, hexnat% "c0280000000000000", 42331197669376, hexnat% "2000030040000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9800c6b800b7ff0000000", hexnat% "640000000000000000000", 14847805021487104, hexnat% "301400000000000000", 57724360458240, hexnat% "2000030040000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20402b1b74c0cfd0000000", hexnat% "144000002000000000", hexnat% "780000000000000000000", hexnat% "800002000091020000000", 324259173170675712, 59373627899904]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4003f1fc0102fd0000000", 6917529096360558592, hexnat% "2140000000000000000000", hexnat% "a80000000000020000000", 14848079899394048, 52226802319360]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1003f1fc0022fd0000000", 6917529096360558592, hexnat% "2440000000000000000000", hexnat% "a80000000000020000000", 14848079899394048, 67619965108224]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f0900000780000000", hexnat% "ac0000000000020000000", 14777745514954752, 6250996282790248448, hexnat% "2500000000000050000000", 2305843215372124160, 140187732541440]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c11 c0
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c12 c0
  c13
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00107.record023
