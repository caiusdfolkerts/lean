module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00086Data
public import GraphInputsRow24Part00086Frames
public import GraphInputsRow24Part00086Leaves
public import GraphInputsRow24Part00086Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00086.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004
def vertexColumn : Fields := ⟨10, hexnat% "f4ab29c2f0f25a95a1eaa6598e6a5956358b61db0e8b92e8791e0f8f1aa569a65592e479716a5594e5a5555354b51d70da362d4b4ad8751d2743db0ea358ce3a4d5334cb31cf0b52e2b4ac6b86d1b16c3bc1e8751cc789d2729c6785d1725c570de0e4382e078e134685294958350d0b41d50c6314e0b42c2b06e0741c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6db6924926db6da69349a4924926d26934924924924d2492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30004133684fbfe000000", hexnat% "1680000000000000000", hexnat% "4000010000400000000000", 64871186038784, 17005592192950992896, hexnat% "3c00000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "165ff120433fa000000", hexnat% "100080000000000000000", hexnat% "7e00000000000000000000", 136064563937280, 10273871076786176]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "12dff1200b3be000000", hexnat% "100400000000000000000", hexnat% "7e00000000000000000000", 139912854634496, 10273872083419136]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1004810369c6bfe000000", 109401406963712, hexnat% "7e00000000000000000000", hexnat% "1248000001000000000", hexnat% "16f00000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11016de836acbbfe000000", 1657324662872342528, 91534343012352, hexnat% "6e00000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13016de936fffbfe000000", 1585267068834414592, hexnat% "6c00000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11016de8327ffbfe000000", 1266637395197952, 1657324662872342528, hexnat% "6e00000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "125ff320833fa000000", hexnat% "100480000000000000000", hexnat% "7e00000000000000000000", 106686987632640, 25013889531904, 1266637462306816]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11004c2036ac99ce000000", 146834194432, 91534343012352, hexnat% "6e00000000000000000000", hexnat% "1df00000000000000", hexnat% "1200000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10048023683fbfe000000", 136339441844224, hexnat% "1249000000000000000", hexnat% "7e00000000000000000000", hexnat% "16d00000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000000328010ce000000", hexnat% "16c0000000000000000", hexnat% "7e00000000000000000000", 185488900096, 289357375570182144, hexnat% "1fb00000000000000", 139363098820608]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c16 c3
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c17 c2
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00086.record004
