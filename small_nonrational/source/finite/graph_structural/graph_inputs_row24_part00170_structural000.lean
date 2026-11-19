module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00170Data
public import GraphInputsRow24Part00170Frames
public import GraphInputsRow24Part00170Leaves
public import GraphInputsRow24Part00170Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00170.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record002
def vertexColumn : Fields := ⟨10, hexnat% "cd23c4f07ccca3a4e8bac9aa669b16959568d93633a2e4b8ae8791e1783ecc6394e4b91e725a95a5c5655556354d4753362d4b46d8751d1743dc8ea368f1394d538cd332cccb8ad2b2ae1b46c9b0ef07a1d8791d4731e2749ca785d1715c3783d0f0bc1f2b05a2384e8c5312a4590e625494a52344d0b61344c5322c4b06e0741c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db6d369b4d249249b6934926d26da49269b4924924924924d2489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "43e04001f0f81e08000000", hexnat% "20800000004000004000000", hexnat% "1c261000000000000000", 8665901826048, hexnat% "92000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bfc673030000b84000000", 126232730961707008, hexnat% "24000080000000008000000", 1266637395197952, 8745358721024]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "43e02001f0f81d08000000", hexnat% "20800000004000004000000", hexnat% "1c461000000000000000", 8670196793344, hexnat% "92000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bfc673030001384000000", 126232730961707008, hexnat% "24000080000000008000000", 1266637395197952, 8710998982656]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20800600034000004000000", hexnat% "4000080000800408000000", hexnat% "3e0001000080000000000", 126223934868684800, hexnat% "1c070000000000000000", 2305843024246079488, 8762538590208]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00170.record002
