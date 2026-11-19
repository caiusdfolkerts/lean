module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00207Data
public import GraphInputsRow29Part00207Frames
public import GraphInputsRow29Part00207Leaves
public import GraphInputsRow29Part00207Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00207.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record004
def vertexColumn : Fields := ⟨10, hexnat% "7c1b85e1e47532c6b16c6715c789d26c9723c9aa5a99a5693a2e87a71aa669a66598e6659563598e53a2e4b8ae1ba1e4789e179e1745b15c4f16a569665594e4b91e5c5a95a59956539595554d56354d8b52d2b46d8751d2745da8e6338cd32cc732ac6b86c9b16c3ba1e4731e2729c6785c8f13c2f651544722a258568381e8a4951560d0762328c6324c5382c2b06e0721c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db4db49b6db6db6db6db49369b6924db6db6db6db6da49b4db492492492492492492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨115, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8c0000e0200001c0f300220000000", hexnat% "4000000080008104000000", hexnat% "580000000000000000000", 55163486208, 13675175870464, 214404767416320]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8c0000c0300001c0f024030000000", hexnat% "4000000080008104000000", hexnat% "20480000000000000000000", 63484985344, 30992484007936, 247390116249600]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8c0000e0780001c07012028000000", 38281146655571968, hexnat% "40000000000001c0000000", 60397977600, 31129922961408, 248489627877376]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800000240800004823cf3e4000000", 51942260736, 214404767416320, hexnat% "4000000000001805000000000000", hexnat% "80000c0300000000000000000000", hexnat% "400000008000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8c0000e0780001c06124030000000", 2533274924613632, hexnat% "4000000080008104000000", 63350767616, 14499809591296, 246290604621824]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c000004080000483ffb1cc000000", hexnat% "100000000004030000000", 60129542144, hexnat% "80000000000001804000000000000", hexnat% "600000008000000000000", hexnat% "e0000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8c0000e0780001c06134030000000", 2533274924613632, hexnat% "4000000080008104000000", 63350767616, 13400297963520, 246290604621824]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "880000a0180001402110000000000", hexnat% "4000000080008104000000", hexnat% "4000040000000801000000000000", hexnat% "60000000c000000000000", 13675175870464, 64290291712, 248489627877376]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨111, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00207.record004
