module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00029Data
public import GraphInputsRow29Part00029Frames
public import GraphInputsRow29Part00029Leaves
public import GraphInputsRow29Part00029Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00029.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record004
def vertexColumn : Fields := ⟨10, hexnat% "7515c373c274b4ab295a3687ae19c6c9aa665956359362db0ea394e33a2e4789e1783ef079174731ac749b2719a6559366391e78571725a9595554d54d4b5c368d534cd8b51d2745de0f43b0dc3c8ea364d5334d332cc73c2e8b92d4b32c6b46c9b16c3bc1e8761d4731e2749ca745c9715c3783d0f23c4f07c3c8a82e544d18a4590e515254350b41dc0e8350cc388e0b12c2b41c8709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db6db6db69b69b4db6da4936da4926db49249249a4db49249b492492492692491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4006130f01824c8f7e000000", hexnat% "4000000000000031000000000", hexnat% "8180c000000000000000000", 1153344129388773376, 17008969892671520768]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000600098c0fcf9c3e000000", 8070450532247928832, hexnat% "400000000180000340000000", hexnat% "c000000006000000000", hexnat% "81800000000000000000000", hexnat% "13060000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40061b0e41804ecf7a000000", hexnat% "4000000000000011000000000", hexnat% "81804010000000000000000", 12397846824197554176, 1153343854577975296]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4006170e21804daf7a000000", hexnat% "4000000000000021000000000", hexnat% "81808010000000000000000", 14703689833411248128, 1153343992016928768]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400000008fd0f83df3a000000", hexnat% "600000000440000000000", hexnat% "400000000080080040000000", hexnat% "c010000002004000000", hexnat% "13060000000000000000", hexnat% "81800000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400000008fc8f83bf3a000000", hexnat% "600000000440000000000", hexnat% "400000000100080040000000", hexnat% "c010000004004000000", hexnat% "13060000000000000000", hexnat% "81800000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60c09100fcfef3e000000", hexnat% "4400000000000000000000000", 17005592192950992896, 69793218560, hexnat% "13060000000000000000", hexnat% "81800000180000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "600080000470326000000", hexnat% "4400000000000000000000000", hexnat% "1f070000000000000000", 671491293184, 17009532842624942080, hexnat% "81800000180080000000000", 1153344129388773376]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00029.record004
