module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00232Data
public import GraphInputsRow29Part00232Frames
public import GraphInputsRow29Part00232Leaves
public import GraphInputsRow29Part00232Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00232.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record015
def vertexColumn : Fields := ⟨10, hexnat% "278791743d16c3b07c78b525c8f2b296a3aa5a1e9c66996639956359362d876538ce4b8ae1ba1e1783e787519c5713c6c99a5693a6598e479694b54b61d0f743b0dc368d6338f1394d5334d332cc73a2e4b52ccb4acab1ae1b16c3b61d2729e1725c3783d0f0bc1f5c0e84d0ac94952928ca4588e4c4a9494a5454352342d84d1382c8b41c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "369b4da4d349b6da69b69a6db6da6db4db4934db6da49a6d269a69b492492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨72, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩, ⟨106, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "418c1410100001d010748000000", hexnat% "80000000080000000000000000", 16717361816799281152, hexnat% "2000400000000240000000000", 37379637248, 17867063951360]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "498814101080005010648000000", 16717361816799281152, hexnat% "2000400000000240000000000", 4503606136930304, 35165044736, hexnat% "400000000008104000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840000000e811204ffc000000", hexnat% "1000000000000c000000000000", hexnat% "2000000000000140000000000", hexnat% "400014000000000000000000000", hexnat% "80800500000000010000000000", hexnat% "1080000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8ac0450008000135066c000000", hexnat% "400000001000000000000000000", 41070624768, 16717361816799281152, hexnat% "10010000000014000000000000", 2252074691592192]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48a80450108000105064c000000", 35185177395200, 16717361816799281152, hexnat% "10010000000014000000000000", 40802189312, hexnat% "400000000008104000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48881410108000501064c000000", hexnat% "10000000000018000000000000", 16717361816799281152, hexnat% "2000400000000240000000000", 41607495680, hexnat% "400000000000104000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ac0440108401d354ffc000000", 12105675798371893248, hexnat% "80000100000000000000000000", hexnat% "400010000000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ac0450108481d354ffc000000", 11529215046068469760, hexnat% "10010000000000000000000000", hexnat% "480000000000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48a81450000e819250ffc000000", hexnat% "10000000000004000000000000", hexnat% "400000000000104000000000", hexnat% "1080000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "880440000e819050ffc000000", hexnat% "80000100080000000000000000", hexnat% "2000000000000300000000000", hexnat% "10010000000004000000000000", hexnat% "400000001000000000000000000", hexnat% "400000000000004000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4888045010800010506cc000000", 16717361816799281152, hexnat% "2000000000000300000000000", 39460012032, hexnat% "10010000000014000000000000", hexnat% "400000000008004000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "488814500000001010084000000", hexnat% "2400000000000100000000000", hexnat% "1000000000001c000000000000", hexnat% "1080000040000000000", 16717361843777044480, 39460012032, 35459249995776]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c16 c5
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c17 c4
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c18 c3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c19 c2
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record015_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00232.record015
