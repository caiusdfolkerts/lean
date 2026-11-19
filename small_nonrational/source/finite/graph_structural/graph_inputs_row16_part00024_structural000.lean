module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00024Data
public import GraphInputsRow16Part00024Frames
public import GraphInputsRow16Part00024Leaves
public import GraphInputsRow16Part00024Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record019
def vertexColumn : Fields := ⟨10, hexnat% "2aa56a3aa99564d8ce2b86e2785e0faa956639a95554d4cd2b46d2745d0f6a354e334ce4b52ccb2ac6b86d1b26c5ba1d8731e2749ca719c9715c8f13c2f07e8a8a83a519160da898a439515150d68350e2344c3382c8b12c2b06d0721c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "269a4db6d269a4db6d2492492492492492492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1001008004880000000", hexnat% "10010011280000000000", hexnat% "800802000108000000", hexnat% "4004004100010000000", hexnat% "20020000060000000", 781684047872, 218802813927424]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record025
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record025
def vertexColumn : Fields := ⟨10, hexnat% "29c8f16aa68ba59a9655936a386e8789e0f969a66392e565a55558d535a364d8b46d8749d0f563a4d9354cb3a2d4b32d2b2ac6b86c9b0ee8751d2719e1745c9715e0f23c1f4c8361382ea4531a26150d60d1342d50d2344c930cc8b12c2b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db69a6d34db4d24924d249249249a4d2492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "12837b0059c5000000", hexnat% "400000000220000000", 612489549624377344, 149533581377536, 8246337208320, 123145436528640]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400b0af19979000000", hexnat% "28000000000000000", 6880537608192, 36037593212649472, hexnat% "100011000080000000", 27021597764222976]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "52811b53d9b7000000", 39591142752256, 149534655119360, 63050394783186944, 720575940379279360]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1088f29fd89f000000", 146366988963282944, hexnat% "420000000100000000", 387028629848064, 72057602627862528]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [863239811744399360, hexnat% "28000001000000000", hexnat% "400000000300000000", hexnat% "100001004000000000", 40681930227712, 2748779069440]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "500113754be2000000", 144115188495286272, 11613591568384, 65302194663981056, hexnat% "28000000000000000", 576601489791778816]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [804877530531102720, 9223512774343131136, 58546795155816448, hexnat% "400000000200000000", hexnat% "120000000080000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400b2b37cbfb000000", 211174952009728, 58546795222925312, hexnat% "120000000000000000", 9223380832947798016]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "420b2b108b7b000000", 105553116266496, 58546795222925312, 7971459301376, 9223521639155630080, hexnat% "100000000080000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400303100b62000000", 9799973526646554624, 69805794291351552, hexnat% "120000000081000000", 40681930227712, 70369146830848, 11888469475328]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record025_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record025_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record025_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record025_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record025_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record025_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record025_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record025_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record025_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record025
