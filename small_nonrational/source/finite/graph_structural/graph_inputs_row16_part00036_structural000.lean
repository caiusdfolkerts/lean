module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00036Data
public import GraphInputsRow16Part00036Frames
public import GraphInputsRow16Part00036Leaves
public import GraphInputsRow16Part00036Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00036.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record001
def vertexColumn : Fields := ⟨10, hexnat% "9e354971721e8b62ba1e0fb519c5719a4e9966391e745c5655554b5a364d534ad8745d0f56354d332cc7352c6b86c5b0ed8729e1725c3783d0f0bc1f2a91623a5154471924a91a6154560d234a344c3322c2b41c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db4da4924d349349a4db49269b492492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9223389629653188608, 225179998548393984, 219902359109632, 1497366528, 483183820800, 1155736804129767424, 901845825380941824]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00036.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00036.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record007
def vertexColumn : Fields := ⟨10, hexnat% "1ac370da35a362d8ce4b8ae2785eb86d1ac5a9365a5356352d58d3352d2b49d1772398ce334e332ce4b52ccb4acab26c5b31e2729e1745c9715c3723c4f0bc1f9492643a51344c9494a52550d2364388d2384c5342c4b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6d36da6d24d249269349a49369a492492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [89800145675223040, hexnat% "20000002000000000", 1333065489701666816, 1116825714688, 109951162777600, 1073741824]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1333074285828243456, hexnat% "20004002020800000", 109955457744896, 1941341995008, 16607023625928704, 72057596252520448, 1480589312]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00036.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00036.record034
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record034
def vertexColumn : Fields := ⟨10, hexnat% "dc4f2ca9aa5a368d64d8ce8b8ae2785e0fac99a65936539355353362d4b4ad4749d1743db0f2398e5354cd34ce8b92ccb8acab1ae1b26c5b0ed8731e2729c9715c3783c8f13c2f07d2645a4932629165254548d0b41d90cc388d2344c5341c8709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db4db6da4936924924924924d24db69a49249a691249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8005d50b8575600000", 11258999202643968, 9223512774343131136, 686095255732224, 144115190223339520, hexnat% "16000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80047c2b853d600000", 108086392130633728, 422212465065984, 144115190223339520, 650910883643392, hexnat% "1e000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1e002f3841d600000", 281476587323392, 131730289100587008, hexnat% "800400080100000000", 146366990037024768, 9007199254740992]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1e27fd384c9600000", 108086391056891904, 35184707633152, hexnat% "800400080100000000", 536870912]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1627efb849d600000", 9295429630892703744, hexnat% "800400000100000000", 281476587323392, 36028797018963968]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1e37ca28488600000", 652010395271168, hexnat% "800400080104000000", 281476587323392, 36028797018963968, 285212672]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8004080a0104600000", 422763294621696, 9295429630892703744, hexnat% "16200010000000000", 686112569819136, 68679894317400064, 2969567232]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record034_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record034_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record034_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record034_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record034_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record034_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record034_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record034_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record034_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00036.record034

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00036.record039
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record039
def vertexColumn : Fields := ⟨10, hexnat% "b51ac3c8ea958d64b8ae27ad13c5a93a6c569695954d56352d2b49d98d6338cd32cc7332cab1ac9bc1e4731d2729d1725c5783c8f0bc1f9492a8590e38651345292a6152550d2364348c6384c5342c2b81d0705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db4d36924da49249249a69349a692492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdfffeff6bf000000", 2305843013508661248, 35433480192, 17592186044416]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fde6e2fd6b4000000", 17733953519616, 4573968388325376, 108227128545247232, 2306124484190404608, 35567697920]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fd87c4edefd000000", 432346663739195392, 52913997086720, 73042756489969664, 36028797018963968, 2305843013508661248]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f7fffdff3f7000000", 9223372054034644992, 34493956096, 35184372088832]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c1 c6
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f79f19ef3a6000000", 36301332021248, 633318714376192, 433471464134410240, 9225623836668461056, 35567697920]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f7863cedbef000000", 108086528495845376, 53876069761024, 296111675768045568, 144115188075855872, 9223372054034644992]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f787186dfff000000", 9226749736575303680, 633318697598976, 62809601736704, 432345564227567616, 108086391056891904]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fde7c07d6f4000000", 633318714376192, 61710090108928, 108227128545247232, 2306124488518926336, 34493956096]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f5ee00ed2e4000000", 2306265226007281664, 9226749754023608320, 4573968388325376, 34493956096, 54013508714496, 72620543991349248]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c17 c5
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c18 c4
  c19
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record039_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record039_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record039_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record039_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record039_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record039_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record039_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record039_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record039_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00036.record039
