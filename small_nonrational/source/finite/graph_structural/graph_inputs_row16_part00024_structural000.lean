module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00024Data
public import GraphInputsRow16Part00024Frames
public import GraphInputsRow16Part00024Leaves
public import GraphInputsRow16Part00024Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

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

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "a716aa9956a394e8b86e4789e0f969a66a5996955568d5346d8751d2743da8d6364d53a2d4b8ad2b1ac9b0ee8751cc789ca745c570de0f43c8f13e2c468662582e07a2946685894652560d0b41d50c6344c9342c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db4924da49a69249a49a492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 49)]))
 (.leaf ([(facetIndex 55), (facetIndex 57)])))
 (.branch 3
 (.leaf ([(facetIndex 61), (facetIndex 69)]))
 (.leaf ([(facetIndex 62), (facetIndex 68)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 70)]))
 (.leaf ([(facetIndex 71)])))
 (.branch 7
 (.leaf ([(facetIndex 72)]))
 (.leaf ([(facetIndex 73)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "3eb130000d00082z29;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record001" 43

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record001" "{\"ridges\":[[11,321],[11,322],[18,641],[18,644],[37,321],[38,641],[38,644],[44,321],[44,322],[45,650],[46,322],[48,321],[48,322],[49,674],[55,332],[56,644],[57,340],[58,641],[58,644],[60,641],[60,644],[61,664],[62,360],[68,332],[69,650],[70,340],[71,674],[72,360],[73,664]],\"owners\":[[11,321,[55,57,62],[37,44,46,48]],[37,321,[62],[11,44,46,48,55,57]],[44,321,[57],[11,37,46,48,55,62]],[48,321,[55,57],[11,37,44,46,62]],[11,322,[68,70,72],[37,44,46,48]],[44,322,[70],[11,37,46,48,68,72]],[46,322,[68,72],[11,37,44,48,70]],[48,322,[68,70],[11,37,44,46,72]],[18,641,[45,49,61],[38,56,58,60]],[38,641,[61],[18,45,49,56,58,60]],[58,641,[45,49],[18,38,56,60,61]],[60,641,[45,61],[18,38,49,56,58]],[18,644,[69,71,73],[38,56,58,60]],[38,644,[73],[18,56,58,60,69,71]],[56,644,[71],[18,38,58,60,69,73]],[58,644,[69,71],[18,38,56,60,73]],[60,644,[69,73],[18,38,56,58,71]],[45,650,[69],[]],[69,650,[45],[]],[49,674,[71],[]],[71,674,[49],[]],[55,332,[68],[]],[68,332,[55],[]],[57,340,[70],[]],[70,340,[57],[]],[61,664,[73],[]],[73,664,[61],[]],[62,360,[72],[]],[72,360,[62],[]]],\"edges\":[[40,[11,37,44,46,48,55,57,62,68,70,72]],[43,[18,38,45,49,56,58,60,61,69,71,73]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,10,12,16],[-3,16],[-5,12],[-8,10,12],[-1,17,19,21],[-5,19],[-7,17,21],[-8,17,19],[-2,6,9,15],[-4,15],[-13,6,9],[-14,6,15],[-2,18,20,22],[-4,22],[-11,20],[-13,18,20],[-14,18,22],[-6,18],[-18,6],[-9,20],[-20,9],[-10,17],[-17,10],[-12,19],[-19,12],[-15,22],[-22,15],[-16,21],[-21,16],[-6,23],[-9,23],[-10,24],[-12,24],[-15,25],[-18,25],[-26,16,17],[-16,26],[-17,26],[-27,19],[-19,27],[-28,20],[-20,28],[-21,29],[-22,30],[-24,31],[-23,31],[-23,-24,32],[-26,33],[-34,26],[-25,-26,34],[-33,35],[-34,36],[-31,35],[-31,-33,36],[-31,-34,37],[-32,36],[-38,27,28],[-28,38],[-27,38],[-27,-28,39],[-30,40],[-29,40],[-40,41],[-38,41],[-38,-40,42],[-39,42],[-35,-42,43],[-36,-41,43],[-37,43],[-43],[1,3,5,7,8,10,12,16,17,19,21],[2,4,6,9,11,13,14,15,18,20,22]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":321,\"a\":11,\"owners\":[55,57,62]},{\"tag\":\"mate\",\"ridge\":321,\"a\":37,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":321,\"a\":44,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":321,\"a\":48,\"owners\":[55,57]},{\"tag\":\"mate\",\"ridge\":322,\"a\":11,\"owners\":[68,70,72]},{\"tag\":\"mate\",\"ridge\":322,\"a\":44,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":322,\"a\":46,\"owners\":[68,72]},{\"tag\":\"mate\",\"ridge\":322,\"a\":48,\"owners\":[68,70]},{\"tag\":\"mate\",\"ridge\":641,\"a\":18,\"owners\":[45,49,61]},{\"tag\":\"mate\",\"ridge\":641,\"a\":38,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":641,\"a\":58,\"owners\":[45,49]},{\"tag\":\"mate\",\"ridge\":641,\"a\":60,\"owners\":[45,61]},{\"tag\":\"mate\",\"ridge\":644,\"a\":18,\"owners\":[69,71,73]},{\"tag\":\"mate\",\"ridge\":644,\"a\":38,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":644,\"a\":56,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":644,\"a\":58,\"owners\":[69,71]},{\"tag\":\"mate\",\"ridge\":644,\"a\":60,\"owners\":[69,73]},{\"tag\":\"mate\",\"ridge\":650,\"a\":45,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":650,\"a\":69,\"owners\":[45]},{\"tag\":\"mate\",\"ridge\":674,\"a\":49,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":674,\"a\":71,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":332,\"a\":55,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":332,\"a\":68,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":340,\"a\":57,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":340,\"a\":70,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":664,\"a\":61,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":664,\"a\":73,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":360,\"a\":62,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":360,\"a\":72,\"owners\":[62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":45,\"full_literals\":[-6,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-9,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":55,\"full_literals\":[-10,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":57,\"full_literals\":[-12,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":61,\"full_literals\":[-15,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-18,25]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[62,68],\"full_literals\":[-26,16,17]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":62,\"full_literals\":[-16,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":68,\"full_literals\":[-17,26]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[70],\"full_literals\":[-27,19]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-19,27]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[71],\"full_literals\":[-28,20]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":71,\"full_literals\":[-20,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":72,\"full_literals\":[-21,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":73,\"full_literals\":[-22,30]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-23,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-23,-24,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-34,false,26],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-26,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-34,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-33,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-31,-34,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,27,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-28,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-38,-40,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-35,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[11,37,44,46,48,55,57,62,68,70,72]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,38,45,49,56,58,60,61,69,71,73]}]}"
  "p cnf 43 72\n-1 10 12 16 0\n-3 16 0\n-5 12 0\n-8 10 12 0\n-1 17 19 21 0\n-5 19 0\n-7 17 21 0\n-8 17 19 0\n-2 6 9 15 0\n-4 15 0\n-13 6 9 0\n-14 6 15 0\n-2 18 20 22 0\n-4 22 0\n-11 20 0\n-13 18 20 0\n-14 18 22 0\n-6 18 0\n-18 6 0\n-9 20 0\n-20 9 0\n-10 17 0\n-17 10 0\n-12 19 0\n-19 12 0\n-15 22 0\n-22 15 0\n-16 21 0\n-21 16 0\n-6 23 0\n-9 23 0\n-10 24 0\n-12 24 0\n-15 25 0\n-18 25 0\n-26 16 17 0\n-16 26 0\n-17 26 0\n-27 19 0\n-19 27 0\n-28 20 0\n-20 28 0\n-21 29 0\n-22 30 0\n-24 31 0\n-23 31 0\n-23 -24 32 0\n-26 33 0\n-34 26 0\n-25 -26 34 0\n-33 35 0\n-34 36 0\n-31 35 0\n-31 -33 36 0\n-31 -34 37 0\n-32 36 0\n-38 27 28 0\n-28 38 0\n-27 38 0\n-27 -28 39 0\n-30 40 0\n-29 40 0\n-40 41 0\n-38 41 0\n-38 -40 42 0\n-39 42 0\n-35 -42 43 0\n-36 -41 43 0\n-37 43 0\n-43 0\n1 3 5 7 8 10 12 16 17 19 21 0\n2 4 6 9 11 13 14 15 18 20 22 0\n"
  "73 -37 0 70 69 0\n74 35 0 51 53 48 45 37 38 32 33 2 29 7 1 4 3 25 71 0\n75 -42 0 74 70 67 0\n76 -39 0 75 66 0\n77 26 19 0 24 6 37 38 2 29 7 22 5 8 71 0\n78 38 34 0 58 59 42 40 15 20 77 50 34 35 10 27 18 17 16 13 72 0\n79 27 36 0 52 78 40 57 77 41 48 21 54 31 46 0\n80 6 22 4 9 11 13 14 15 18 20 0 72 9 0\n81 36 0 75 76 52 56 78 65 61 44 14 26 79 39 60 25 42 33 15 20 47 30 11 19 12 80 0\n82 -41 0 81 70 68 0\n83 -40 0 82 63 0\n84 -38 0 82 64 0\n85 -29 0 83 62 0\n86 34 0 84 78 0\n87 -21 0 85 43 0\n88 26 0 86 49 0\n89 -31 0 86 73 55 0\n90 -16 0 87 28 0\n91 17 0 88 90 36 0\n92 -24 0 89 45 0\n93 10 0 91 23 0\n94 0 93 92 32 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "7c5caaa1e9561da8e5386e1783e5c6a99a4791d68d534cd1b45d0f6a358d538cd331cd4b2ac6b16c3ba1d8751c6725c570de0f43c4f0bc1f5528a8a916239511c6898a469515151548d1368388d130ce0b22c2b41c8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da69a6db49249249a6924d26924d2492489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 37), (facetIndex 41), (facetIndex 54), (facetIndex 64)]))
 (.leaf ([(facetIndex 28), (facetIndex 32), (facetIndex 35), (facetIndex 40), (facetIndex 43), (facetIndex 46), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 48), (facetIndex 58), (facetIndex 68)]))
 (.leaf ([(facetIndex 51), (facetIndex 56), (facetIndex 57)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 50), (facetIndex 55), (facetIndex 59)]))
 (.leaf ([(facetIndex 29), (facetIndex 52), (facetIndex 53)])))
 (.branch 7
 (.leaf ([(facetIndex 26), (facetIndex 27), (facetIndex 31), (facetIndex 33), (facetIndex 36)]))
 (.leaf ([(facetIndex 38), (facetIndex 44), (facetIndex 45)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "204000089b82d70207f2011c6231c29d8z13;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 39), (facetIndex 49)]))
 (.leaf ([(facetIndex 60), (facetIndex 61), (facetIndex 62)])))
 (.branch 3
 (.leaf ([(facetIndex 65), (facetIndex 67), (facetIndex 70)]))
 (.branch 4
 (.leaf ([(facetIndex 42), (facetIndex 47)]))
 (.leaf ([(facetIndex 63), (facetIndex 69)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "a04108490000000006000cz1f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [2]
def grouped3_0020 : List Nat := [2, 3, 4]
def grouped3_0021 : List Nat := [3]
def grouped3_0022 : List Nat := [3, 4]
def grouped3_0023 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005_matrix_checked

def leafCount : Nat := 1
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 8), (facetIndex 10), (facetIndex 21), (facetIndex 36), (facetIndex 45), (facetIndex 53), (facetIndex 54), (facetIndex 57), (facetIndex 59), (facetIndex 60), (facetIndex 66), (facetIndex 68), (facetIndex 70)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.leaf (leaf0000))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record005" 74

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record005" "{\"ridges\":[[15,321],[20,321],[25,324],[25,336],[26,21],[28,76],[31,21],[33,21],[35,321],[36,134],[42,330],[43,50],[45,49],[46,321],[47,354],[49,49],[51,76],[51,104],[56,104],[57,104],[59,49],[63,330],[66,84],[66,274],[66,324],[66,336],[67,90],[68,642],[69,354],[70,60]],\"owners\":[[26,21,[13,14,55],[1,31,33,49,50]],[31,21,[13,14,50],[1,26,33,49,55]],[33,21,[13,14,49,50,55],[1,26,31]],[36,134,[21,64],[2,33,37]],[43,50,[60],[7,31,38,44,45,65,67,69]],[66,274,[8,44],[22,46,69]],[68,642,[10,37],[24,48,64]],[28,76,[70],[11,50,51,52,53,61,62,63]],[51,76,[61,63],[11,28,50,52,53,62,70]],[66,84,[13,50,55,70],[25,32,61,65]],[15,321,[20,42,46,47,59],[35,53]],[20,321,[15,35,42,47,53],[46,59]],[35,321,[20,59],[15,42,46,47,53]],[46,321,[15,53],[20,35,42,47,59]],[25,324,[15,35,53,63],[66]],[66,324,[15,53],[25,35,63]],[51,104,[67],[16,40,56,57,62,70]],[56,104,[62],[16,40,51,57,67,70]],[57,104,[62,67,70],[16,40,51,56]],[25,336,[20,46,59,69],[66]],[66,336,[20,59],[25,46,69]],[67,90,[39,61],[]],[42,330,[63],[]],[63,330,[42],[]],[47,354,[69],[]],[69,354,[47],[]],[70,60,[49,60],[]]],\"edges\":[[40,[15,20,25,35,42,46,47,53,59,63,66,69]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-12,-9],[-12,-10],[-14,-12],[-16,-12],[-17,-4],[-17,-9],[-17,-12],[-17,-16],[-18,-12],[-18,-17],[-19,-18],[-27,-14],[-30,-27],[-31,-20],[-32,-5],[-32,-17],[-34,-9],[-34,-10],[-34,-11],[-34,-13],[-34,-33],[-35,-11],[-35,-17],[-35,-32],[-35,-33],[-36,-34],[-37,-6],[-37,-28],[-37,-35],[-39,-10],[-39,-20],[-39,-22],[-39,-23],[-39,-31],[-40,-39],[-41,-3],[-41,-15],[-41,-25],[-41,-26],[-41,-28],[-41,-32],[-41,-37],[-41,-38],[-47,-4],[-47,-43],[-47,-44],[-48,-15],[-48,-17],[-48,-28],[-48,-47],[-49,-13],[-49,-46],[-9,3,4,37],[-14,3,4,32],[-16,3,4,31,32,37],[-18,7,46],[-27,-31,-41],[-25,42],[-47,1,26],[-49,2,19],[-11,51],[-33,43,45],[-47,3,32,37,51],[-5,6,24,28,29,41],[-6,5,17,24,29,35],[-17,6,41],[-28,5,35],[-8,5,17,35,45],[-47,5,35],[-33,48],[-38,44],[-39,44,48,51],[-8,6,28,41,50],[-47,6,41],[-48,21,43],[-24,45],[-45,24],[-29,50],[-50,29],[-51,31,42],[-52,13,19,23,36,46],[-53,11,15,17,22,25,28,47],[-54,30,40,49],[-55,33,38,39],[-56,32,37,41],[-57,12,34,35],[-58,9,10,14,16,18],[-59,20,26,27],[-60,52],[-60,53],[-61,54],[-61,55],[-62,60],[-62,61],[-63,56],[-63,57],[-64,58],[-64,59],[-65,63],[-65,64],[-66,62],[-66,65],[66],[-21,67],[-31,67],[-68,42,43,44],[-42,68],[-43,68],[-44,68],[-24,69],[-29,69],[-70,45,50],[-45,70],[-50,70],[-68,71],[-67,71],[-69,-70,72],[-72,73],[-71,-73,74],[-74],[-1,-2,-7,-18,-27,-35,-36,-39,-41,-42,-47,-49,-51],[5,6,8,17,24,28,29,35,41,45,47,50]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":29,\"b\":26},{\"tag\":\"incompatible\",\"a\":29,\"b\":27},{\"tag\":\"incompatible\",\"a\":31,\"b\":29},{\"tag\":\"incompatible\",\"a\":33,\"b\":29},{\"tag\":\"incompatible\",\"a\":35,\"b\":14},{\"tag\":\"incompatible\",\"a\":35,\"b\":26},{\"tag\":\"incompatible\",\"a\":35,\"b\":29},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":36,\"b\":29},{\"tag\":\"incompatible\",\"a\":36,\"b\":35},{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":45,\"b\":31},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":38},{\"tag\":\"incompatible\",\"a\":50,\"b\":15},{\"tag\":\"incompatible\",\"a\":50,\"b\":35},{\"tag\":\"incompatible\",\"a\":52,\"b\":26},{\"tag\":\"incompatible\",\"a\":52,\"b\":27},{\"tag\":\"incompatible\",\"a\":52,\"b\":28},{\"tag\":\"incompatible\",\"a\":52,\"b\":30},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":28},{\"tag\":\"incompatible\",\"a\":53,\"b\":35},{\"tag\":\"incompatible\",\"a\":53,\"b\":50},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":55,\"b\":20},{\"tag\":\"incompatible\",\"a\":55,\"b\":46},{\"tag\":\"incompatible\",\"a\":55,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":27},{\"tag\":\"incompatible\",\"a\":57,\"b\":38},{\"tag\":\"incompatible\",\"a\":57,\"b\":40},{\"tag\":\"incompatible\",\"a\":57,\"b\":41},{\"tag\":\"incompatible\",\"a\":57,\"b\":49},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":13},{\"tag\":\"incompatible\",\"a\":59,\"b\":32},{\"tag\":\"incompatible\",\"a\":59,\"b\":43},{\"tag\":\"incompatible\",\"a\":59,\"b\":44},{\"tag\":\"incompatible\",\"a\":59,\"b\":46},{\"tag\":\"incompatible\",\"a\":59,\"b\":50},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":14},{\"tag\":\"incompatible\",\"a\":66,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":67,\"b\":32},{\"tag\":\"incompatible\",\"a\":67,\"b\":35},{\"tag\":\"incompatible\",\"a\":67,\"b\":46},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":30},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"mate\",\"ridge\":21,\"a\":26,\"owners\":[13,14,55]},{\"tag\":\"mate\",\"ridge\":21,\"a\":31,\"owners\":[13,14,50]},{\"tag\":\"mate\",\"ridge\":21,\"a\":33,\"owners\":[13,14,49,50,55]},{\"tag\":\"mate\",\"ridge\":134,\"a\":36,\"owners\":[21,64]},{\"tag\":\"three\",\"ridge\":49,\"vertices\":[45,49,59]},{\"tag\":\"mate\",\"ridge\":50,\"a\":43,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":274,\"a\":66,\"owners\":[8,44]},{\"tag\":\"mate\",\"ridge\":642,\"a\":68,\"owners\":[10,37]},{\"tag\":\"mate\",\"ridge\":76,\"a\":28,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":76,\"a\":51,\"owners\":[61,63]},{\"tag\":\"mate\",\"ridge\":84,\"a\":66,\"owners\":[13,50,55,70]},{\"tag\":\"mate\",\"ridge\":321,\"a\":15,\"owners\":[20,42,46,47,59]},{\"tag\":\"mate\",\"ridge\":321,\"a\":20,\"owners\":[15,35,42,47,53]},{\"tag\":\"mate\",\"ridge\":321,\"a\":35,\"owners\":[20,59]},{\"tag\":\"mate\",\"ridge\":321,\"a\":46,\"owners\":[15,53]},{\"tag\":\"mate\",\"ridge\":324,\"a\":25,\"owners\":[15,35,53,63]},{\"tag\":\"mate\",\"ridge\":324,\"a\":66,\"owners\":[15,53]},{\"tag\":\"mate\",\"ridge\":104,\"a\":51,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":104,\"a\":56,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":104,\"a\":57,\"owners\":[62,67,70]},{\"tag\":\"mate\",\"ridge\":336,\"a\":25,\"owners\":[20,46,59,69]},{\"tag\":\"mate\",\"ridge\":336,\"a\":66,\"owners\":[20,59]},{\"tag\":\"mate\",\"ridge\":90,\"a\":67,\"owners\":[39,61]},{\"tag\":\"mate\",\"ridge\":330,\"a\":42,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":330,\"a\":63,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":354,\"a\":47,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":354,\"a\":69,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":60,\"a\":70,\"owners\":[49,60]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[30,37,41,54,64],\"full_literals\":[-52,13,19,23,36,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[28,32,35,40,43,46,66],\"full_literals\":[-53,11,15,17,22,25,28,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[48,58,68],\"full_literals\":[-54,30,40,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[51,56,57],\"full_literals\":[-55,33,38,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[50,55,59],\"full_literals\":[-56,32,37,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[29,52,53],\"full_literals\":[-57,12,34,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[26,27,31,33,36],\"full_literals\":[-58,9,10,14,16,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[38,44,45],\"full_literals\":[-59,20,26,27]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-62,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-66,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-66,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":39,\"full_literals\":[-21,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-31,67]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[60,61,62],\"full_literals\":[-68,42,43,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":60,\"full_literals\":[-42,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":61,\"full_literals\":[-43,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":62,\"full_literals\":[-44,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":42,\"full_literals\":[-24,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":47,\"full_literals\":[-29,69]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[63,69],\"full_literals\":[-70,45,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":63,\"full_literals\":[-45,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":69,\"full_literals\":[-50,70]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-69,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-71,-73,74],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[8,10,21,36,45,53,54,57,59,60,66,68,70]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[15,20,25,35,42,46,47,53,59,63,66,69]}]}"
  "p cnf 74 122\n-12 -9 0\n-12 -10 0\n-14 -12 0\n-16 -12 0\n-17 -4 0\n-17 -9 0\n-17 -12 0\n-17 -16 0\n-18 -12 0\n-18 -17 0\n-19 -18 0\n-27 -14 0\n-30 -27 0\n-31 -20 0\n-32 -5 0\n-32 -17 0\n-34 -9 0\n-34 -10 0\n-34 -11 0\n-34 -13 0\n-34 -33 0\n-35 -11 0\n-35 -17 0\n-35 -32 0\n-35 -33 0\n-36 -34 0\n-37 -6 0\n-37 -28 0\n-37 -35 0\n-39 -10 0\n-39 -20 0\n-39 -22 0\n-39 -23 0\n-39 -31 0\n-40 -39 0\n-41 -3 0\n-41 -15 0\n-41 -25 0\n-41 -26 0\n-41 -28 0\n-41 -32 0\n-41 -37 0\n-41 -38 0\n-47 -4 0\n-47 -43 0\n-47 -44 0\n-48 -15 0\n-48 -17 0\n-48 -28 0\n-48 -47 0\n-49 -13 0\n-49 -46 0\n-9 3 4 37 0\n-14 3 4 32 0\n-16 3 4 31 32 37 0\n-18 7 46 0\n-27 -31 -41 0\n-25 42 0\n-47 1 26 0\n-49 2 19 0\n-11 51 0\n-33 43 45 0\n-47 3 32 37 51 0\n-5 6 24 28 29 41 0\n-6 5 17 24 29 35 0\n-17 6 41 0\n-28 5 35 0\n-8 5 17 35 45 0\n-47 5 35 0\n-33 48 0\n-38 44 0\n-39 44 48 51 0\n-8 6 28 41 50 0\n-47 6 41 0\n-48 21 43 0\n-24 45 0\n-45 24 0\n-29 50 0\n-50 29 0\n-51 31 42 0\n-52 13 19 23 36 46 0\n-53 11 15 17 22 25 28 47 0\n-54 30 40 49 0\n-55 33 38 39 0\n-56 32 37 41 0\n-57 12 34 35 0\n-58 9 10 14 16 18 0\n-59 20 26 27 0\n-60 52 0\n-60 53 0\n-61 54 0\n-61 55 0\n-62 60 0\n-62 61 0\n-63 56 0\n-63 57 0\n-64 58 0\n-64 59 0\n-65 63 0\n-65 64 0\n-66 62 0\n-66 65 0\n66 0\n-21 67 0\n-31 67 0\n-68 42 43 44 0\n-42 68 0\n-43 68 0\n-44 68 0\n-24 69 0\n-29 69 0\n-70 45 50 0\n-45 70 0\n-50 70 0\n-68 71 0\n-67 71 0\n-69 -70 72 0\n-72 73 0\n-71 -73 74 0\n-74 0\n-1 -2 -7 -18 -27 -35 -36 -39 -41 -42 -47 -49 -51 0\n5 6 8 17 24 28 29 35 41 45 47 50 0\n"
  "123 62 0 103 101 0\n124 65 0 103 102 0\n125 60 0 123 93 0\n126 61 0 123 94 0\n127 63 0 124 99 0\n128 64 0 124 100 0\n129 52 0 125 89 0\n130 53 0 125 90 0\n131 54 0 126 91 0\n132 55 0 126 92 0\n133 56 0 127 95 0\n134 57 0 127 96 0\n135 58 0 128 97 0\n136 59 0 128 98 0\n137 71 0 132 115 116 107 108 109 104 105 75 71 80 70 72 84 0\n138 -73 0 137 120 119 0\n139 -72 0 138 118 0\n140 -70 0 139 117 110 111 77 79 112 0\n141 -45 0 140 113 0\n142 -50 0 140 114 0\n143 -24 0 141 76 0\n144 -29 0 142 78 0\n145 68 0 141 132 130 107 108 109 58 62 71 84 32 34 80 61 72 47 48 49 50 82 0\n146 -35 41 0 133 24 29 85 0\n147 -37 41 0 142 141 144 143 146 27 28 64 66 74 73 122 0\n148 41 0 133 142 141 144 143 146 147 85 15 16 69 67 65 68 122 0\n149 -3 0 148 36 0\n150 -15 0 148 37 0\n151 -25 0 148 38 0\n152 -26 0 148 39 0\n153 -28 0 148 40 0\n154 -32 0 148 41 0\n155 -37 0 148 42 0\n156 -38 0 148 43 0\n157 -17 35 0 154 149 134 135 5 6 7 8 10 54 86 87 18 0\n158 -34 17 31 0 156 132 152 136 151 150 153 130 131 154 155 149 135 129 17 18 19 20 21 26 84 31 32 33 35 88 82 12 13 44 83 55 52 87 81 11 0\n159 -12 0 135 1 2 3 4 9 87 0\n160 35 31 0 159 134 157 86 158 0\n161 31 0 156 132 136 151 150 153 130 152 131 154 155 149 145 135 129 148 160 22 23 25 84 30 31 32 33 35 88 82 12 13 44 45 46 59 63 83 53 55 106 51 52 87 11 56 60 81 121 0\n162 -20 0 161 14 0\n163 -27 0 161 148 57 0\n164 0 163 162 136 152 88 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005.l) :=
(.leaf (⟨0, by decide⟩))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005.g)) :=
(.leaf ([]))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ab2aa5a95a1eaa655876a3a2e2b89e0faa95a5591e6a5995551d68d8b4ad8749d0f6a358c73a2d8b52e2b4acab1ac9b16c3ba1d4731e2729d1725c3783c8f0bc1f5491a19856546898a519a16251945550c6344c5342c8b0ac1b21c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6da6d26db69a6924936db492492492492492692249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 37), (facetIndex 43), (facetIndex 60), (facetIndex 72)]))
 (.leaf ([(facetIndex 32), (facetIndex 53), (facetIndex 57), (facetIndex 58)])))
 (.branch 3
 (.leaf ([(facetIndex 45), (facetIndex 54), (facetIndex 62)]))
 (.leaf ([(facetIndex 34), (facetIndex 46), (facetIndex 68), (facetIndex 69)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 25), (facetIndex 39), (facetIndex 41), (facetIndex 47)]))
 (.leaf ([(facetIndex 26), (facetIndex 28), (facetIndex 29), (facetIndex 31), (facetIndex 33), (facetIndex 35)])))
 (.branch 7
 (.leaf ([(facetIndex 36), (facetIndex 38), (facetIndex 40), (facetIndex 42), (facetIndex 44)]))
 (.branch 8
 (.leaf ([(facetIndex 55), (facetIndex 56)]))
 (.leaf ([(facetIndex 24)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3300000200011772100000432606464606535150550548z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 59), (facetIndex 61)]))
 (.branch 2
 (.leaf ([(facetIndex 71), (facetIndex 73)]))
 (.leaf ([(facetIndex 27), (facetIndex 48), (facetIndex 52)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 65), (facetIndex 66), (facetIndex 70)]))
 (.leaf ([(facetIndex 67), (facetIndex 74), (facetIndex 75)])))
 (.branch 6
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 51)]))
 (.leaf ([(facetIndex 63), (facetIndex 64)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9082c08dec00000002b6a0000000000000004z14;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1, 2]
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [1, 2]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [3]
def grouped3_0024 : List Nat := [3, 4]
def grouped3_0025 : List Nat := [3, 4, 5, 6]
def grouped3_0026 : List Nat := [4]
def grouped3_0027 : List Nat := [5]
def grouped3_0028 : List Nat := [5, 6]
def grouped3_0029 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record008" 79

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record008" "{\"ridges\":[[16,25],[17,552],[18,648],[26,138],[32,548],[33,69],[35,644],[42,552],[44,265],[45,648],[49,60],[50,156],[51,540],[53,552],[54,644],[54,648],[56,69],[57,69],[62,552],[62,648],[65,172],[66,526],[70,674]],\"owners\":[[16,25,[4,24,36,37,38,49,50,51,59],[60]],[26,138,[74],[6,38,40,44,45,64,65,67]],[44,265,[16,60,61],[7,41,43]],[32,548,[75],[14,53,57,58,66,70]],[35,644,[75],[15,54,58,67,70]],[54,644,[70],[15,35,58,67,75]],[17,552,[66,74,75],[42,53,62]],[42,552,[75],[17,53,62,66,74]],[53,552,[74],[17,42,62,66,75]],[62,552,[66],[17,42,53,74,75]],[18,648,[67,74,75],[45,54,62]],[45,648,[75],[18,54,62,67,74]],[54,648,[74],[18,45,62,67,75]],[62,648,[67],[18,45,54,74,75]],[66,526,[27,67],[]],[70,674,[48,74],[]],[49,60,[63],[]],[50,156,[64],[]],[51,540,[],[]],[65,172,[52,75],[]]],\"edges\":[[29,[17,18,27,42,45,51,53,54,62,66,67,74,75]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-6,-5],[-8,-5],[-9,-5],[-10,-5],[-12,-5],[-17,-9],[-20,-1],[-21,-15],[-21,-17],[-21,-19],[-21,-20],[-29,-5],[-29,-6],[-29,-28],[-31,-13],[-31,-16],[-31,-22],[-32,-8],[-32,-30],[-35,-31],[-37,-10],[-37,-18],[-37,-33],[-42,-5],[-43,-15],[-44,-31],[-46,-10],[-46,-18],[-46,-33],[-46,-37],[-47,-5],[-47,-18],[-47,-29],[-47,-37],[-12,-31,-32],[-2,1,5,15,16,17,24,25,26,34],[-6,46],[-20,2,35,36],[-11,47],[-14,47],[-29,45],[-3,41,46,47],[-19,47],[-28,46],[-37,41],[-4,42,46,47],[-21,47],[-29,46],[-37,42],[-41,7,42],[-45,23,46],[-24,38],[-25,39],[-26],[-40,27,47],[-48,11,28,32,33],[-49,21,29,37],[-50,13,22,43,44],[-51,6,8,9,10,12,14],[-52,15,17,18,19,20],[-53,30,31],[-54,5],[-55,48],[-56,49],[-56,50],[-57,55],[-57,56],[-58,51],[-59,53,54],[-60,54],[-61,52,60],[-61,59],[-62,60],[-63,58,62],[-64,58],[-63,61],[-64,62],[-65,57,64],[-65,63],[65],[-34,66],[-36,66],[-7,67],[-23,67],[-27,67],[-68,40,41,45],[-41,68],[-45,68],[-69,42,46,47],[-42,69],[-46,69],[-47,69],[-70,24,25,26],[-24,70],[-25,70],[-38,71],[-39,71],[-67,72],[-72,73],[-66,73],[-74,68,69],[-69,74],[-68,74],[-68,-69,75],[-70,-71,76],[-74,-76,78],[-75,77],[-78,79],[-73,-77,79],[-79],[3,4,7,19,21,26,28,29,37,41,42,46,47]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":26,\"b\":24},{\"tag\":\"incompatible\",\"a\":28,\"b\":24},{\"tag\":\"incompatible\",\"a\":29,\"b\":24},{\"tag\":\"incompatible\",\"a\":31,\"b\":24},{\"tag\":\"incompatible\",\"a\":33,\"b\":24},{\"tag\":\"incompatible\",\"a\":38,\"b\":29},{\"tag\":\"incompatible\",\"a\":44,\"b\":4},{\"tag\":\"incompatible\",\"a\":45,\"b\":36},{\"tag\":\"incompatible\",\"a\":45,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":42},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":54,\"b\":24},{\"tag\":\"incompatible\",\"a\":54,\"b\":26},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":34},{\"tag\":\"incompatible\",\"a\":56,\"b\":37},{\"tag\":\"incompatible\",\"a\":56,\"b\":46},{\"tag\":\"incompatible\",\"a\":57,\"b\":28},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":60,\"b\":56},{\"tag\":\"incompatible\",\"a\":62,\"b\":31},{\"tag\":\"incompatible\",\"a\":62,\"b\":40},{\"tag\":\"incompatible\",\"a\":62,\"b\":58},{\"tag\":\"incompatible\",\"a\":67,\"b\":24},{\"tag\":\"incompatible\",\"a\":68,\"b\":36},{\"tag\":\"incompatible\",\"a\":69,\"b\":56},{\"tag\":\"incompatible\",\"a\":74,\"b\":31},{\"tag\":\"incompatible\",\"a\":74,\"b\":40},{\"tag\":\"incompatible\",\"a\":74,\"b\":58},{\"tag\":\"incompatible\",\"a\":74,\"b\":62},{\"tag\":\"incompatible\",\"a\":75,\"b\":24},{\"tag\":\"incompatible\",\"a\":75,\"b\":40},{\"tag\":\"incompatible\",\"a\":75,\"b\":54},{\"tag\":\"incompatible\",\"a\":75,\"b\":62},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[33,56,57]},{\"tag\":\"mate\",\"ridge\":25,\"a\":16,\"owners\":[4,24,36,37,38,49,50,51,59]},{\"tag\":\"mate\",\"ridge\":138,\"a\":26,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":265,\"a\":44,\"owners\":[16,60,61]},{\"tag\":\"mate\",\"ridge\":548,\"a\":32,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":644,\"a\":35,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":644,\"a\":54,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":552,\"a\":17,\"owners\":[66,74,75]},{\"tag\":\"mate\",\"ridge\":552,\"a\":42,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":552,\"a\":53,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":552,\"a\":62,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":648,\"a\":18,\"owners\":[67,74,75]},{\"tag\":\"mate\",\"ridge\":648,\"a\":45,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":648,\"a\":54,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":648,\"a\":62,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":526,\"a\":66,\"owners\":[27,67]},{\"tag\":\"mate\",\"ridge\":674,\"a\":70,\"owners\":[48,74]},{\"tag\":\"mate\",\"ridge\":60,\"a\":49,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":156,\"a\":50,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":540,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":172,\"a\":65,\"owners\":[52,75]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[32,53,57,58],\"full_literals\":[-48,11,28,32,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[45,54,62],\"full_literals\":[-49,21,29,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[34,46,68,69],\"full_literals\":[-50,13,22,43,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[26,28,29,31,33,35],\"full_literals\":[-51,6,8,9,10,12,14]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[36,38,40,42,44],\"full_literals\":[-52,15,17,18,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[55,56],\"full_literals\":[-53,30,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[24],\"full_literals\":[-54,5]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-57,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,53,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,52,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-63,58,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-64,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-64,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-65,57,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-65,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":59,\"full_literals\":[-34,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":61,\"full_literals\":[-36,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":27,\"full_literals\":[-7,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":48,\"full_literals\":[-23,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":52,\"full_literals\":[-27,67]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[65,66,70],\"full_literals\":[-68,40,41,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":66,\"full_literals\":[-41,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":70,\"full_literals\":[-45,68]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[67,74,75],\"full_literals\":[-69,42,46,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":67,\"full_literals\":[-42,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-46,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":75,\"full_literals\":[-47,69]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[49,50,51],\"full_literals\":[-70,24,25,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":49,\"full_literals\":[-24,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":50,\"full_literals\":[-25,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":63,\"full_literals\":[-38,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":64,\"full_literals\":[-39,71]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-69,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-70,-71,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-74,-76,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-78,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-73,-77,79],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[17,18,27,42,45,51,53,54,62,66,67,74,75]}]}"
  "p cnf 79 111\n-6 -5 0\n-8 -5 0\n-9 -5 0\n-10 -5 0\n-12 -5 0\n-17 -9 0\n-20 -1 0\n-21 -15 0\n-21 -17 0\n-21 -19 0\n-21 -20 0\n-29 -5 0\n-29 -6 0\n-29 -28 0\n-31 -13 0\n-31 -16 0\n-31 -22 0\n-32 -8 0\n-32 -30 0\n-35 -31 0\n-37 -10 0\n-37 -18 0\n-37 -33 0\n-42 -5 0\n-43 -15 0\n-44 -31 0\n-46 -10 0\n-46 -18 0\n-46 -33 0\n-46 -37 0\n-47 -5 0\n-47 -18 0\n-47 -29 0\n-47 -37 0\n-12 -31 -32 0\n-2 1 5 15 16 17 24 25 26 34 0\n-6 46 0\n-20 2 35 36 0\n-11 47 0\n-14 47 0\n-29 45 0\n-3 41 46 47 0\n-19 47 0\n-28 46 0\n-37 41 0\n-4 42 46 47 0\n-21 47 0\n-29 46 0\n-37 42 0\n-41 7 42 0\n-45 23 46 0\n-24 38 0\n-25 39 0\n-26 0\n-40 27 47 0\n-48 11 28 32 33 0\n-49 21 29 37 0\n-50 13 22 43 44 0\n-51 6 8 9 10 12 14 0\n-52 15 17 18 19 20 0\n-53 30 31 0\n-54 5 0\n-55 48 0\n-56 49 0\n-56 50 0\n-57 55 0\n-57 56 0\n-58 51 0\n-59 53 54 0\n-60 54 0\n-61 52 60 0\n-61 59 0\n-62 60 0\n-63 58 62 0\n-64 58 0\n-63 61 0\n-64 62 0\n-65 57 64 0\n-65 63 0\n65 0\n-34 66 0\n-36 66 0\n-7 67 0\n-23 67 0\n-27 67 0\n-68 40 41 45 0\n-41 68 0\n-45 68 0\n-69 42 46 47 0\n-42 69 0\n-46 69 0\n-47 69 0\n-70 24 25 26 0\n-24 70 0\n-25 70 0\n-38 71 0\n-39 71 0\n-67 72 0\n-72 73 0\n-66 73 0\n-74 68 69 0\n-69 74 0\n-68 74 0\n-68 -69 75 0\n-70 -71 76 0\n-74 -76 78 0\n-75 77 0\n-78 79 0\n-73 -77 79 0\n-79 0\n3 4 7 19 21 26 28 29 37 41 42 46 47 0\n"
  "112 63 0 80 79 0\n113 61 0 112 76 0\n114 59 0 113 72 0\n115 -70 24 25 0 54 93 0\n116 -78 0 110 108 0\n117 3 4 7 19 21 28 29 37 41 42 46 47 0 54 111 0\n118 74 7 0 102 103 90 91 92 87 46 49 44 48 43 47 42 117 0\n119 69 67 0 83 118 85 84 90 91 92 101 50 51 55 86 0\n120 46 47 70 73 0 114 113 112 80 54 47 43 40 39 95 94 99 98 119 100 82 81 37 44 48 89 24 62 70 69 73 71 77 74 78 68 66 67 63 64 65 57 21 22 23 56 18 19 61 15 16 17 20 26 35 58 59 25 6 60 7 38 36 0\n121 -64 10 14 0 75 77 68 73 70 62 1 2 3 5 59 0\n122 47 70 73 0 80 114 113 112 54 95 94 100 82 81 39 40 43 47 120 27 28 29 30 121 78 66 67 63 64 65 57 12 13 14 62 56 70 69 18 19 73 71 61 74 15 16 17 20 26 35 68 58 59 25 6 60 7 38 36 0\n123 -47 0 113 80 31 32 33 34 62 70 73 71 77 78 67 64 57 8 9 10 11 60 0\n124 -14 0 123 40 0\n125 -21 0 123 47 0\n126 -70 76 0 105 96 97 52 53 115 0\n127 73 0 116 123 99 98 83 118 106 122 126 0\n128 -77 0 127 110 109 0\n129 -75 0 128 107 0\n130 -37 0 129 45 49 87 90 104 0\n131 -64 0 124 77 121 73 4 70 62 0\n132 57 0 131 80 78 0\n133 56 0 132 67 0\n134 49 0 133 64 0\n135 29 0 134 130 125 57 0\n136 45 0 135 41 0\n137 46 0 135 48 0\n138 68 0 136 88 0\n139 69 0 137 91 0\n140 0 138 139 129 104 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record022
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2aca693a599564da8e2ba1e1783eaa6994e6a55965555535a362d2b45d0f5a358e934ce8b4ae1b46c9b16c3ba1d4749ca719e1745c3783c8f13e1c548aa1582e07951a24a9866151560d0b41d50d2328d1314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36da6d24926da4d24924d249249a492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 50), (facetIndex 55), (facetIndex 56)]))
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 52), (facetIndex 53), (facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 28), (facetIndex 34), (facetIndex 38), (facetIndex 43), (facetIndex 51), (facetIndex 65)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 33), (facetIndex 47), (facetIndex 48)]))
 (.leaf ([(facetIndex 29), (facetIndex 42), (facetIndex 44), (facetIndex 64)])))
 (.branch 7
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 41)]))
 (.branch 8
 (.leaf ([(facetIndex 27), (facetIndex 30), (facetIndex 62), (facetIndex 63)]))
 (.leaf ([(facetIndex 45), (facetIndex 49)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "100357722000000223084408535666301134007537z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 46)]))
 (.leaf ([(facetIndex 54), (facetIndex 57)])))
 (.branch 3
 (.leaf ([(facetIndex 58), (facetIndex 66)]))
 (.leaf ([(facetIndex 59), (facetIndex 67)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 69)]))
 (.leaf ([(facetIndex 70)])))
 (.branch 7
 (.leaf ([(facetIndex 71)]))
 (.leaf ([(facetIndex 72)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "7d6068000068804z28;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1]
def grouped3_0009 : List Nat := [0, 1, 2, 3]
def grouped3_0011 : List Nat := [1]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [2, 3]
def grouped3_0014 : List Nat := [3]
def grouped3_0015 : List Nat := [4]
def grouped3_0016 : List Nat := [4, 5]
def grouped3_0017 : List Nat := [4, 5, 6, 7]
def grouped3_0018 : List Nat := [5]
def grouped3_0019 : List Nat := [6]
def grouped3_0020 : List Nat := [6, 7]
def grouped3_0021 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record022" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record022" 52

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record022" "{\"ridges\":[[10,289],[10,290],[19,648],[35,289],[35,290],[37,646],[43,289],[43,290],[44,648],[45,289],[45,290],[46,658],[47,289],[47,290],[48,289],[48,290],[53,648],[54,308],[57,356],[58,676],[59,312],[60,648],[61,648],[66,646],[67,308],[69,356],[70,312]],\"owners\":[[10,289,[54,57,59],[35,43,45,47,48]],[35,289,[59],[10,43,45,47,48,54,57]],[43,289,[54,57],[10,35,45,47,48,59]],[45,289,[57],[10,35,43,47,48,54,59]],[47,289,[54,59],[10,35,43,45,48,57]],[48,289,[54,57,59],[10,35,43,45,47]],[10,290,[67,69,70],[35,43,45,47,48]],[35,290,[70],[10,43,45,47,48,67,69]],[43,290,[67,69],[10,35,45,47,48,70]],[45,290,[69],[10,35,43,47,48,67,70]],[47,290,[67,70],[10,35,43,45,48,69]],[48,290,[67,69,70],[10,35,43,45,47]],[19,648,[66,71,72],[44,53,60,61]],[44,648,[72],[19,53,60,61,66,71]],[53,648,[71],[19,44,60,61,66,72]],[60,648,[66,72],[19,44,53,61,71]],[61,648,[66,71],[19,44,53,60,72]],[37,646,[66],[]],[66,646,[37],[]],[46,658,[71],[]],[54,308,[67],[]],[67,308,[54],[]],[57,356,[69],[]],[69,356,[57],[]],[58,676,[72],[]],[59,312,[70],[]],[70,312,[59],[]]],\"edges\":[[37,[10,35,43,45,47,48,54,57,59,67,69,70]],[43,[19,37,44,46,53,58,60,61,66,71,72]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record022" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record022\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-16,-4],[-16,-14],[-18,-16],[-25,-3],[-25,-6],[-25,-17],[-26,-25],[-1,16,19,21],[-5,21],[-8,16,19],[-10,19],[-12,16,21],[-13,16,19,21],[-1,25,27,28],[-5,28],[-8,25,27],[-10,27],[-12,25,28],[-13,25,27,28],[-2,24,29,30],[-9,30],[-15,29],[-22,24,30],[-23,24,29],[-7,24],[-24,7],[-11,29],[-16,25],[-25,16],[-19,27],[-27,19],[-20,30],[-21,28],[-28,21],[-31,3,4,14,17,18],[-32,5,6,26],[-33,31,32],[-34,33],[-35,34],[35],[-7,36],[-16,37],[-19,37],[-24,38],[-21,39],[-25,39],[-27,40],[-28,41],[-29,42],[-30,43],[-37,44],[-36,44],[-39,45],[-38,45],[-45,46],[-44,46],[-44,-45,47],[-41,48],[-40,48],[-43,49],[-42,49],[-48,50],[-48,-49,51],[-46,-51,52],[-47,-50,52],[-52],[1,5,8,10,12,13,16,19,21,25,27,28],[2,7,9,11,15,20,22,23,24,29,30]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":54,\"b\":32},{\"tag\":\"incompatible\",\"a\":54,\"b\":50},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":67,\"b\":31},{\"tag\":\"incompatible\",\"a\":67,\"b\":36},{\"tag\":\"incompatible\",\"a\":67,\"b\":55},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"mate\",\"ridge\":289,\"a\":10,\"owners\":[54,57,59]},{\"tag\":\"mate\",\"ridge\":289,\"a\":35,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":289,\"a\":43,\"owners\":[54,57]},{\"tag\":\"mate\",\"ridge\":289,\"a\":45,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":289,\"a\":47,\"owners\":[54,59]},{\"tag\":\"mate\",\"ridge\":289,\"a\":48,\"owners\":[54,57,59]},{\"tag\":\"mate\",\"ridge\":290,\"a\":10,\"owners\":[67,69,70]},{\"tag\":\"mate\",\"ridge\":290,\"a\":35,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":290,\"a\":43,\"owners\":[67,69]},{\"tag\":\"mate\",\"ridge\":290,\"a\":45,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":290,\"a\":47,\"owners\":[67,70]},{\"tag\":\"mate\",\"ridge\":290,\"a\":48,\"owners\":[67,69,70]},{\"tag\":\"mate\",\"ridge\":648,\"a\":19,\"owners\":[66,71,72]},{\"tag\":\"mate\",\"ridge\":648,\"a\":44,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":648,\"a\":53,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":648,\"a\":60,\"owners\":[66,72]},{\"tag\":\"mate\",\"ridge\":648,\"a\":61,\"owners\":[66,71]},{\"tag\":\"mate\",\"ridge\":646,\"a\":37,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":646,\"a\":66,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":658,\"a\":46,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":308,\"a\":54,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":308,\"a\":67,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":356,\"a\":57,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":356,\"a\":69,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":676,\"a\":58,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":312,\"a\":59,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":312,\"a\":70,\"owners\":[59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[31,32,50,55,56],\"full_literals\":[-31,3,4,14,17,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[35,36,68],\"full_literals\":[-32,5,6,26]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-33,31,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-34,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-35,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":37,\"full_literals\":[-7,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":54,\"full_literals\":[-16,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":57,\"full_literals\":[-19,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-24,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":59,\"full_literals\":[-21,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-25,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":69,\"full_literals\":[-27,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":70,\"full_literals\":[-28,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":71,\"full_literals\":[-29,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":72,\"full_literals\":[-30,43]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-45,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-48,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-46,-51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-50,52],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[10,35,43,45,47,48,54,57,59,67,69,70]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[19,37,44,46,53,58,60,61,66,71,72]}]}"
  "p cnf 52 68\n-16 -4 0\n-16 -14 0\n-18 -16 0\n-25 -3 0\n-25 -6 0\n-25 -17 0\n-26 -25 0\n-1 16 19 21 0\n-5 21 0\n-8 16 19 0\n-10 19 0\n-12 16 21 0\n-13 16 19 21 0\n-1 25 27 28 0\n-5 28 0\n-8 25 27 0\n-10 27 0\n-12 25 28 0\n-13 25 27 28 0\n-2 24 29 30 0\n-9 30 0\n-15 29 0\n-22 24 30 0\n-23 24 29 0\n-7 24 0\n-24 7 0\n-11 29 0\n-16 25 0\n-25 16 0\n-19 27 0\n-27 19 0\n-20 30 0\n-21 28 0\n-28 21 0\n-31 3 4 14 17 18 0\n-32 5 6 26 0\n-33 31 32 0\n-34 33 0\n-35 34 0\n35 0\n-7 36 0\n-16 37 0\n-19 37 0\n-24 38 0\n-21 39 0\n-25 39 0\n-27 40 0\n-28 41 0\n-29 42 0\n-30 43 0\n-37 44 0\n-36 44 0\n-39 45 0\n-38 45 0\n-45 46 0\n-44 46 0\n-44 -45 47 0\n-41 48 0\n-40 48 0\n-43 49 0\n-42 49 0\n-48 50 0\n-48 -49 51 0\n-46 -51 52 0\n-47 -50 52 0\n-52 0\n1 5 8 10 12 13 16 19 21 25 27 28 0\n2 7 9 11 15 20 22 23 24 29 30 0\n"
  "69 34 0 40 39 0\n70 33 0 69 38 0\n71 46 0 55 56 53 51 45 46 42 43 9 34 12 13 8 11 31 10 67 0\n72 -51 0 71 66 64 0\n73 25 48 0 59 47 30 17 58 48 33 15 28 18 19 14 16 67 0\n74 48 0 70 58 48 15 73 4 5 6 7 29 36 1 2 3 37 35 0\n75 -49 0 74 72 63 0\n76 -43 0 75 60 0\n77 -42 0 75 61 0\n78 -30 0 76 50 0\n79 -29 0 77 49 0\n80 -9 0 78 21 0\n81 -20 0 78 32 0\n82 -15 0 79 22 0\n83 -11 0 79 27 0\n84 24 0 78 79 81 82 83 80 25 23 20 24 68 0\n85 7 0 84 26 0\n86 38 0 84 44 0\n87 36 0 85 41 0\n88 45 0 86 54 0\n89 44 0 87 52 0\n90 47 0 88 89 57 0\n91 50 0 74 62 0\n92 0 90 91 66 65 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record031
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "23c4ea96558b6a394e1ba1e4783ec66394e5558d4b5a364d5362d1b61d4743da4d9354d332ce8b4ac6b86d1b0ee8751cc729c6785d1715e0f43c8f07e94528960d84e0ba9152685854950d60d1342d50d1324c3342c4b0ac8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da69a4da6db49249269249349a492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 29), (facetIndex 37), (facetIndex 42), (facetIndex 55), (facetIndex 68)]))
 (.leaf ([(facetIndex 33), (facetIndex 58), (facetIndex 70), (facetIndex 72)])))
 (.branch 3
 (.leaf ([(facetIndex 40), (facetIndex 43), (facetIndex 46), (facetIndex 47)]))
 (.leaf ([(facetIndex 52), (facetIndex 54), (facetIndex 57), (facetIndex 59)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 27), (facetIndex 34), (facetIndex 64), (facetIndex 67)]))
 (.leaf ([(facetIndex 32), (facetIndex 45), (facetIndex 48), (facetIndex 49)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 30), (facetIndex 31), (facetIndex 35), (facetIndex 36), (facetIndex 38)]))
 (.branch 8
 (.leaf ([(facetIndex 50), (facetIndex 53), (facetIndex 56)]))
 (.leaf ([(facetIndex 39)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "1010040040000313703730755225020028606641566064z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 44)]))
 (.branch 2
 (.leaf ([(facetIndex 51), (facetIndex 60)]))
 (.leaf ([(facetIndex 66), (facetIndex 69)]))))
 (.branch 4
 (.leaf ([(facetIndex 65), (facetIndex 71)]))
 (.branch 5
 (.leaf ([(facetIndex 61), (facetIndex 62), (facetIndex 63)]))
 (.leaf ([(facetIndex 73), (facetIndex 74)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1686100989210000002z26;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7, 8]
def grouped2_0008 : List Nat := [7]
def grouped2_0009 : List Nat := [7, 8]
def grouped2_0010 : List Nat := [8]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1, 2]
def grouped3_0014 : List Nat := [1]
def grouped3_0015 : List Nat := [1, 2]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [3]
def grouped3_0018 : List Nat := [3, 4, 5]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record031" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record031" 50

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record031" "{\"ridges\":[[10,273],[10,274],[14,521],[14,524],[30,521],[32,273],[32,274],[40,273],[41,538],[44,650],[46,273],[47,273],[47,274],[48,273],[48,274],[52,521],[52,524],[54,521],[54,524],[56,521],[56,524],[57,521],[57,524],[62,568],[63,792],[65,284],[66,538],[69,650],[71,340],[74,568]],\"owners\":[[10,273,[51,60,61,63],[32,40,46,47,48]],[32,273,[61,63],[10,40,46,47,48,51,60]],[40,273,[60],[10,32,46,47,48,51,61,63]],[46,273,[51,60,63],[10,32,40,47,48,61]],[47,273,[51,61,63],[10,32,40,46,48,60]],[48,273,[51,60,61,63],[10,32,40,46,47]],[10,274,[65,71,73],[32,40,46,47,48]],[32,274,[73],[10,40,46,47,48,65,71]],[47,274,[65,73],[10,32,40,46,48,71]],[48,274,[65,71,73],[10,32,40,46,47]],[14,521,[41,44,62,63],[30,52,54,56,57]],[30,521,[62,63],[14,41,44,52,54,56,57]],[52,521,[44],[14,30,41,54,56,57,62,63]],[54,521,[41,44,63],[14,30,52,56,57,62]],[56,521,[41,44,62,63],[14,30,52,54,57]],[57,521,[41,62,63],[14,30,44,52,54,56]],[14,524,[66,69,74],[30,52,54,56,57]],[52,524,[69],[14,30,54,56,57,66,74]],[54,524,[66,69],[14,30,52,56,57,74]],[56,524,[66,69,74],[14,30,52,54,57]],[57,524,[66,74],[14,30,52,54,56,69]],[41,538,[66],[]],[66,538,[41],[]],[44,650,[69],[]],[69,650,[44],[]],[65,284,[51],[]],[71,340,[60],[]],[62,568,[74],[]],[74,568,[62],[]],[63,792,[],[]]],\"edges\":[[29,[14,30,41,44,52,54,56,57,62,63,66,69,74]],[33,[10,32,40,46,47,48,51,60,61,63,65,71,73]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record031" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record031\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-7],[-12,-7],[-21,-20],[-24,-5],[-24,-13],[-24,-20],[-27,-21],[-1,14,19,20,22],[-4,20,22],[-6,19],[-10,14,19,22],[-11,14,20,22],[-12,14,19,20,22],[-1,23,26,27],[-4,27],[-11,23,27],[-12,23,26,27],[-2,7,8,21,22],[-3,21,22],[-15,8],[-16,7,8,22],[-17,7,8,21,22],[-18,7,21,22],[-2,24,25,28],[-15,25],[-16,24,25],[-17,24,25,28],[-18,24,28],[-7,24],[-24,7],[-8,25],[-25,8],[-23,14],[-26,19],[-21,28],[-28,21],[-22],[-29,4,9,12,13],[-30,5],[-31,29],[-32,30],[-33,32],[-34,31,33],[-35,34],[35],[-7,36],[-8,36],[-14,37],[-19,37],[-24,38],[-25,38],[-20,39],[-21,39],[-27,40],[-28,40],[-38,41],[-37,41],[-37,-38,42],[-41,43],[-36,43],[-36,-41,44],[-36,-42,45],[-40,46],[-39,46],[-39,-40,47],[-46,48],[-47,49],[-43,-49,50],[-44,-48,50],[-45,50],[-50],[2,3,7,8,15,16,17,18,21,22,24,25,28],[1,4,6,10,11,12,14,19,20,22,23,26,27]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":45,\"b\":41},{\"tag\":\"incompatible\",\"a\":48,\"b\":41},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":39},{\"tag\":\"incompatible\",\"a\":66,\"b\":49},{\"tag\":\"incompatible\",\"a\":66,\"b\":61},{\"tag\":\"incompatible\",\"a\":73,\"b\":62},{\"tag\":\"mate\",\"ridge\":273,\"a\":10,\"owners\":[51,60,61,63]},{\"tag\":\"mate\",\"ridge\":273,\"a\":32,\"owners\":[61,63]},{\"tag\":\"mate\",\"ridge\":273,\"a\":40,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":273,\"a\":46,\"owners\":[51,60,63]},{\"tag\":\"mate\",\"ridge\":273,\"a\":47,\"owners\":[51,61,63]},{\"tag\":\"mate\",\"ridge\":273,\"a\":48,\"owners\":[51,60,61,63]},{\"tag\":\"mate\",\"ridge\":274,\"a\":10,\"owners\":[65,71,73]},{\"tag\":\"mate\",\"ridge\":274,\"a\":32,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":274,\"a\":47,\"owners\":[65,73]},{\"tag\":\"mate\",\"ridge\":274,\"a\":48,\"owners\":[65,71,73]},{\"tag\":\"mate\",\"ridge\":521,\"a\":14,\"owners\":[41,44,62,63]},{\"tag\":\"mate\",\"ridge\":521,\"a\":30,\"owners\":[62,63]},{\"tag\":\"mate\",\"ridge\":521,\"a\":52,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":521,\"a\":54,\"owners\":[41,44,63]},{\"tag\":\"mate\",\"ridge\":521,\"a\":56,\"owners\":[41,44,62,63]},{\"tag\":\"mate\",\"ridge\":521,\"a\":57,\"owners\":[41,62,63]},{\"tag\":\"mate\",\"ridge\":524,\"a\":14,\"owners\":[66,69,74]},{\"tag\":\"mate\",\"ridge\":524,\"a\":52,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":524,\"a\":54,\"owners\":[66,69]},{\"tag\":\"mate\",\"ridge\":524,\"a\":56,\"owners\":[66,69,74]},{\"tag\":\"mate\",\"ridge\":524,\"a\":57,\"owners\":[66,74]},{\"tag\":\"mate\",\"ridge\":538,\"a\":41,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":538,\"a\":66,\"owners\":[41]},{\"tag\":\"mate\",\"ridge\":650,\"a\":44,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":650,\"a\":69,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":284,\"a\":65,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":340,\"a\":71,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":568,\"a\":62,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":568,\"a\":74,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":792,\"a\":63,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[32,45,48,49],\"full_literals\":[-29,4,9,12,13]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[39],\"full_literals\":[-30,5]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-31,false,29],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-32,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-33,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-34,31,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-35,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":41,\"full_literals\":[-7,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":44,\"full_literals\":[-8,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":51,\"full_literals\":[-14,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":60,\"full_literals\":[-19,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-24,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-25,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":61,\"full_literals\":[-20,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":62,\"full_literals\":[-21,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":73,\"full_literals\":[-27,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-28,40]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-37,-38,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-41,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-36,-42,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-40,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-47,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-43,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[14,30,41,44,52,54,56,57,62,63,66,69,74]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[10,32,40,46,47,48,51,60,61,63,65,71,73]}]}"
  "p cnf 50 73\n-9 -7 0\n-12 -7 0\n-21 -20 0\n-24 -5 0\n-24 -13 0\n-24 -20 0\n-27 -21 0\n-1 14 19 20 22 0\n-4 20 22 0\n-6 19 0\n-10 14 19 22 0\n-11 14 20 22 0\n-12 14 19 20 22 0\n-1 23 26 27 0\n-4 27 0\n-11 23 27 0\n-12 23 26 27 0\n-2 7 8 21 22 0\n-3 21 22 0\n-15 8 0\n-16 7 8 22 0\n-17 7 8 21 22 0\n-18 7 21 22 0\n-2 24 25 28 0\n-15 25 0\n-16 24 25 0\n-17 24 25 28 0\n-18 24 28 0\n-7 24 0\n-24 7 0\n-8 25 0\n-25 8 0\n-23 14 0\n-26 19 0\n-21 28 0\n-28 21 0\n-22 0\n-29 4 9 12 13 0\n-30 5 0\n-31 29 0\n-32 30 0\n-33 32 0\n-34 31 33 0\n-35 34 0\n35 0\n-7 36 0\n-8 36 0\n-14 37 0\n-19 37 0\n-24 38 0\n-25 38 0\n-20 39 0\n-21 39 0\n-27 40 0\n-28 40 0\n-38 41 0\n-37 41 0\n-37 -38 42 0\n-41 43 0\n-36 43 0\n-36 -41 44 0\n-36 -42 45 0\n-40 46 0\n-39 46 0\n-39 -40 47 0\n-46 48 0\n-47 49 0\n-43 -49 50 0\n-44 -48 50 0\n-45 50 0\n-50 0\n2 3 7 8 15 16 17 18 21 22 24 25 28 0\n1 4 6 10 11 12 14 19 20 22 23 26 27 0\n"
  "74 34 0 45 44 0\n75 -45 0 71 70 0\n76 2 3 7 8 15 16 17 18 21 24 25 28 0 37 72 0\n77 1 4 6 10 11 12 14 19 20 23 26 27 0 37 73 0\n78 21 43 0 37 60 46 47 21 20 59 56 51 50 19 36 23 18 22 76 0\n79 43 0 37 59 57 48 49 11 33 10 34 78 3 7 9 12 13 8 77 0\n80 -49 0 79 71 68 0\n81 -47 0 80 67 0\n82 -21 0 81 35 53 55 65 0\n83 -3 0 82 37 19 0\n84 -28 0 82 36 0\n85 24 25 0 84 82 83 31 25 29 28 26 24 27 76 0\n86 -24 0 37 74 4 5 6 30 39 9 1 2 41 38 42 40 43 0\n87 25 0 86 85 0\n88 8 0 87 32 0\n89 38 0 87 51 0\n90 36 0 88 47 0\n91 41 0 89 56 0\n92 -42 0 90 75 62 0\n93 44 0 91 90 61 0\n94 -37 0 92 89 58 0\n95 -48 0 93 71 69 0\n96 -14 0 94 48 0\n97 -19 0 94 49 0\n98 -46 0 95 66 0\n99 -23 0 96 33 0\n100 -6 0 97 10 0\n101 -26 0 97 34 0\n102 -10 0 97 96 37 11 0\n103 -40 0 98 63 0\n104 -39 0 98 64 0\n105 -27 0 103 54 0\n106 -20 0 104 52 0\n107 -4 0 105 15 0\n108 -11 0 105 99 16 0\n109 -12 0 105 101 99 17 0\n110 -1 0 105 101 99 14 0\n111 0 110 108 107 100 102 109 96 97 106 99 101 105 77 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record031

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record032
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "c6a3a4ea96558b6a394e1ba1e4783ec66394e695554b5a354d1b61d4743dc4d9354e334ccb3c2e8b92e2b4ac6b86d1b0ee8751cc729c6785d1715e0f43c8f07e92528960d84e0ba91524950d44d0b68350e1344c930ce0b42c4b0ac8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b69a69369b69a693692492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 29), (facetIndex 37), (facetIndex 42), (facetIndex 45), (facetIndex 58), (facetIndex 70)]))
 (.leaf ([(facetIndex 33), (facetIndex 38), (facetIndex 48), (facetIndex 52), (facetIndex 62), (facetIndex 74)])))
 (.branch 3
 (.leaf ([(facetIndex 27), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 54), (facetIndex 66)]))
 (.leaf ([(facetIndex 28), (facetIndex 30), (facetIndex 34), (facetIndex 57), (facetIndex 69)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 35), (facetIndex 60), (facetIndex 72)]))
 (.leaf ([(facetIndex 36)])))
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 46), (facetIndex 47)]))
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 53)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "440180800440180b9ff9d86c124458cc8c34z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record032" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record032" 43

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record032" "{\"ridges\":[[8,521],[8,522],[44,521],[44,522],[45,521],[45,522],[46,521],[47,521],[47,522],[51,273],[59,652],[71,652],[77,792]],\"owners\":[[8,521,[56,59,64,65],[30,41,44,45,46,47]],[44,521,[56,59,65],[8,30,41,45,46,47,64]],[45,521,[56,59,64,65],[8,30,41,44,46,47]],[46,521,[56,64,65],[8,30,41,44,45,47,59]],[47,521,[56,59,64],[8,30,41,44,45,46,65]],[8,522,[68,71,76,77],[30,41,44,45,46,47]],[44,522,[68,71,77],[8,30,41,45,46,47,76]],[45,522,[68,71,76,77],[8,30,41,44,46,47]],[47,522,[68,71,76],[8,30,41,44,45,46,77]],[51,273,[55,63,65],[11,32,40,49,52,53,61]],[59,652,[71],[]],[71,652,[59],[]],[77,792,[65],[]]],\"edges\":[[29,[8,30,41,44,45,46,47,56,59,64,65,68,71,76,77]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record032" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record032\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-6,-2],[-6,-3],[-6,-4],[-6,-5],[-10,-9],[-11,-9],[-13,-9],[-14,-9],[-15,-7],[-15,-8],[-16,-7],[-16,-8],[-17,-8],[-18,-7],[-18,-8],[-20,-7],[-21,-19],[-22,-19],[-23,-22],[-24,-7],[-25,-19],[-26,-7],[-26,-19],[-27,-21],[-27,-25],[-27,-26],[-28,-19],[-28,-27],[-29,-27],[-30,-29],[-31,-19],[-31,-27],[-1,21,23,25,26],[-11,21,23,26],[-12,21,23,25,26],[-13,21,25,26],[-14,21,23,25],[-1,28,30,31,32],[-11,28,30,32],[-12,28,30,31,32],[-14,28,30,31],[-17,20,24,26],[-23,30],[-30,23],[-32,26],[-33,2,7,8,9,19,27],[-34,3,4,5,22,29],[-35,6],[-36,10,11,13,14],[-37,15,16,17,18],[-38,33],[-38,34],[-39,38],[-40,35],[-41,36],[-41,37],[-42,40],[-42,41],[-43,39],[-43,42],[43],[1,4,9,11,12,13,14,21,23,25,26,28,30,31,32]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":36,\"b\":27},{\"tag\":\"incompatible\",\"a\":36,\"b\":28},{\"tag\":\"incompatible\",\"a\":36,\"b\":30},{\"tag\":\"incompatible\",\"a\":36,\"b\":34},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":46,\"b\":41},{\"tag\":\"incompatible\",\"a\":47,\"b\":41},{\"tag\":\"incompatible\",\"a\":49,\"b\":39},{\"tag\":\"incompatible\",\"a\":49,\"b\":40},{\"tag\":\"incompatible\",\"a\":50,\"b\":39},{\"tag\":\"incompatible\",\"a\":50,\"b\":40},{\"tag\":\"incompatible\",\"a\":51,\"b\":40},{\"tag\":\"incompatible\",\"a\":53,\"b\":39},{\"tag\":\"incompatible\",\"a\":53,\"b\":40},{\"tag\":\"incompatible\",\"a\":55,\"b\":39},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":57,\"b\":54},{\"tag\":\"incompatible\",\"a\":59,\"b\":57},{\"tag\":\"incompatible\",\"a\":63,\"b\":39},{\"tag\":\"incompatible\",\"a\":64,\"b\":54},{\"tag\":\"incompatible\",\"a\":65,\"b\":39},{\"tag\":\"incompatible\",\"a\":65,\"b\":54},{\"tag\":\"incompatible\",\"a\":66,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":54},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":69},{\"tag\":\"incompatible\",\"a\":76,\"b\":54},{\"tag\":\"incompatible\",\"a\":76,\"b\":66},{\"tag\":\"mate\",\"ridge\":521,\"a\":8,\"owners\":[56,59,64,65]},{\"tag\":\"mate\",\"ridge\":521,\"a\":44,\"owners\":[56,59,65]},{\"tag\":\"mate\",\"ridge\":521,\"a\":45,\"owners\":[56,59,64,65]},{\"tag\":\"mate\",\"ridge\":521,\"a\":46,\"owners\":[56,64,65]},{\"tag\":\"mate\",\"ridge\":521,\"a\":47,\"owners\":[56,59,64]},{\"tag\":\"mate\",\"ridge\":522,\"a\":8,\"owners\":[68,71,76,77]},{\"tag\":\"mate\",\"ridge\":522,\"a\":44,\"owners\":[68,71,77]},{\"tag\":\"mate\",\"ridge\":522,\"a\":45,\"owners\":[68,71,76,77]},{\"tag\":\"mate\",\"ridge\":522,\"a\":47,\"owners\":[68,71,76]},{\"tag\":\"mate\",\"ridge\":273,\"a\":51,\"owners\":[55,63,65]},{\"tag\":\"mate\",\"ridge\":652,\"a\":59,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":652,\"a\":71,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":792,\"a\":77,\"owners\":[65]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[27,39,40,41,54,66],\"full_literals\":[-33,2,7,8,9,19,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[28,30,34,57,69],\"full_literals\":[-34,3,4,5,22,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[36],\"full_literals\":[-35,6]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[43,44,46,47],\"full_literals\":[-36,10,11,13,14]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[49,50,51,53],\"full_literals\":[-37,15,16,17,18]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-40,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-41,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-42,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-42,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-43,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-43,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[8,30,41,44,45,46,47,56,59,64,65,68,71,76,77]}]}"
  "p cnf 43 62\n-6 -2 0\n-6 -3 0\n-6 -4 0\n-6 -5 0\n-10 -9 0\n-11 -9 0\n-13 -9 0\n-14 -9 0\n-15 -7 0\n-15 -8 0\n-16 -7 0\n-16 -8 0\n-17 -8 0\n-18 -7 0\n-18 -8 0\n-20 -7 0\n-21 -19 0\n-22 -19 0\n-23 -22 0\n-24 -7 0\n-25 -19 0\n-26 -7 0\n-26 -19 0\n-27 -21 0\n-27 -25 0\n-27 -26 0\n-28 -19 0\n-28 -27 0\n-29 -27 0\n-30 -29 0\n-31 -19 0\n-31 -27 0\n-1 21 23 25 26 0\n-11 21 23 26 0\n-12 21 23 25 26 0\n-13 21 25 26 0\n-14 21 23 25 0\n-1 28 30 31 32 0\n-11 28 30 32 0\n-12 28 30 31 32 0\n-14 28 30 31 0\n-17 20 24 26 0\n-23 30 0\n-30 23 0\n-32 26 0\n-33 2 7 8 9 19 27 0\n-34 3 4 5 22 29 0\n-35 6 0\n-36 10 11 13 14 0\n-37 15 16 17 18 0\n-38 33 0\n-38 34 0\n-39 38 0\n-40 35 0\n-41 36 0\n-41 37 0\n-42 40 0\n-42 41 0\n-43 39 0\n-43 42 0\n43 0\n1 4 9 11 12 13 14 21 23 25 26 28 30 31 32 0\n"
  "63 39 0 61 59 0\n64 42 0 61 60 0\n65 38 0 63 53 0\n66 40 0 64 57 0\n67 41 0 64 58 0\n68 33 0 65 51 0\n69 34 0 65 52 0\n70 35 0 66 54 0\n71 36 0 67 55 0\n72 37 0 67 56 0\n73 6 0 70 48 0\n74 -2 0 73 1 0\n75 -3 0 73 2 0\n76 -4 0 73 3 0\n77 -5 0 73 4 0\n78 1 9 11 12 13 14 21 23 25 26 28 30 31 32 0 76 62 0\n79 -7 0 72 9 11 14 16 20 22 50 42 0\n80 -8 0 72 10 12 13 15 50 0\n81 -19 9 26 0 76 75 77 69 45 17 18 21 27 31 47 36 30 43 39 40 41 38 78 0\n82 9 26 0 80 79 74 68 76 75 77 69 45 81 46 24 25 28 29 32 36 47 19 44 34 35 37 33 78 0\n83 -9 0 71 5 6 7 8 49 0\n84 26 0 83 82 0\n85 -19 0 84 23 0\n86 -27 0 84 26 0\n87 0 85 86 68 74 79 83 80 46 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00024.record032
