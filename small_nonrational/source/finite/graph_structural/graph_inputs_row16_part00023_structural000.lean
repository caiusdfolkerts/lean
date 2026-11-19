module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00023Data
public import GraphInputsRow16Part00023Frames
public import GraphInputsRow16Part00023Leaves
public import GraphInputsRow16Part00023Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record034
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034
def vertexColumn : Fields := ⟨10, hexnat% "2b4a723c4eaa6598b6a394e8b92e2785e0fab1ca6998e539a9565a56352d68d9354d8b52d8749d1743da8d634ccb3a2e2b4ad1b26c5b0ee8751cc789d2729c6715e0f43c8f0bd4a258361381e52685894950d60d1341d50d2324c3342c4b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db69a6d24db6d34924934926926d2492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4102fef71fffe000000", hexnat% "1000000000000000000", hexnat% "80000020000000000", hexnat% "200000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11007ef705ffe000000", 2882303761517117440, 1786706395136, hexnat% "80000020000000000", hexnat% "4200000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11003ef00497e000000", hexnat% "4280000000000000000", 576460840350253056, 54563264528384, 72567767433216, 2594073393955340288]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "82faf023232000000", hexnat% "1000040004808000000", 106652627894272, hexnat% "4300000000000000000", 24763170816, 18141941858304]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1804ab637ffe000000", hexnat% "1000040000000000000", 18141941858304, 649644246248194048, hexnat% "4200000000000000000", 2449958197289549824]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100046273efee000000", hexnat% "4380000000000000000", 3026419018312450048, 39687971984637952, 72057594037927936]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4382e2f1013a2000000", 52814675968, 108086391325327360, hexnat% "1000040004000000000", 108851651149824, 687194767360]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100026200490a000000", 108851651149824, hexnat% "4380000000020000000", 18279380811776, 39687971984637952, 3242591731706757120, 97777614848]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c13 c4
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record034

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record035
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035
def vertexColumn : Fields := ⟨10, hexnat% "acb2aa6a3a4eaa6598b6a394e8b92e2785e0fab1ca6998e539a95652d68d5362d4b49d1743dc8ea358e938cd332cf0ba2e4b8ad2b86d1b26c5b0ee8751cc789d2729c6715e0f43c8f0bd4a258361381e524950d44d0768350e2348c930ce0b42c4b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6da69b4936db6d34da492492492492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6000eb5f7ffe000000", hexnat% "4000800000000000000", 1161634034745344, 2377900603251621888, hexnat% "10800000000000000000", 4644337115725824]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20007f7f7b5a000000", hexnat% "4000800000000000000", 19931332608, 141287244169216, 2413929400270585856, hexnat% "10c00000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "102020778ff3a2000000", 52814675968, 2322168557862912, hexnat% "800100200000000000", hexnat% "4000800100000000000", hexnat% "400080000010000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20006fdfeb7a000000", hexnat% "4000800000000000000", 88113938432, 4538783999459328, 2413929400270585856, hexnat% "10c00000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [17169924690542592, hexnat% "4000800000900000000", 844434593808384, 2431943799316938752, hexnat% "10e00000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000816ffe91e000000", 98247376896, 2431943798780067840, hexnat% "10e00000000000000000", 11540474045136896]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14e029c0dafffe000000", 6227633859723264, 2538772348534784, 9007199254740992]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400083feebfee000000", 2431943798780067840, hexnat% "10e00000000000000000", 18966844014592]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000809ffe93e000000", 2431943798780067840, hexnat% "10e00000000000000000", 1125987953672192, 9570158871838720, 4503599627370496]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200040cf2122000000", hexnat% "4000800104808000000", hexnat% "10002010000080000000", hexnat% "800100208004000000", 1125985806188544, 12103433662234624, hexnat% "400080000010000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record035

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record026
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "a713aa9966a5a36538ce4b89e1783ea6539a9565a568d534cd4b61d2745d0f6a358e938cd3362ccb4ad1b26c5b0ee8751cc789d2729c6785c9715d0f0be34528362384e07a3152685896150d48d1341d50d230cd0b22c4b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6926926d34926924d3492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 31), (facetIndex 35), (facetIndex 38), (facetIndex 47), (facetIndex 70)]))
 (.leaf ([(facetIndex 54), (facetIndex 58), (facetIndex 59), (facetIndex 61)])))
 (.branch 3
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 46), (facetIndex 49)]))
 (.leaf ([(facetIndex 28), (facetIndex 37), (facetIndex 40), (facetIndex 44), (facetIndex 57), (facetIndex 69)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 27), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 68)]))
 (.leaf ([(facetIndex 39), (facetIndex 41), (facetIndex 45)])))
 (.branch 7
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 32), (facetIndex 33), (facetIndex 34), (facetIndex 36)]))
 (.leaf ([(facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 56)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1c12400825f07fe100ab4aba1e1b61b38z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 50)]))
 (.leaf ([(facetIndex 55), (facetIndex 60)])))
 (.branch 3
 (.leaf ([(facetIndex 62), (facetIndex 67)]))
 (.leaf ([(facetIndex 63), (facetIndex 71)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 72)]))
 (.leaf ([(facetIndex 73)])))
 (.branch 7
 (.leaf ([(facetIndex 74)]))
 (.leaf ([(facetIndex 75)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "fac6004006810002z29;"⟩
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
def grouped2_0006 : List Nat := [4, 5, 6, 7]
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record026" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record026" 48

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record026" "{\"ridges\":[[10,289],[10,290],[18,644],[34,289],[38,641],[38,644],[43,289],[43,290],[46,289],[46,290],[48,658],[49,290],[50,674],[55,300],[58,644],[59,644],[60,356],[61,644],[62,312],[67,300],[72,356],[74,312],[75,664]],\"owners\":[[10,289,[55,60,62],[34,43,46,49]],[34,289,[62],[10,43,46,49,55,60]],[43,289,[60],[10,34,46,49,55,62]],[46,289,[55,60],[10,34,43,49,62]],[10,290,[67,72,74],[34,43,46,49]],[43,290,[72],[10,34,46,49,67,74]],[46,290,[67,72],[10,34,43,49,74]],[49,290,[67,74],[10,34,43,46,72]],[38,641,[63],[18,48,50,58,59,61]],[18,644,[71,73,75],[38,58,59,61]],[38,644,[75],[18,58,59,61,71,73]],[58,644,[71,73],[18,38,59,61,75]],[59,644,[73],[18,38,58,61,71,75]],[61,644,[71,75],[18,38,58,59,73]],[48,658,[71],[]],[50,674,[73],[]],[55,300,[67],[]],[67,300,[55],[]],[60,356,[72],[]],[72,356,[60],[]],[62,312,[74],[]],[74,312,[62],[]],[75,664,[63],[]]],\"edges\":[[37,[10,34,43,46,49,55,60,62,67,72,74]],[43,[18,38,48,50,58,59,61,63,71,73,75]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record026" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record026\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-24,-3],[-24,-5],[-24,-9],[-24,-21],[-1,13,16,18],[-4,18],[-7,16],[-8,13,16],[-1,20,23,25],[-7,23],[-8,20,23],[-11,20,25],[-6,19],[-2,22,24,26],[-6,26],[-14,22,24],[-15,24],[-17,22,26],[-10,22],[-12,24],[-13,20],[-20,13],[-16,23],[-23,16],[-18,25],[-25,18],[-26,19],[-27,3,5,6,9,21],[-28,27],[-29,28],[-30,29],[30],[-13,31],[-16,31],[-32,18,20],[-18,32],[-20,32],[-19,33],[-22,33],[-34,23],[-23,34],[-35,24],[-24,35],[-25,36],[-26,37],[-31,38],[-33,39],[-40,32],[-32,39],[-32,-33,40],[-39,41],[-40,42],[-38,41],[-38,-39,42],[-38,-40,43],[-44,34,35],[-35,44],[-34,44],[-37,45],[-36,45],[-45,46],[-44,46],[-44,-45,47],[-41,-47,48],[-42,-46,48],[-43,48],[-48],[1,4,7,8,11,13,16,18,20,23,25],[2,6,10,12,14,15,17,19,22,24,26]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":73,\"b\":31},{\"tag\":\"incompatible\",\"a\":73,\"b\":35},{\"tag\":\"incompatible\",\"a\":73,\"b\":47},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"mate\",\"ridge\":289,\"a\":10,\"owners\":[55,60,62]},{\"tag\":\"mate\",\"ridge\":289,\"a\":34,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":289,\"a\":43,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":289,\"a\":46,\"owners\":[55,60]},{\"tag\":\"mate\",\"ridge\":290,\"a\":10,\"owners\":[67,72,74]},{\"tag\":\"mate\",\"ridge\":290,\"a\":43,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":290,\"a\":46,\"owners\":[67,72]},{\"tag\":\"mate\",\"ridge\":290,\"a\":49,\"owners\":[67,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":38,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":644,\"a\":18,\"owners\":[71,73,75]},{\"tag\":\"mate\",\"ridge\":644,\"a\":38,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":644,\"a\":58,\"owners\":[71,73]},{\"tag\":\"mate\",\"ridge\":644,\"a\":59,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":644,\"a\":61,\"owners\":[71,75]},{\"tag\":\"mate\",\"ridge\":658,\"a\":48,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":674,\"a\":50,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":300,\"a\":55,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":300,\"a\":67,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":356,\"a\":60,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":356,\"a\":72,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":312,\"a\":62,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":312,\"a\":74,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":664,\"a\":75,\"owners\":[63]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[31,35,38,47,70],\"full_literals\":[-27,3,5,6,9,21]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-28,27,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-29,28,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-30,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":55,\"full_literals\":[-13,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":60,\"full_literals\":[-16,31]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[62,67],\"full_literals\":[-32,18,20]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":62,\"full_literals\":[-18,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-20,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":63,\"full_literals\":[-19,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-22,33]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[72],\"full_literals\":[-34,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":72,\"full_literals\":[-23,34]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[73],\"full_literals\":[-35,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":73,\"full_literals\":[-24,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":74,\"full_literals\":[-25,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":75,\"full_literals\":[-26,37]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,32,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-33,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-40,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-38,-39,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-38,-40,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-45,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-41,-47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-46,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[10,34,43,46,49,55,60,62,67,72,74]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,38,48,50,58,59,61,63,71,73,75]}]}"
  "p cnf 48 69\n-24 -3 0\n-24 -5 0\n-24 -9 0\n-24 -21 0\n-1 13 16 18 0\n-4 18 0\n-7 16 0\n-8 13 16 0\n-1 20 23 25 0\n-7 23 0\n-8 20 23 0\n-11 20 25 0\n-6 19 0\n-2 22 24 26 0\n-6 26 0\n-14 22 24 0\n-15 24 0\n-17 22 26 0\n-10 22 0\n-12 24 0\n-13 20 0\n-20 13 0\n-16 23 0\n-23 16 0\n-18 25 0\n-25 18 0\n-26 19 0\n-27 3 5 6 9 21 0\n-28 27 0\n-29 28 0\n-30 29 0\n30 0\n-13 31 0\n-16 31 0\n-32 18 20 0\n-18 32 0\n-20 32 0\n-19 33 0\n-22 33 0\n-34 23 0\n-23 34 0\n-35 24 0\n-24 35 0\n-25 36 0\n-26 37 0\n-31 38 0\n-33 39 0\n-40 32 0\n-32 39 0\n-32 -33 40 0\n-39 41 0\n-40 42 0\n-38 41 0\n-38 -39 42 0\n-38 -40 43 0\n-44 34 35 0\n-35 44 0\n-34 44 0\n-37 45 0\n-36 45 0\n-45 46 0\n-44 46 0\n-44 -45 47 0\n-41 -47 48 0\n-42 -46 48 0\n-43 48 0\n-48 0\n1 4 7 8 11 13 16 18 20 23 25 0\n2 6 10 12 14 15 17 19 22 24 26 0\n"
  "70 29 0 32 31 0\n71 28 0 70 30 0\n72 27 0 71 29 0\n73 -43 0 67 66 0\n74 41 0 51 53 49 46 36 37 33 34 6 26 12 5 8 7 24 68 0\n75 -47 0 74 67 64 0\n76 33 24 0 20 17 38 39 13 27 18 19 14 16 69 0\n77 44 40 0 57 58 43 41 10 23 76 50 36 37 6 26 12 21 9 11 68 0\n78 35 42 0 52 77 43 56 76 40 47 24 54 34 46 0\n79 42 0 75 72 52 77 63 59 45 15 78 42 1 2 3 4 28 0\n80 -46 0 79 67 65 0\n81 -45 0 80 61 0\n82 -44 0 80 62 0\n83 -36 0 81 60 0\n84 40 0 82 77 0\n85 -25 0 83 44 0\n86 32 0 84 48 0\n87 -38 0 84 73 55 0\n88 -18 0 85 25 0\n89 20 0 86 88 35 0\n90 -31 0 87 46 0\n91 13 0 89 22 0\n92 0 91 90 33 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record026_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record026

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record027
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "29a4eaa659a968d94e3392e2785e0fa994e6a5596958d54d3352d2745d0f723a8d63a4d33a2d8b32d2b86d1b26c5b0ee8751cc789d2729c6785c9715d0f0be32528362384e07a31524352344d0768350e2348e130cd0b22c4b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db4934936db493492492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 31), (facetIndex 35), (facetIndex 38), (facetIndex 59), (facetIndex 71)]))
 (.leaf ([(facetIndex 28), (facetIndex 54), (facetIndex 55), (facetIndex 57), (facetIndex 58)])))
 (.branch 3
 (.leaf ([(facetIndex 66), (facetIndex 67), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 32), (facetIndex 34), (facetIndex 48), (facetIndex 50), (facetIndex 52)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 43), (facetIndex 47), (facetIndex 49), (facetIndex 51)]))
 (.leaf ([(facetIndex 27), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 44), (facetIndex 45), (facetIndex 46)])))
 (.branch 7
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 53), (facetIndex 65)]))
 (.leaf ([(facetIndex 33), (facetIndex 36), (facetIndex 37)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "904b00000482738e396d96da3f0fb1b1az14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 56), (facetIndex 61)]))
 (.leaf ([(facetIndex 60), (facetIndex 62)])))
 (.branch 3
 (.leaf ([(facetIndex 63), (facetIndex 68)]))
 (.leaf ([(facetIndex 64), (facetIndex 72)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 73)]))
 (.leaf ([(facetIndex 74)])))
 (.branch 7
 (.leaf ([(facetIndex 75)]))
 (.leaf ([(facetIndex 76)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "7d63002003441z2d;"⟩
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
def grouped2_0006 : List Nat := [4, 5, 6, 7]
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record027" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record027" 49

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record027" "{\"ridges\":[[11,290],[14,641],[14,642],[34,289],[38,641],[38,642],[44,290],[47,641],[47,642],[48,290],[49,641],[49,642],[50,290],[51,642],[52,290],[56,300],[60,660],[61,356],[62,676],[64,664],[72,660],[73,356],[74,676],[75,312],[76,664]],\"owners\":[[34,289,[63],[11,44,48,50,52,56,61]],[11,290,[68,73,75],[34,44,48,50,52]],[44,290,[73],[11,34,48,50,52,68,75]],[48,290,[68,73],[11,34,44,50,52,75]],[50,290,[68,75],[11,34,44,48,52,73]],[52,290,[68,73,75],[11,34,44,48,50]],[14,641,[60,62,64],[38,47,49,51]],[38,641,[64],[14,47,49,51,60,62]],[47,641,[60,62],[14,38,49,51,64]],[49,641,[62],[14,38,47,51,60,64]],[14,642,[72,74,76],[38,47,49,51]],[38,642,[76],[14,47,49,51,72,74]],[47,642,[72,74],[14,38,49,51,76]],[49,642,[74],[14,38,47,51,72,76]],[51,642,[72,76],[14,38,47,49,74]],[56,300,[68],[]],[60,660,[72],[]],[72,660,[60],[]],[61,356,[73],[]],[73,356,[61],[]],[62,676,[74],[]],[74,676,[62],[]],[75,312,[63],[]],[64,664,[76],[]],[76,664,[64],[]]],\"edges\":[[37,[11,34,44,48,50,52,56,61,63,68,73,75]],[43,[14,38,47,49,51,60,62,64,72,74,76]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record027" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record027\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-25,-3],[-25,-5],[-25,-15],[-25,-22],[-4,19],[-1,21,24,26],[-7,24],[-9,21,24],[-11,21,26],[-13,21,24,26],[-2,16,18,20],[-6,20],[-8,16,18],[-10,18],[-2,23,25,27],[-6,27],[-8,23,25],[-10,25],[-12,23,27],[-14,21],[-16,23],[-23,16],[-17,24],[-24,17],[-18,25],[-25,18],[-26,19],[-20,27],[-27,20],[-28,3,5,6,15,22],[-29,28],[-30,29],[-31,30],[31],[-17,32],[-16,33],[-18,33],[-19,34],[-21,34],[-35,20,23],[-20,35],[-23,35],[-36,24],[-24,36],[-37,25],[-25,37],[-27,38],[-33,39],[-32,39],[-35,40],[-41,35],[-34,-35,41],[-40,42],[-41,43],[-39,42],[-39,-40,43],[-39,-41,44],[-45,36,37],[-37,45],[-36,45],[-38,46],[-46,47],[-45,47],[-45,-46,48],[-42,-48,49],[-43,-47,49],[-44,49],[-49],[1,4,7,9,11,13,14,17,19,21,24,26],[2,6,8,10,12,16,18,20,23,25,27]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":74,\"b\":31},{\"tag\":\"incompatible\",\"a\":74,\"b\":35},{\"tag\":\"incompatible\",\"a\":74,\"b\":59},{\"tag\":\"incompatible\",\"a\":74,\"b\":71},{\"tag\":\"mate\",\"ridge\":289,\"a\":34,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":290,\"a\":11,\"owners\":[68,73,75]},{\"tag\":\"mate\",\"ridge\":290,\"a\":44,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":290,\"a\":48,\"owners\":[68,73]},{\"tag\":\"mate\",\"ridge\":290,\"a\":50,\"owners\":[68,75]},{\"tag\":\"mate\",\"ridge\":290,\"a\":52,\"owners\":[68,73,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":14,\"owners\":[60,62,64]},{\"tag\":\"mate\",\"ridge\":641,\"a\":38,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":641,\"a\":47,\"owners\":[60,62]},{\"tag\":\"mate\",\"ridge\":641,\"a\":49,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":642,\"a\":14,\"owners\":[72,74,76]},{\"tag\":\"mate\",\"ridge\":642,\"a\":38,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":642,\"a\":47,\"owners\":[72,74]},{\"tag\":\"mate\",\"ridge\":642,\"a\":49,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":642,\"a\":51,\"owners\":[72,76]},{\"tag\":\"mate\",\"ridge\":300,\"a\":56,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":660,\"a\":60,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":660,\"a\":72,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":356,\"a\":61,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":356,\"a\":73,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":676,\"a\":62,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":676,\"a\":74,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":312,\"a\":75,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":664,\"a\":64,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":664,\"a\":76,\"owners\":[64]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[31,35,38,59,71],\"full_literals\":[-28,3,5,6,15,22]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-29,28,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-30,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-31,30,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":61,\"full_literals\":[-17,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":60,\"full_literals\":[-16,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":62,\"full_literals\":[-18,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":63,\"full_literals\":[-19,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":68,\"full_literals\":[-21,34]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[64,72],\"full_literals\":[-35,20,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":64,\"full_literals\":[-20,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-23,35]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[73],\"full_literals\":[-36,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":73,\"full_literals\":[-24,36]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[74],\"full_literals\":[-37,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-25,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":76,\"full_literals\":[-27,38]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-41,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-34,-35,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-40,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-39,-41,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-46,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-42,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-47,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[11,34,44,48,50,52,56,61,63,68,73,75]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[14,38,47,49,51,60,62,64,72,74,76]}]}"
  "p cnf 49 70\n-25 -3 0\n-25 -5 0\n-25 -15 0\n-25 -22 0\n-4 19 0\n-1 21 24 26 0\n-7 24 0\n-9 21 24 0\n-11 21 26 0\n-13 21 24 26 0\n-2 16 18 20 0\n-6 20 0\n-8 16 18 0\n-10 18 0\n-2 23 25 27 0\n-6 27 0\n-8 23 25 0\n-10 25 0\n-12 23 27 0\n-14 21 0\n-16 23 0\n-23 16 0\n-17 24 0\n-24 17 0\n-18 25 0\n-25 18 0\n-26 19 0\n-20 27 0\n-27 20 0\n-28 3 5 6 15 22 0\n-29 28 0\n-30 29 0\n-31 30 0\n31 0\n-17 32 0\n-16 33 0\n-18 33 0\n-19 34 0\n-21 34 0\n-35 20 23 0\n-20 35 0\n-23 35 0\n-36 24 0\n-24 36 0\n-37 25 0\n-25 37 0\n-27 38 0\n-33 39 0\n-32 39 0\n-35 40 0\n-41 35 0\n-34 -35 41 0\n-40 42 0\n-41 43 0\n-39 42 0\n-39 -40 43 0\n-39 -41 44 0\n-45 36 37 0\n-37 45 0\n-36 45 0\n-38 46 0\n-46 47 0\n-45 47 0\n-45 -46 48 0\n-42 -48 49 0\n-43 -47 49 0\n-44 49 0\n-49 0\n1 4 7 9 11 13 14 17 19 21 24 26 0\n2 6 8 10 12 16 18 20 23 25 27 0\n"
  "71 30 0 34 33 0\n72 29 0 71 32 0\n73 28 0 72 31 0\n74 -44 0 68 67 0\n75 42 0 53 55 50 48 41 42 36 37 12 29 19 11 13 14 26 70 0\n76 -48 0 75 68 65 0\n77 35 25 0 25 18 41 42 12 29 19 21 15 17 70 0\n78 45 41 0 59 60 46 44 7 23 77 52 38 39 5 27 20 8 9 10 6 69 0\n79 37 43 0 54 78 46 58 77 43 50 24 56 35 49 0\n80 43 0 76 73 54 78 64 61 47 16 79 45 1 2 3 4 30 0\n81 -47 0 80 68 66 0\n82 -46 0 81 62 0\n83 -45 0 81 63 0\n84 -38 0 82 61 0\n85 41 0 83 78 0\n86 -27 0 84 47 0\n87 35 0 85 51 0\n88 -39 0 85 74 57 0\n89 -20 0 86 28 0\n90 23 0 87 89 40 0\n91 -33 0 88 48 0\n92 16 0 90 22 0\n93 0 92 91 36 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record027_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record027

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record029
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "29caa93a599564da8e8b89e1783eaa6994e565a55554d68d8749d1743da8d6364cd34ce8b8ad2b2ad1b16c3ba1d4789d2719d1725c3783c8f13e2c5489a1582e07951a2629266251560d0b41d50d2344c9314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36da6d24926da69249a49249249a492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 49)]))
 (.leaf ([(facetIndex 57), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 55), (facetIndex 58)]))
 (.leaf ([(facetIndex 59), (facetIndex 67)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 69)]))
 (.leaf ([(facetIndex 70)])))
 (.branch 7
 (.leaf ([(facetIndex 71)]))
 (.leaf ([(facetIndex 72)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "7d606400006884z29;"⟩
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
def grouped3_0012 : List Nat := [6, 7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record029" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record029" 36

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record029" "{\"ridges\":[[10,289],[19,641],[34,289],[42,289],[44,641],[45,289],[48,290],[54,641],[55,308],[58,356],[59,312],[60,641],[61,648],[67,308],[69,356],[70,312],[71,674],[72,660]],\"owners\":[[10,289,[55,58,59],[34,42,45,48]],[34,289,[59],[10,42,45,48,55,58]],[42,289,[55,58],[10,34,45,48,59]],[45,289,[58],[10,34,42,48,55,59]],[48,290,[67,70],[10,34,42,45,69]],[19,641,[37,49,57],[44,54,60,61]],[44,641,[57],[19,37,49,54,60,61]],[54,641,[49],[19,37,44,57,60,61]],[60,641,[37,49],[19,44,54,57,61]],[61,648,[66,72],[19,44,54,60,71]],[71,674,[49],[]],[55,308,[67],[]],[67,308,[55],[]],[72,660,[57],[]],[58,356,[69],[]],[69,356,[58],[]],[59,312,[70],[]],[70,312,[59],[]]],\"edges\":[[37,[10,34,42,45,48,55,58,59,67,69,70]],[43,[19,37,44,49,54,57,60,61,66,71,72]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record029" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record029\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,11,13,14],[-3,14],[-5,11,13],[-7,13],[-8,18,20],[-2,4,9,12],[-6,12],[-10,9],[-15,4,9],[-16,17,22],[-21,9],[-11,18],[-18,11],[-22,12],[-13,19],[-19,13],[-14,20],[-20,14],[-4,23],[-9,23],[-12,24],[-17,24],[-25,11,13],[-11,25],[-13,25],[-26,14,18],[-14,26],[-18,26],[-19,27],[-20,28],[-24,29],[-23,29],[-30,25,26],[-26,30],[-25,30],[-25,-26,31],[-29,-30,32],[-29,-31,33],[-28,34],[-27,34],[-34,35],[-32,-35,36],[-33,36],[-36],[1,3,5,7,8,11,13,14,18,19,20],[2,4,6,9,10,12,15,16,17,21,22]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":289,\"a\":10,\"owners\":[55,58,59]},{\"tag\":\"mate\",\"ridge\":289,\"a\":34,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":289,\"a\":42,\"owners\":[55,58]},{\"tag\":\"mate\",\"ridge\":289,\"a\":45,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":290,\"a\":48,\"owners\":[67,70]},{\"tag\":\"mate\",\"ridge\":641,\"a\":19,\"owners\":[37,49,57]},{\"tag\":\"mate\",\"ridge\":641,\"a\":44,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":641,\"a\":54,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":641,\"a\":60,\"owners\":[37,49]},{\"tag\":\"mate\",\"ridge\":648,\"a\":61,\"owners\":[66,72]},{\"tag\":\"mate\",\"ridge\":674,\"a\":71,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":308,\"a\":55,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":308,\"a\":67,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":660,\"a\":72,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":356,\"a\":58,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":356,\"a\":69,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":312,\"a\":59,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":312,\"a\":70,\"owners\":[59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":37,\"full_literals\":[-4,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-9,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":57,\"full_literals\":[-12,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-17,24]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[55,58],\"full_literals\":[-25,11,13]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":55,\"full_literals\":[-11,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":58,\"full_literals\":[-13,25]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[59,67],\"full_literals\":[-26,14,18]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":59,\"full_literals\":[-14,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-18,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":69,\"full_literals\":[-19,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":70,\"full_literals\":[-20,28]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-23,false,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-30,25,26],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-26,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-29,-30,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-29,-31,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[10,34,42,45,48,55,58,59,67,69,70]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[19,37,44,49,54,57,60,61,66,71,72]}]}"
  "p cnf 36 46\n-1 11 13 14 0\n-3 14 0\n-5 11 13 0\n-7 13 0\n-8 18 20 0\n-2 4 9 12 0\n-6 12 0\n-10 9 0\n-15 4 9 0\n-16 17 22 0\n-21 9 0\n-11 18 0\n-18 11 0\n-22 12 0\n-13 19 0\n-19 13 0\n-14 20 0\n-20 14 0\n-4 23 0\n-9 23 0\n-12 24 0\n-17 24 0\n-25 11 13 0\n-11 25 0\n-13 25 0\n-26 14 18 0\n-14 26 0\n-18 26 0\n-19 27 0\n-20 28 0\n-24 29 0\n-23 29 0\n-30 25 26 0\n-26 30 0\n-25 30 0\n-25 -26 31 0\n-29 -30 32 0\n-29 -31 33 0\n-28 34 0\n-27 34 0\n-34 35 0\n-32 -35 36 0\n-33 36 0\n-36 0\n1 3 5 7 8 11 13 14 18 19 20 0\n2 4 6 9 10 12 15 16 17 21 22 0\n"
  "47 -33 0 44 43 0\n48 30 0 34 35 27 28 24 25 2 18 5 1 3 4 16 45 0\n49 29 0 31 32 21 22 19 20 7 14 10 6 9 8 11 46 0\n50 32 0 49 48 37 0\n51 -31 0 49 47 38 0\n52 -35 0 50 44 42 0\n53 -34 0 52 41 0\n54 -28 0 53 39 0\n55 -27 0 53 40 0\n56 -20 0 54 30 0\n57 -19 0 55 29 0\n58 -14 0 56 17 0\n59 -13 0 57 15 0\n60 26 0 48 59 28 33 12 23 0\n61 18 0 60 58 26 0\n62 -25 0 60 51 36 0\n63 11 0 61 13 0\n64 0 63 62 24 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record029_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record029

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record030
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "32ca715caaa9a59a96a394e4ba1e2785e0faa9565655568d5362d4749d1743da8d6334e8b52e2b4acab16c3ba1d4789d2719c970de0f43c8f13e2c4b28a8a89a898568382e0792926545494554342d0749314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "26d26d34924da4d24926d269249a492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 46)]))
 (.leaf ([(facetIndex 37), (facetIndex 47)])))
 (.branch 3
 (.leaf ([(facetIndex 57), (facetIndex 64)]))
 (.leaf ([(facetIndex 54), (facetIndex 58)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 66)]))
 (.leaf ([(facetIndex 67)])))
 (.branch 7
 (.leaf ([(facetIndex 70)]))
 (.leaf ([(facetIndex 71)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "f80b020000d00c0000200000008z1b;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record030" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record030" 42

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record030" "{\"ridges\":[[14,321],[14,324],[24,642],[24,648],[36,321],[36,324],[37,645],[43,330],[44,642],[44,648],[46,354],[47,673],[53,321],[53,324],[54,645],[55,321],[55,324],[56,321],[56,324],[57,344],[58,673],[64,330],[65,642],[65,648],[66,660],[67,354],[68,642],[68,648],[69,642],[69,648],[70,344],[71,660]],\"owners\":[[14,321,[43,46,57],[36,53,55,56]],[36,321,[57],[14,43,46,53,55,56]],[53,321,[46],[14,36,43,55,56,57]],[55,321,[43,46],[14,36,53,56,57]],[56,321,[43,57],[14,36,46,53,55]],[14,324,[64,67,70],[36,53,55,56]],[36,324,[70],[14,53,55,56,64,67]],[53,324,[67],[14,36,55,56,64,70]],[55,324,[64,67],[14,36,53,56,70]],[56,324,[64,70],[14,36,53,55,67]],[24,642,[37,47,66],[44,65,68,69]],[44,642,[66],[24,37,47,65,68,69]],[65,642,[47],[24,37,44,66,68,69]],[68,642,[37,47],[24,44,65,66,69]],[69,642,[37,66],[24,44,47,65,68]],[24,648,[54,58,71],[44,65,68,69]],[44,648,[71],[24,54,58,65,68,69]],[65,648,[58],[24,44,54,68,69,71]],[68,648,[54,58],[24,44,65,69,71]],[69,648,[54,71],[24,44,58,65,68]],[37,645,[54],[]],[54,645,[37],[]],[43,330,[64],[]],[64,330,[43],[]],[46,354,[67],[]],[67,354,[46],[]],[47,673,[58],[]],[58,673,[47],[]],[57,344,[70],[]],[70,344,[57],[]],[66,660,[71],[]],[71,660,[66],[]]],\"edges\":[[40,[14,36,43,46,53,55,56,57,64,67,70]],[43,[24,37,44,47,54,58,65,66,68,69,71]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record030" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record030\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,5,7,13],[-3,13],[-9,7],[-11,5,7],[-12,5,13],[-1,15,18,21],[-3,21],[-9,18],[-11,15,18],[-12,15,21],[-2,4,8,17],[-6,17],[-16,8],[-19,4,8],[-20,4,17],[-2,10,14,22],[-6,22],[-16,14],[-19,10,14],[-20,10,22],[-4,10],[-10,4],[-5,15],[-15,5],[-7,18],[-18,7],[-8,14],[-14,8],[-13,21],[-21,13],[-17,22],[-22,17],[-5,23],[-7,23],[-4,24],[-8,24],[-13,25],[-15,25],[-10,26],[-14,26],[-27,17],[-17,27],[-28,18],[-18,28],[-29,21],[-21,29],[-30,22],[-22,30],[-23,31],[-23,-24,32],[-25,33],[-25,-26,34],[-33,35],[-34,36],[-31,35],[-31,-34,37],[-32,36],[-38,27,28],[-28,38],[-27,38],[-39,29,30],[-30,39],[-29,39],[-40,38,39],[-39,40],[-38,40],[-38,-39,41],[-35,-41,42],[-36,-40,42],[-37,42],[-42],[1,3,5,7,9,11,12,13,15,18,21],[2,4,6,8,10,14,16,17,19,20,22]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":321,\"a\":14,\"owners\":[43,46,57]},{\"tag\":\"mate\",\"ridge\":321,\"a\":36,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":321,\"a\":53,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":321,\"a\":55,\"owners\":[43,46]},{\"tag\":\"mate\",\"ridge\":321,\"a\":56,\"owners\":[43,57]},{\"tag\":\"mate\",\"ridge\":324,\"a\":14,\"owners\":[64,67,70]},{\"tag\":\"mate\",\"ridge\":324,\"a\":36,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":324,\"a\":53,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":324,\"a\":55,\"owners\":[64,67]},{\"tag\":\"mate\",\"ridge\":324,\"a\":56,\"owners\":[64,70]},{\"tag\":\"mate\",\"ridge\":642,\"a\":24,\"owners\":[37,47,66]},{\"tag\":\"mate\",\"ridge\":642,\"a\":44,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":642,\"a\":65,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":642,\"a\":68,\"owners\":[37,47]},{\"tag\":\"mate\",\"ridge\":642,\"a\":69,\"owners\":[37,66]},{\"tag\":\"mate\",\"ridge\":648,\"a\":24,\"owners\":[54,58,71]},{\"tag\":\"mate\",\"ridge\":648,\"a\":44,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":648,\"a\":65,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":648,\"a\":68,\"owners\":[54,58]},{\"tag\":\"mate\",\"ridge\":648,\"a\":69,\"owners\":[54,71]},{\"tag\":\"mate\",\"ridge\":645,\"a\":37,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":645,\"a\":54,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":330,\"a\":43,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":330,\"a\":64,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":354,\"a\":46,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":354,\"a\":67,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":673,\"a\":47,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":673,\"a\":58,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":344,\"a\":57,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":344,\"a\":70,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":660,\"a\":66,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":660,\"a\":71,\"owners\":[66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":43,\"full_literals\":[-5,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":46,\"full_literals\":[-7,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":37,\"full_literals\":[-4,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":47,\"full_literals\":[-8,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":57,\"full_literals\":[-13,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":64,\"full_literals\":[-15,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":54,\"full_literals\":[-10,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":58,\"full_literals\":[-14,26]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[66],\"full_literals\":[-27,17]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":66,\"full_literals\":[-17,27]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[67],\"full_literals\":[-28,18]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":67,\"full_literals\":[-18,28]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[70],\"full_literals\":[-29,21]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":70,\"full_literals\":[-21,29]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[71],\"full_literals\":[-30,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":71,\"full_literals\":[-22,30]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-23,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-23,-24,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-26,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-34,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-31,-34,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,27,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-39,29,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-40,38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-38,-39,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-35,-41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-40,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[14,36,43,46,53,55,56,57,64,67,70]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[24,37,44,47,54,58,65,66,68,69,71]}]}"
  "p cnf 42 73\n-1 5 7 13 0\n-3 13 0\n-9 7 0\n-11 5 7 0\n-12 5 13 0\n-1 15 18 21 0\n-3 21 0\n-9 18 0\n-11 15 18 0\n-12 15 21 0\n-2 4 8 17 0\n-6 17 0\n-16 8 0\n-19 4 8 0\n-20 4 17 0\n-2 10 14 22 0\n-6 22 0\n-16 14 0\n-19 10 14 0\n-20 10 22 0\n-4 10 0\n-10 4 0\n-5 15 0\n-15 5 0\n-7 18 0\n-18 7 0\n-8 14 0\n-14 8 0\n-13 21 0\n-21 13 0\n-17 22 0\n-22 17 0\n-5 23 0\n-7 23 0\n-4 24 0\n-8 24 0\n-13 25 0\n-15 25 0\n-10 26 0\n-14 26 0\n-27 17 0\n-17 27 0\n-28 18 0\n-18 28 0\n-29 21 0\n-21 29 0\n-30 22 0\n-22 30 0\n-23 31 0\n-23 -24 32 0\n-25 33 0\n-25 -26 34 0\n-33 35 0\n-34 36 0\n-31 35 0\n-31 -34 37 0\n-32 36 0\n-38 27 28 0\n-28 38 0\n-27 38 0\n-39 29 30 0\n-30 39 0\n-29 39 0\n-40 38 39 0\n-39 40 0\n-38 40 0\n-38 -39 41 0\n-35 -41 42 0\n-36 -40 42 0\n-37 42 0\n-42 0\n1 3 5 7 9 11 12 13 15 18 21 0\n2 4 6 8 10 14 16 17 19 20 22 0\n"
  "74 -37 0 71 70 0\n75 35 0 53 55 51 49 37 38 33 34 2 30 5 1 4 3 26 72 0\n76 -41 0 75 71 68 0\n77 -39 34 0 76 67 60 42 12 32 47 61 45 30 37 52 39 40 21 20 18 27 19 16 73 0\n78 -40 0 71 69 54 57 77 62 64 48 17 31 41 58 43 26 34 50 35 36 22 15 13 28 14 11 73 0\n79 -39 0 78 65 0\n80 -38 0 78 66 0\n81 -30 0 79 62 0\n82 -29 0 79 63 0\n83 -28 0 80 59 0\n84 -27 0 80 60 0\n85 -22 0 81 48 0\n86 -21 0 82 46 0\n87 -18 0 83 44 0\n88 -17 0 84 42 0\n89 -6 0 85 17 0\n90 -3 0 86 7 0\n91 -13 0 86 29 0\n92 -9 0 87 8 0\n93 -7 0 87 25 0\n94 26 0 85 88 89 39 40 21 20 18 27 19 16 73 0\n95 15 0 86 87 92 91 93 90 23 6 9 10 72 0\n96 5 0 95 24 0\n97 25 0 95 38 0\n98 23 0 96 33 0\n99 34 0 97 94 52 0\n100 31 0 98 49 0\n101 0 100 99 74 56 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record030_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record030

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record031
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "a715aa996635a8e53a2e4b89e1783eca699566a5596953568d5352d8749d1743da8d6354cd3a2d4b8ad1b26c5b0ee8751cc789d2729c670de0f43c8f13e2c4a8961582e07a294a685894951560d0b41d50d2324c5342c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db4da4924da69269249a49a492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 49)]))
 (.leaf ([(facetIndex 55), (facetIndex 59)])))
 (.branch 3
 (.leaf ([(facetIndex 61), (facetIndex 69)]))
 (.leaf ([(facetIndex 62), (facetIndex 70)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 72)]))
 (.leaf ([(facetIndex 73)])))
 (.branch 7
 (.leaf ([(facetIndex 74)]))
 (.leaf ([(facetIndex 75)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "fac0d00000d02002z29;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record031" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record031" 42

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record031" "{\"ridges\":[[11,321],[11,322],[18,644],[37,321],[37,322],[38,641],[44,321],[44,322],[45,650],[47,321],[47,322],[48,321],[48,322],[49,674],[55,332],[56,644],[58,644],[59,356],[60,644],[61,344],[69,332],[72,356],[73,674],[74,344],[75,664]],\"owners\":[[11,321,[55,59,61],[37,44,47,48]],[37,321,[61],[11,44,47,48,55,59]],[44,321,[59],[11,37,47,48,55,61]],[47,321,[55,59],[11,37,44,48,61]],[48,321,[55,61],[11,37,44,47,59]],[11,322,[69,72,74],[37,44,47,48]],[37,322,[74],[11,44,47,48,69,72]],[44,322,[72],[11,37,47,48,69,74]],[47,322,[69,72],[11,37,44,48,74]],[48,322,[69,74],[11,37,44,47,72]],[38,641,[62],[18,45,49,56,58,60]],[18,644,[70,73,75],[38,56,58,60]],[56,644,[73],[18,38,58,60,70,75]],[58,644,[70,73],[18,38,56,60,75]],[60,644,[70,75],[18,38,56,58,73]],[45,650,[70],[]],[49,674,[73],[]],[73,674,[49],[]],[55,332,[69],[]],[69,332,[55],[]],[59,356,[72],[]],[72,356,[59],[]],[61,344,[74],[]],[74,344,[61],[]],[75,664,[62],[]]],\"edges\":[[40,[11,37,44,47,48,55,59,61,69,72,74]],[43,[18,38,45,49,56,58,60,62,70,73,75]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record031" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record031\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,10,13,15],[-3,15],[-5,13],[-7,10,13],[-8,10,15],[-1,17,19,21],[-3,21],[-5,19],[-7,17,19],[-8,17,21],[-4,16],[-2,18,20,22],[-11,20],[-12,18,20],[-14,18,22],[-6,18],[-9,20],[-20,9],[-10,17],[-17,10],[-13,19],[-19,13],[-15,21],[-21,15],[-22,16],[-9,23],[-10,24],[-13,24],[-25,15,17],[-15,25],[-17,25],[-16,26],[-18,26],[-27,19],[-19,27],[-28,20],[-20,28],[-21,29],[-24,30],[-23,-24,31],[-26,32],[-33,25],[-25,32],[-25,-26,33],[-32,34],[-33,35],[-30,34],[-30,-32,35],[-30,-33,36],[-31,35],[-37,27,28],[-28,37],[-27,37],[-27,-28,38],[-29,39],[-39,40],[-37,40],[-37,-39,41],[-38,41],[-34,-41,42],[-35,-40,42],[-36,42],[-42],[1,3,5,7,8,10,13,15,17,19,21],[2,4,6,9,11,12,14,16,18,20,22]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":321,\"a\":11,\"owners\":[55,59,61]},{\"tag\":\"mate\",\"ridge\":321,\"a\":37,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":321,\"a\":44,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":321,\"a\":47,\"owners\":[55,59]},{\"tag\":\"mate\",\"ridge\":321,\"a\":48,\"owners\":[55,61]},{\"tag\":\"mate\",\"ridge\":322,\"a\":11,\"owners\":[69,72,74]},{\"tag\":\"mate\",\"ridge\":322,\"a\":37,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":322,\"a\":44,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":322,\"a\":47,\"owners\":[69,72]},{\"tag\":\"mate\",\"ridge\":322,\"a\":48,\"owners\":[69,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":38,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":644,\"a\":18,\"owners\":[70,73,75]},{\"tag\":\"mate\",\"ridge\":644,\"a\":56,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":644,\"a\":58,\"owners\":[70,73]},{\"tag\":\"mate\",\"ridge\":644,\"a\":60,\"owners\":[70,75]},{\"tag\":\"mate\",\"ridge\":650,\"a\":45,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":674,\"a\":49,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":674,\"a\":73,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":332,\"a\":55,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":332,\"a\":69,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":356,\"a\":59,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":356,\"a\":72,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":344,\"a\":61,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":344,\"a\":74,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":664,\"a\":75,\"owners\":[62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-9,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":55,\"full_literals\":[-10,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":59,\"full_literals\":[-13,24]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[61,69],\"full_literals\":[-25,15,17]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":61,\"full_literals\":[-15,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-17,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":62,\"full_literals\":[-16,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":70,\"full_literals\":[-18,26]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[72],\"full_literals\":[-27,19]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":72,\"full_literals\":[-19,27]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[73],\"full_literals\":[-28,20]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":73,\"full_literals\":[-20,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":74,\"full_literals\":[-21,29]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-23,-24,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-33,25,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-26,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-33,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-30,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-30,-32,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-30,-33,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-37,27,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-28,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-37,-39,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-34,-41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-35,-40,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[11,37,44,47,48,55,59,61,69,72,74]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,38,45,49,56,58,60,62,70,73,75]}]}"
  "p cnf 42 65\n-1 10 13 15 0\n-3 15 0\n-5 13 0\n-7 10 13 0\n-8 10 15 0\n-1 17 19 21 0\n-3 21 0\n-5 19 0\n-7 17 19 0\n-8 17 21 0\n-4 16 0\n-2 18 20 22 0\n-11 20 0\n-12 18 20 0\n-14 18 22 0\n-6 18 0\n-9 20 0\n-20 9 0\n-10 17 0\n-17 10 0\n-13 19 0\n-19 13 0\n-15 21 0\n-21 15 0\n-22 16 0\n-9 23 0\n-10 24 0\n-13 24 0\n-25 15 17 0\n-15 25 0\n-17 25 0\n-16 26 0\n-18 26 0\n-27 19 0\n-19 27 0\n-28 20 0\n-20 28 0\n-21 29 0\n-24 30 0\n-23 -24 31 0\n-26 32 0\n-33 25 0\n-25 32 0\n-25 -26 33 0\n-32 34 0\n-33 35 0\n-30 34 0\n-30 -32 35 0\n-30 -33 36 0\n-31 35 0\n-37 27 28 0\n-28 37 0\n-27 37 0\n-27 -28 38 0\n-29 39 0\n-39 40 0\n-37 40 0\n-37 -39 41 0\n-38 41 0\n-34 -41 42 0\n-35 -40 42 0\n-36 42 0\n-42 0\n1 3 5 7 8 10 13 15 17 19 21 0\n2 4 6 9 11 12 14 16 18 20 22 0\n"
  "66 -36 0 63 62 0\n67 34 0 45 47 43 39 30 31 27 28 2 24 1 4 5 3 22 64 0\n68 -41 0 67 63 60 0\n69 -38 0 68 59 0\n70 26 20 0 17 13 32 33 11 25 15 16 12 14 65 0\n71 3 21 1 7 5 10 13 15 17 19 0 64 10 0\n72 37 33 0 52 53 37 35 8 21 70 44 30 31 2 24 19 6 9 71 0\n73 19 35 0 68 46 72 58 55 38 23 7 50 8 21 34 51 36 18 26 40 27 1 4 20 71 0\n74 35 0 69 73 22 35 28 54 39 37 48 70 41 0\n75 -40 0 74 63 61 0\n76 -39 0 75 56 0\n77 -37 0 75 57 0\n78 -29 0 76 55 0\n79 33 0 77 72 0\n80 -21 0 78 38 0\n81 25 0 79 42 0\n82 -30 0 79 66 49 0\n83 -15 0 80 23 0\n84 17 0 81 83 29 0\n85 -24 0 82 39 0\n86 10 0 84 20 0\n87 0 86 85 27 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record031_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record031
